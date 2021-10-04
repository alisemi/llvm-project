/*
 * OldButUsefulCodes.cpp
 *
 * These are the pieces of codes that were worked on but are not being used for the current compiler pass.
 * Most of them are related to loop processing, and some is from the remainder of old spmreg logic
 * (spmreg instruction was returning a special value previously in case the data is not found in spm
 *  so software should have been handle this)
 *
 *  Created on: Oct 4, 2021
 *      Author: ali
 */

#include "GraphSPMInstInternal.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/Intrinsics.h"
#include <llvm/Analysis/LoopInfo.h>
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Support/Debug.h"
#include <vector>
#include <algorithm>
#include <string>
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Transforms/Utils/FunctionComparator.h"
#include "llvm/IR/DataLayout.h"

using namespace llvm;

static bool insertSPMDEL(SPMDELInfo &spmdelInfo, LLVMContext &llvmContext,
		Instruction *edgeArray, Function *spmdel_intrinsic);

static bool createLoopFromLoopBounds(Optional<Loop::LoopBounds> &loopBounds,
		Loop *outerMostLoop, BasicBlock *insertionPoint, LoopInfo &LI,
		DominatorTree &DT, Instruction *edgeArray, Function *spmdel_intrinsic,
		LLVMContext &llvmContext);

static void countBlocksInLoop(Loop *L, unsigned nesAng);

//Returns itself it is already a top-level loop
static Loop* outermostParentLoop(Loop *L);

static void findValues(const SCEV *Expr, ScalarEvolution &SE,
		SetVector<Value*> &Values);

static void SCEVDebug(const SCEV &scev);

static void processSCEV(LoadInst *loadInst, ScalarEvolution *SE, Loop *L);

static void dumpLoopBounds(Loop *L, ScalarEvolution &SE);

static bool createLoopFromLoopBounds(Optional<Loop::LoopBounds> &loopBounds,
		Loop *outerMostLoop, BasicBlock *insertionPoint, LoopInfo &LI,
		DominatorTree &DT, Instruction *edgeArray, Function *spmdel_intrinsic,
		LLVMContext &llvmContext) {
	Loop &New = *(LI.AllocateLoop());
	Instruction *insertionPointInst;
	Value &IVInitialVal = loopBounds->getInitialIVValue();
	Value &IVFinalVal = loopBounds->getFinalIVValue();
	Value *stepValue = loopBounds->getStepValue();
	BasicBlock *spmdelPreheader, *spmdelExiting, *spmdelBody, *spmdelInc,
			*spmdelExit;

	llvm::Type *i32_type = llvm::IntegerType::getInt32Ty(llvmContext);
	insertionPointInst = insertionPoint->getFirstNonPHI();

	//Loop Insertion
	IRBuilder<> Builder(insertionPointInst);
	Value *Compare = Builder.CreateICmpSLT(&IVInitialVal, &IVFinalVal,
			"spmdel.guard_cmp");
	ConstantInt *CompareConstantInt = dyn_cast<ConstantInt>(Compare);
	bool noNeedGuard = false;
	if (CompareConstantInt) {
		noNeedGuard = CompareConstantInt->getZExtValue();
	}
	Instruction *compareInst = dyn_cast<Instruction>(Compare);
	if (compareInst) { //It means that we did not compare constants so need for loop guard
		Instruction *ThenBranchInst = SplitBlockAndInsertIfThen(Compare,
				compareInst->getNextNode(), false, nullptr, &DT, &LI, nullptr);
		spmdelPreheader = ThenBranchInst->getParent();
		spmdelPreheader->setName("spmdel.ph");
		spmdelExit = ThenBranchInst->getParent()->getNextNode();
		spmdelExit->setName("spmdel.end");
		spmdelBody = SplitBlock(spmdelPreheader,
				spmdelPreheader->getTerminator(), &DT, &LI, nullptr,
				"spmdel.body");
		spmdelExiting = SplitBlock(spmdelBody, spmdelBody->getTerminator(), &DT,
				&LI, nullptr, "spmdel.exiting");

	} else if (noNeedGuard) { //We compared constants and infer that we don't need loop guard as İnitialValue is already less than FinalValue
		spmdelPreheader = SplitBlock(insertionPoint,
				insertionPoint->getFirstNonPHI(), &DT, &LI, nullptr,
				"spmdel.ph");
		spmdelBody = SplitBlock(spmdelPreheader,
				spmdelPreheader->getFirstNonPHI(), &DT, &LI, nullptr,
				"spmdel.body");
		spmdelExiting = SplitBlock(spmdelBody, spmdelBody->getFirstNonPHI(),
				&DT, &LI, nullptr, "spmdel.exiting");
		spmdelExit = SplitBlock(spmdelExiting, spmdelExiting->getFirstNonPHI(),
				&DT, &LI, nullptr, "spmdel.end");
	} else { //We compared constants and İnitialValue >= FinalValue, so the program never even enters to the loop
		DEBUG_WITH_TYPE("loops",
				dbgs() << "Degenerate loop, no need to insert a new loop\n");
		return false;
	}
	spmdelInc = SplitBlock(spmdelBody, spmdelBody->getTerminator(), &DT, &LI,
			nullptr, "spmdel.inc");

	//Step Logic and actual loop mechanic is here
	Builder.SetInsertPoint(spmdelInc);
	Instruction *stepInstClone = loopBounds->getStepInst().clone();
	stepInstClone->setName("spmdel.inc");
	stepInstClone->insertBefore(spmdelInc->getTerminator());

	Builder.SetInsertPoint(spmdelBody->getTerminator());
	PHINode *IndVar = Builder.CreatePHI(stepValue->getType(), 2, "spmdel.j");
	IndVar->addIncoming(&IVInitialVal, spmdelPreheader);
	IndVar->addIncoming(stepInstClone, spmdelInc);

	Value *toChange;
	for (auto iter = stepInstClone->op_begin(); iter != stepInstClone->op_end();
			++iter) {
		if ((*iter) != stepValue) {
			toChange = (*iter);
		}
	}
	stepInstClone->replaceUsesOfWith(toChange, IndVar);

	spmdelInc->getTerminator()->eraseFromParent();
	Builder.SetInsertPoint(spmdelInc);
	Value *EndCond = Builder.CreateICmpSLT(stepInstClone, &IVFinalVal,
			"spmdel.end_cmp");
	Instruction *EndCondInst = cast<Instruction>(EndCond);
	Builder.SetInsertPoint(EndCondInst->getParent());
	Builder.CreateCondBr(EndCond, spmdelBody, spmdelExiting);

	//Actual spmdel call insertion on body
	Value *i32ptr = insertGEP(cast<AllocaInst>(edgeArray), IndVar,
			spmdelBody->getTerminator(), llvmContext);
	errs() << "*i32ptr" << *i32ptr << "\n";
	Builder.SetInsertPoint(spmdelBody->getTerminator());

	Value *args[] = { i32ptr, ConstantInt::get(i32_type, 0/*value*/, true) };
	Builder.CreateCall(spmdel_intrinsic, args);

	//Update LI and DT
	New.addBlockEntry(spmdelBody);
	New.addBlockEntry(spmdelInc);
	//This means that outermostloop is a top level loop and new loop is also a top level loop
	if (!outerMostLoop) {
		LI.addTopLevelLoop(&New);
	}
	//Outermost loop can be either a top-level loop or an innerloop but
	//we insert the new loop under outermostloop
	else {
		//Now can add the new loop as a child
		outerMostLoop->addChildLoop(&New);
		LI.changeLoopFor(spmdelBody, &New);
		LI.changeLoopFor(spmdelInc, &New);
	}
#ifndef NDEBUG
	assert(
			DT.verify(DominatorTree::VerificationLevel::Full)
					&& "Dominator tree is invalid");
	New.verifyLoop();
	if (outerMostLoop) {
		outerMostLoop->verifyLoop();
	}
	LI.verify(DT);
#endif
	return true;
}

static bool insertSPMREG(LoadInst *I, Loop *L, LLVMContext &llvmContext,
		LoopInfo &LI, DominatorTree &DT, Function *spmreg_intrinsic) {
	llvm::Type *i32_type = llvm::IntegerType::getInt32Ty(llvmContext);
	llvm::Type *i1_type = Type::getInt1Ty(llvmContext);
	BasicBlock::iterator ii(I);
	Value *loadPtrOperand = I->getPointerOperand();
	BasicBlock *loopEntrance = L->getLoopPreheader();
	if (L->isGuarded()) {
		loopEntrance = loopEntrance->getPrevNode();
	}

	errs() << "Loop Entrance is : " << loopEntrance->getName() << "\n";
	IRBuilder<> Builder(loopEntrance->getTerminator());
	Value *spmHit = Builder.CreateAlloca(i1_type, nullptr, "spmreg_hit");
	Builder.CreateStore(ConstantInt::get(i1_type, 1/*value*/, true), spmHit);

	Builder.SetInsertPoint(I);
	Value *spmHitValue = Builder.CreateLoad(spmHit, "spmreg_hitPredicate");
	Value *CompareSpmHit = Builder.CreateICmpEQ(spmHitValue,
			ConstantInt::get(i1_type, 1/*value*/, true));

	BasicBlock *IfSPMHit = SplitBlock(I->getParent(), I, &DT, &LI, nullptr,
			"spmreg_if_hit");
	BasicBlock *IfSPMNotHitInner = SplitBlock(I->getParent(), I, &DT, &LI,
			nullptr, "spmreg_if_nothit_inner");
	BasicBlock *IfSPMNotHit = SplitBlock(I->getParent(), I, &DT, &LI, nullptr,
			"spmreg_if_nothit");
	BasicBlock *IfSPMRest = SplitBlock(I->getParent(), I, &DT, &LI, nullptr,
			"spmreg_rest");

	Builder.SetInsertPoint(cast<Instruction>(CompareSpmHit)->getNextNode());
	Builder.CreateCondBr(CompareSpmHit, IfSPMHit, IfSPMNotHit);
	cast<Instruction>(CompareSpmHit)->getParent()->getTerminator()->eraseFromParent();

	Builder.SetInsertPoint(IfSPMHit->getTerminator());
	Value *spm_args[] = { I->getPointerOperand(), ConstantInt::get(i32_type,
			0/*value*/, true) };
	CallInst *call_inst = Builder.CreateCall(spmreg_intrinsic, spm_args,
			"valueFromSpm");
	Value *CompareSpmHitInner = Builder.CreateICmpEQ(call_inst,
			ConstantInt::get(i32_type, SPM_REG_SPECIAL_VALUE/*value*/, true),
			"spreg_hitPredicate_inner");
	Builder.CreateCondBr(CompareSpmHitInner, IfSPMNotHitInner, IfSPMRest);
	IfSPMHit->getTerminator()->eraseFromParent();

	Builder.SetInsertPoint(IfSPMNotHitInner->getTerminator());
	Builder.CreateStore(ConstantInt::get(i1_type, 0/*value*/, true), spmHit);

	Builder.SetInsertPoint(IfSPMNotHit->getTerminator());
	Value *loadedValue = Builder.CreateLoad(i32_type, loadPtrOperand);

	Builder.SetInsertPoint(I);
	PHINode *ActualValue = Builder.CreatePHI(i32_type, 2, "actual_load");
	ActualValue->addIncoming(call_inst, IfSPMHit);
	ActualValue->addIncoming(loadedValue, IfSPMNotHit);

	I->replaceAllUsesWith(ActualValue);
	I->eraseFromParent();
	return true;
}

//===----------------------------------------------------------------------===//
//SCEVFindValues Implementations
//
bool SCEVFindValues::follow(const SCEV *S) {
	const SCEVUnknown *Unknown = dyn_cast<SCEVUnknown>(S);
	const SCEVAddRecExpr *AddRecExpr = dyn_cast<SCEVAddRecExpr>(S);
	if (AddRecExpr) {
		errs() << "\tStep recurrence : " << *AddRecExpr->getStepRecurrence(SE)
				<< "\n";
		const SCEVAddExpr *AddExpr = dyn_cast<SCEVAddExpr>(
				AddRecExpr->getOperand(0));
		if (AddExpr) {
			errs() << "\tAddExpr: " << *AddExpr->getOperand(0) << "\n";
		}
	}

	if (!Unknown)
		return true;

	Values.insert(Unknown->getValue());
	Instruction *Inst = dyn_cast<Instruction>(Unknown->getValue());
	if (!Inst
			|| (Inst->getOpcode() != Instruction::SRem
					&& Inst->getOpcode() != Instruction::SDiv))
		return false;

	auto *Dividend = SE.getSCEV(Inst->getOperand(1));
	if (!isa<SCEVConstant>(Dividend))
		return false;

	auto *Divisor = SE.getSCEV(Inst->getOperand(0));
	SCEVFindValues FindValues(SE, Values);
	SCEVTraversal<SCEVFindValues> ST(FindValues);
	ST.visitAll(Dividend);
	ST.visitAll(Divisor);

	return false;
}

static void countBlocksInLoop(Loop *L, unsigned nesAng) {
	unsigned numBlocks = 0;
	Loop::block_iterator bb;

	for (bb = L->block_begin(); bb != L->block_end(); ++bb) {
		numBlocks++;
	}
	DEBUG_WITH_TYPE("loops",
			dbgs() << "Loop level " << nesAng << " has " << numBlocks
					<< " blocks\n");
	BasicBlock *predecessor = L->getLoopPredecessor();
	DEBUG_WITH_TYPE("loops",
			dbgs() << "Loop predecessor block is " << predecessor->getName()
					<< "\n");

	SmallVector<std::pair<BasicBlock*, BasicBlock*>, 8> ExitEdges;
	L->getExitEdges(ExitEdges);
	if (ExitEdges.size() == 1) {
		DEBUG_WITH_TYPE("loops", dbgs() << "it has only one exit edge\n");
	}
	BasicBlock *from_block = ExitEdges[0].first;
	BasicBlock *to_block = ExitEdges[0].second;
	DEBUG_WITH_TYPE("loops",
			dbgs() << "Exit Edge from " << from_block->getName() << " to "
					<< to_block->getName() << "\n");
	DEBUG_WITH_TYPE("loops",
			dbgs() << "Loop depth : " << L->getLoopDepth() << "\n");
	Loop *parent_loop = L->getParentLoop();
	if (parent_loop) {
		DEBUG_WITH_TYPE("loops",
				dbgs() << "Parent loop is : " << parent_loop->getName()
						<< "\n");
	} else {
		DEBUG_WITH_TYPE("loops", dbgs() << "This is a top level loop\n");
	}
	DEBUG_WITH_TYPE("loops",
			dbgs() << "Top level parent loop is "
					<< outermostParentLoop(L)->getName() << "\n\n");

	std::vector<Loop*> subLoops = L->getSubLoops();
	Loop::iterator j, f;
	for (j = subLoops.begin(), f = subLoops.end(); j != f; ++j) {
		countBlocksInLoop(*j, nesAng + 1);
	}
}

static Loop* outermostParentLoop(Loop *L) {
	Loop *parent_loop = L->getParentLoop();
	if (parent_loop) {
		return outermostParentLoop(parent_loop);
	} else {
		return L;
	}
}

static void findValues(const SCEV *Expr, ScalarEvolution &SE,
		SetVector<Value*> &Values) {
	SCEVFindValues FindValues(SE, Values);
	SCEVTraversal<SCEVFindValues> ST(FindValues);
	ST.visitAll(Expr);
}

static void SCEVDebug(const SCEV &scev) {
//		std::string Result = "allocaInst->getType() ";
//		raw_string_ostream OS(Result);
	raw_ostream *OS = &dbgs();
	switch (static_cast<SCEVTypes>(scev.getSCEVType())) {

	case scConstant:
		cast<SCEVConstant>(&scev)->getValue()->printAsOperand(*OS, false);
		return;
	case scTruncate: {
		const SCEVTruncateExpr *Trunc = cast<SCEVTruncateExpr>(&scev);
		const SCEV *Op = Trunc->getOperand();
		*OS << "(trunc " << *Op->getType() << " " << *Op << " to "
				<< *Trunc->getType() << ")";
		return;
	}
	case scZeroExtend: {
		const SCEVZeroExtendExpr *ZExt = cast<SCEVZeroExtendExpr>(&scev);
		const SCEV *Op = ZExt->getOperand();
		*OS << "(zext " << *Op->getType() << " " << *Op << " to "
				<< *ZExt->getType() << ")";
		return;
	}
	case scSignExtend: {
		const SCEVSignExtendExpr *SExt = cast<SCEVSignExtendExpr>(&scev);
		const SCEV *Op = SExt->getOperand();
		*OS << "(sext " << *Op->getType() << " " << *Op << " to "
				<< *SExt->getType() << ")";
		return;
	}
	case scAddRecExpr: {
		const SCEVAddRecExpr *AR = cast<SCEVAddRecExpr>(&scev);
		errs() << (*AR->getOperand(0)).getSCEVType() << "\n";
		*OS << "{" << *AR->getOperand(0);
		for (unsigned i = 1, e = AR->getNumOperands(); i != e; ++i)
			*OS << ",+," << *AR->getOperand(i);
		*OS << "}<";
		if (AR->hasNoUnsignedWrap())
			*OS << "nuw><";
		if (AR->hasNoSignedWrap())
			*OS << "nsw><";
		if (AR->hasNoSelfWrap()
				&& !AR->getNoWrapFlags(
						(SCEV::NoWrapFlags) (SCEV::FlagNUW | SCEV::FlagNSW)))
			*OS << "nw><";
		AR->getLoop()->getHeader()->printAsOperand(*OS, /*PrintType=*/
		false);
		*OS << ">";
		return;
	}
	case scAddExpr:
	case scMulExpr:
	case scUMaxExpr:
	case scSMaxExpr:
	case scUMinExpr:
	case scSMinExpr: {
		const SCEVNAryExpr *NAry = cast<SCEVNAryExpr>(&scev);
		const char *OpStr = nullptr;
		switch (NAry->getSCEVType()) {
		case scAddExpr:
			OpStr = " + ";
			break;
		case scMulExpr:
			OpStr = " * ";
			break;
		case scUMaxExpr:
			OpStr = " umax ";
			break;
		case scSMaxExpr:
			OpStr = " smax ";
			break;
		case scUMinExpr:
			OpStr = " umin ";
			break;
		case scSMinExpr:
			OpStr = " smin ";
			break;
		}
		*OS << "(";
		for (SCEVNAryExpr::op_iterator I = NAry->op_begin(), E = NAry->op_end();
				I != E; ++I) {
			*OS << **I;
			if (std::next(I) != E)
				*OS << OpStr;
		}
		*OS << ")";
		switch (NAry->getSCEVType()) {
		case scAddExpr:
		case scMulExpr:
			if (NAry->hasNoUnsignedWrap())
				*OS << "<nuw>";
			if (NAry->hasNoSignedWrap())
				*OS << "<nsw>";
		}
		return;
	}
	case scUDivExpr: {
		const SCEVUDivExpr *UDiv = cast<SCEVUDivExpr>(&scev);
		*OS << "(" << *UDiv->getLHS() << " /u " << *UDiv->getRHS() << ")";
		return;
	}
	case scUnknown: {
		const SCEVUnknown *U = cast<SCEVUnknown>(&scev);
		Type *AllocTy;
		if (U->isSizeOf(AllocTy)) {
			*OS << "sizeof(" << *AllocTy << ")";
			return;
		}
		if (U->isAlignOf(AllocTy)) {
			*OS << "alignof(" << *AllocTy << ")";
			return;
		}

		Type *CTy;
		Constant *FieldNo;
		if (U->isOffsetOf(CTy, FieldNo)) {
			*OS << "offsetof(" << *CTy << ", ";
			FieldNo->printAsOperand(*OS, false);
			*OS << ")";
			return;
		}

		// Otherwise just print it normally.
		U->getValue()->printAsOperand(*OS, false);
		return;
	}
	case scCouldNotCompute:
		*OS << "***COULDNOTCOMPUTE***";
		return;
	}
	llvm_unreachable("Unknown SCEV kind!");
}

//TODO this is useful for smart processing but not for now
static void processSCEV(LoadInst *loadInst, ScalarEvolution *SE, Loop *L) {
	const SCEV *scev = SE->getSCEV(loadInst->getPointerOperand());
//scev->dump();
	SCEVDebug(*scev);
	DEBUG_WITH_TYPE("loops", dbgs() << "\n");
	SetVector<Value*> SCEVValues;
	findValues(scev, *SE, SCEVValues);
	DEBUG_WITH_TYPE("loops", dbgs() << "Values for this SCEV:\n");
	for (auto const &it : SCEVValues) {
		DEBUG_WITH_TYPE("loops", dbgs() << *it << "\n");
	}

	const SCEV *ExitValue = SE->getSCEVAtScope(scev, L->getParentLoop());
	DEBUG_WITH_TYPE("loops", dbgs() << "Exit  Value: ");
	if (!SE->isLoopInvariant(ExitValue, L)) {
		DEBUG_WITH_TYPE("loops", dbgs() << "Unknown\n");
	} else {
		DEBUG_WITH_TYPE("loops", dbgs() << *ExitValue << "\n");
	}
	SCEVValues.clear();
	findValues(ExitValue, *SE, SCEVValues);
	DEBUG_WITH_TYPE("loops", dbgs() << "Values for this SCEV(Exit):\n");
	for (auto const &it : SCEVValues) {
		DEBUG_WITH_TYPE("loops", dbgs() << *it << "\n");
	}
}

static void dumpLoopBounds(Loop *L, ScalarEvolution &SE) {
	DEBUG_WITH_TYPE("loops", dbgs() << "Loop head: " << L->getName() << "\n");
	Optional<Loop::LoopBounds> Bounds = L->getBounds(SE);
	if (Bounds.hasValue()) {
		Value &IVInitialVal = Bounds->getInitialIVValue();
		Value &IVFinalVal = Bounds->getFinalIVValue();
		Instruction &stepInst = Bounds->getStepInst();
		Value *stepVal = Bounds->getStepValue();
		PHINode *inductionVar = L->getInductionVariable(SE);
		const SCEV *backedgeCount = SE.getBackedgeTakenCount(L);

		DEBUG_WITH_TYPE("loops",
				dbgs() << "IVInitialVal: " << IVInitialVal << "\n");
		DEBUG_WITH_TYPE("loops",
				dbgs() << "IVFinalVal: " << IVFinalVal << "\n");
		DEBUG_WITH_TYPE("loops",
				dbgs() << "Step Instruction: " << stepInst << "\n");
		DEBUG_WITH_TYPE("loops", dbgs() << "Step Value: " << *stepVal << "\n");
		DEBUG_WITH_TYPE("loops",
				dbgs() << "Bacekdge count: " << *backedgeCount << "\n");
		DEBUG_WITH_TYPE("loops",
				dbgs() << "Induction Variable: " << *inductionVar << "\n");

	} else {
		errs() << "Can't find any bounds\n";
	}
}

static bool insertSPMDEL(SPMDELInfo &spmdelInfo, LLVMContext &llvmContext,
		Instruction *edgeArray, Function *spmdel_intrinsic) {

	bool modified = false;
	if (spmdelInfo.innerLoops.size() > 1) { //Find min bound and max bounds

	} else { //Trivial cases
		BasicBlock *exitingBlock = spmdelInfo.outerMostLoop.getExitingBlock();
		DEBUG_WITH_TYPE("loops",
				dbgs() << "Exiting Block: " << exitingBlock->getName() << "\n");

		Loop *targetLoop = *(spmdelInfo.innerLoops.begin());
		Optional<Loop::LoopBounds> Bounds = targetLoop->getBounds(
				spmdelInfo.SE);
		Loop *outerMostLoop;
		BasicBlock *insertionPoint;
		if (&spmdelInfo.outerMostLoop == *(spmdelInfo.innerLoops.begin())) {
			outerMostLoop = nullptr;
			Loop *PL = spmdelInfo.outerMostLoop.getParentLoop();
			assert(
					!PL
							&& "Outermost loop must be a top-level loop if only single inner loop and equal to outermost");
			insertionPoint = spmdelInfo.outerMostLoop.getExitBlock();
			if (spmdelInfo.outerMostLoop.isGuarded()) {
				insertionPoint = insertionPoint->getNextNode();
			}
		} else {
			outerMostLoop = &spmdelInfo.outerMostLoop;
			SmallVector<Loop*, 4> PreorderLoops =
					spmdelInfo.outerMostLoop.getLoopsInPreorder();
			insertionPoint = PreorderLoops.back()->getExitBlock();
			if (PreorderLoops.back()->isGuarded()) {
				insertionPoint = insertionPoint->getNextNode();
			}
		}

//		modified = createLoopFromLoopBounds(Bounds, outerMostLoop,
//				insertionPoint, spmdelInfo.LI, spmdelInfo.DT, edgeArray,
//				spmdel_intrinsic, llvmContext);
		Value *i32ptr = insertGEP(cast<AllocaInst>(edgeArray),
				&Bounds->getInitialIVValue(), insertionPoint->getTerminator(),
				llvmContext);
		errs() << "*i32ptr" << *i32ptr << "\n";
		IRBuilder<> Builder(cast<Instruction>(i32ptr)->getNextNode());
		llvm::Type *i32_type = llvm::IntegerType::getInt32Ty(llvmContext);
		Value *args[] = { i32ptr, ConstantInt::get(i32_type, 0/*value*/, true) };
		Builder.CreateCall(spmdel_intrinsic, args);
	}

	return modified;
}
