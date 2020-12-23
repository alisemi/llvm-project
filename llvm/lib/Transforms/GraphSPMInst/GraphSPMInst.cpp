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

using namespace llvm;

//void findEdgeArray(std::map<StringRef, AllocaInst*> &spmcon_locations,
//		Value *&edgeArray);

namespace {
struct GraphSPMInstPass: public ModulePass {
	static char ID;
	GraphSPMInstPass() :
			ModulePass(ID) {
	}

	void getAnalysisUsage(AnalysisUsage &AU) const override;
	bool runOnModule(Module &M) override;
};
}

//===----------------------------------------------------------------------===//
//Static Function Declarations
//
static void findEdgeArray(std::map<StringRef, AllocaInst*> &spmcon_locations,
		Value *&edgeArray);

static void findVertexArray(std::map<StringRef, AllocaInst*> &spmcon_locations,
		Value *&vertexArray);

static bool insertSPMCON(std::map<StringRef, AllocaInst*> &spmcon_locations,
		LLVMContext &llvmContext, Function *spmcon_intrinsic);

static bool insertSPMDEL(SPMDELInfo &spmdelInfo, LLVMContext &llvmContext,
		Instruction *edgeArray, Function *spmdel_intrinsic);

static bool insertSPMDEL(std::map<StringRef, AllocaInst*> &spmcon_locations,
		LLVMContext &llvmContext, Value *edgeArray, Function *delspm_intrinsic);

static void findAnnotatedVariables(Module &M,
		std::map<Value*, StringRef> &annotated_vars_map,
		SmallVector<Instruction*, 4> &annotationCalls);

static void functionAnnotattions(Module &M);

//Returns itself it is already a top-level loop
static Loop* outermostParentLoop(Loop *L);

static void findValues(const SCEV *Expr, ScalarEvolution &SE,
		SetVector<Value*> &Values);

static void SCEVDebug(const SCEV &scev);

static void processSCEV(LoadInst *loadInst, ScalarEvolution *SE, Loop *L);

static void dumpLoopBounds(Loop *L, ScalarEvolution &SE);

static Loop* outermostLoopForSpmHelper(Loop *L, Instruction *edgeArray,
		std::map<Instruction*, Loop*> *loadLoopMap);

static void outermostLoopForSpm(Loop *L, ScalarEvolution *SE, LoopInfo *LI,
		DominatorTree *DT, Instruction *edgeArray,
		std::vector<Instruction*> &spmRegLocations,
		std::map<Instruction*, Loop*> &loadLoopMap,
		SmallSet<SPMDELInfo*, 4> &spmDelInfos);

static void countBlocksInLoop(Loop *L, unsigned nesAng);

static bool createLoopFromLoopBounds(Optional<Loop::LoopBounds> &loopBounds,
		Loop *outerMostLoop, BasicBlock *insertionPoint, LoopInfo &LI,
		DominatorTree &DT, Instruction *edgeArray, Function *spmdel_intrinsic,
		LLVMContext &llvmContext);

static bool insertSPMREG(LoadInst *I, Loop *L, LLVMContext &llvmContext,
		LoopInfo &LI, DominatorTree &DT, Function *spmreg_intrinsic);

static bool insertMEMSPM(std::map<StringRef, AllocaInst*> &spmcon_locations,
		LLVMContext &llvmContext, Value *vertexArray,
		Function *memspm_intrinsic);

static Value* insertGEP(AllocaInst *inst, Value *IndexValue,
		Instruction *insertionPoint, LLVMContext &llvmContext);

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

//===----------------------------------------------------------------------===//
//Static Function Implementations
//

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

static void findEdgeArray(std::map<StringRef, AllocaInst*> &spmcon_locations,
		Value *&edgeArray) {
	std::map<StringRef, AllocaInst*>::iterator it;
	it = spmcon_locations.find(ANNO_RISCV_EDGES);
	if (it != spmcon_locations.end()) {
		edgeArray = (Value*) it->second;
	}
}

static void findVertexArray(std::map<StringRef, AllocaInst*> &spmcon_locations,
		Value *&vertexArray) {
	std::map<StringRef, AllocaInst*>::iterator it;
	it = spmcon_locations.find(ANNO_RISCV_OFFSETS);
	if (it != spmcon_locations.end()) {
		vertexArray = (Value*) it->second;
	}
}

static bool insertMEMSPM(std::map<StringRef, AllocaInst*> &spmcon_locations,
		LLVMContext &llvmContext, Value *vertexArray,
		Function *memspm_intrinsic) {
	bool modified = false;
	llvm::Type *i32_type = llvm::IntegerType::getInt32Ty(llvmContext);
	std::map<StringRef, AllocaInst*>::iterator it;
	it = spmcon_locations.find(ANNO_RISCV_MEMSPM);
	if (it != spmcon_locations.end()) {
		DEBUG_WITH_TYPE("annotation",
				dbgs() << "MEMSPM: Found at " << it->second->getName() << " - "
						<< it->first << "\n");
		// What is using this instruction?
		for (auto iter = it->second->user_begin();
				iter != it->second->user_end(); ++iter) {
			StoreInst *storeUser = dyn_cast<StoreInst>(*iter);
			if (storeUser) {
				DEBUG_WITH_TYPE("annotation",
						dbgs() << "We have a store instruction" << "\n");
				Value *valueOperand = storeUser->getValueOperand();
				Value *i32ptr = insertGEP(cast<AllocaInst>(vertexArray),
						valueOperand, storeUser, llvmContext);
				Value *args[] = { i32ptr, ConstantInt::get(i32_type, 0/*value*/,
						true) };
				CallInst *call_inst = CallInst::Create(memspm_intrinsic, args);
				ReplaceInstWithInst(storeUser, call_inst);
			}
		}
	}
	return modified;
}

//If the alloca variable is of type [11 x i32]*, indexList size is 2 but
//if it is *i32 already then size should be only 1
static Value* insertGEP(AllocaInst *inst, Value *IndexValue,
		Instruction *insertionPoint, LLVMContext &llvmContext) {
	llvm::Type *i32_type = llvm::IntegerType::getInt32Ty(llvmContext);
	IRBuilder<> Builder(insertionPoint);
	if (dyn_cast<ArrayType>(inst->getAllocatedType())) {
		Value *indexList[2] = { ConstantInt::get(i32_type, 0/*value*/, true),
				IndexValue };
		return Builder.CreateInBoundsGEP(inst, indexList);
	} else if (dyn_cast<PointerType>(inst->getAllocatedType())) {
		Value *indexList[1] = { IndexValue };
		Value *prei32Ptr = Builder.CreateLoad(inst);
		return Builder.CreateGEP(prei32Ptr, indexList);
	}
	return nullptr;
}

static bool insertSPMCON(std::map<StringRef, AllocaInst*> &spmcon_locations,
		LLVMContext &llvmContext, Function *spmcon_intrinsic) {
	bool modified = false;
	llvm::Type *i32_type = llvm::IntegerType::getInt32Ty(llvmContext);
	std::map<StringRef, AllocaInst*>::iterator it;

	it = spmcon_locations.find(ANNO_RISCV_EDGES);
	if (it != spmcon_locations.end()) {
		DEBUG_WITH_TYPE("annotation",
				dbgs() << "SPMCON: Found at " << it->second->getName() << " - "
						<< it->first << "\n");
		Value *i32ptr = insertGEP(it->second,
				ConstantInt::get(i32_type, 0/*value*/, true),
				it->second->getParent()->getTerminator(), llvmContext);
		assert(i32ptr && "No pointer to the edges of the graph");
		errs() << "i32ptr is " << *i32ptr << "\n";
		Value *args[] = { i32ptr, ConstantInt::get(i32_type, 0/*value*/, true) };
		IRBuilder<> Builder(cast<Instruction>(i32ptr)->getNextNode());
		Builder.CreateCall(spmcon_intrinsic, args);
		modified = true;
	}

	it = spmcon_locations.find(ANNO_RISCV_VERSPDATA);
	if (it != spmcon_locations.end()) {
		DEBUG_WITH_TYPE("annotation",
				dbgs() << "SPMCON: Found at " << it->second->getName() << " - "
						<< it->first << "\n");
		Value *i32ptr = insertGEP(it->second,
				ConstantInt::get(i32_type, 0/*value*/, true),
				it->second->getParent()->getTerminator(), llvmContext);
		assert(i32ptr && "No pointer to the versp data of the graph");

		IRBuilder<> Builder(it->second->getParent()->getTerminator());
		Value *args[] = { i32ptr, ConstantInt::get(i32_type, 0/*value*/, true) };
		Builder.CreateCall(spmcon_intrinsic, args);

		std::map<StringRef, AllocaInst*>::iterator it2;
		it2 = spmcon_locations.find(ANNO_RISCV_VERSPDATA_SIZE);
		if (it2 != spmcon_locations.end()) { //Programmer already specified the versp data size
				//There should be store instruction for this AllocaInst
			SmallVector<StoreInst*, 4> storeForSizeAllocas;
			// What is using this instruction?
			for (auto iter = it2->second->user_begin();
					iter != it2->second->user_end(); ++iter) {
				StoreInst *storeUser = dyn_cast<StoreInst>(*iter);
				if (storeUser) { //There should be store instruction for this AllocaInst
					storeForSizeAllocas.push_back(storeUser);
				}
			}
			assert(
					storeForSizeAllocas.size() == 1
							&& "Versp Data size variable should be single");
			StoreInst *storeUser = *storeForSizeAllocas.begin();
			Value *valueOperand = storeUser->getValueOperand();
			DEBUG_WITH_TYPE("annotation",
					dbgs() << "Versp Data size: " << *valueOperand << "\n");
			Value *i32ptr = insertGEP(it->second, valueOperand,
					it->second->getParent()->getTerminator(), llvmContext);
			assert(i32ptr && "No pointer to the size of versp data graph");
			Value *args[] = { i32ptr, ConstantInt::get(i32_type, 0/*value*/,
					true) };
			Builder.CreateCall(spmcon_intrinsic, args);

		} else { //Try to look if the size can be determined from the program, i.e. if it is an array with static size
			ArrayType *allocaArrayType = dyn_cast<ArrayType>(
					it->second->getAllocatedType());
			assert(allocaArrayType && "Cannnot determine the versp data size");
			DEBUG_WITH_TYPE("annotation",
					dbgs() << "Versp Data size: "
							<< allocaArrayType->getArrayNumElements() << "\n");
			Value *i32ptr = insertGEP(it->second,
					ConstantInt::get(i32_type,
							allocaArrayType->getArrayNumElements() /*value*/,
							true), it->second->getParent()->getTerminator(),
					llvmContext);
			assert(i32ptr && "No pointer to the size of versp data graph");
			Value *args[] = { i32ptr, ConstantInt::get(i32_type, 0/*value*/,
					true) };
			Builder.CreateCall(spmcon_intrinsic, args);
		}

		modified = true;
	}
	return modified;
}

//Basic spmdel insertion by user-specified index value
static bool insertSPMDEL(std::map<StringRef, AllocaInst*> &spmcon_locations,
		LLVMContext &llvmContext, Value *edgeArray,
		Function *spmdel_intrinsic) {
	bool modified = false;
	llvm::Type *i32_type = llvm::IntegerType::getInt32Ty(llvmContext);
	std::map<StringRef, AllocaInst*>::iterator it;
	it = spmcon_locations.find(ANNO_RISCV_DELSPM);
	if (it != spmcon_locations.end()) {
		DEBUG_WITH_TYPE("annotation",
				dbgs() << "SPMDEL: Found at " << it->second->getName() << " - "
						<< it->first << "\n");
		// What is using this instruction?
		for (auto iter = it->second->user_begin();
				iter != it->second->user_end(); ++iter) {
			StoreInst *storeUser = dyn_cast<StoreInst>(*iter);
			if (storeUser) {
				DEBUG_WITH_TYPE("annotation",
						dbgs() << "We have a store instruction" << "\n");
				Value *valueOperand = storeUser->getValueOperand();
				Value *i32ptr = insertGEP(cast<AllocaInst>(edgeArray),
						valueOperand, storeUser, llvmContext);
				Value *args[] = { i32ptr, ConstantInt::get(i32_type, 0/*value*/,
						true) };
				CallInst *call_inst = CallInst::Create(spmdel_intrinsic, args);
				ReplaceInstWithInst(storeUser, call_inst);
			}
		}
	}
	return modified;
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

static void findAnnotatedVariables(Module &M,
		std::map<Value*, StringRef> &annotated_vars_map,
		SmallVector<Instruction*, 4> &annotationCalls) {
	for (Function &fn : M) {
		for (BasicBlock &bb : fn) {
			for (Instruction &inst : bb) {
				if (CallInst *callInst = dyn_cast<CallInst>(&inst)) {
					if (Function *calledFunction =
							callInst->getCalledFunction()) {
						if (calledFunction->getName().startswith(
								"llvm.var.annotation")) {
							DEBUG_WITH_TYPE("annotation",
									dbgs()
											<< "Here we found an annotate function call..\n");
							annotationCalls.push_back(callInst);
							Value *array_ptr = callInst->getOperand(0);
							BitCastInst *arrayPtrInst = cast<BitCastInst>(
									array_ptr);
							Value *annotatedVariable;
							errs() << *arrayPtrInst << "\n";
							assert(
									arrayPtrInst->getNumUses() == 1
											&& "There should be only one user for the bitcast");
							for (auto iter = arrayPtrInst->op_begin();
									iter != arrayPtrInst->op_end(); ++iter) {
								DEBUG_WITH_TYPE("annotation",
										dbgs() << (*iter)->getName() << "\n");
								annotatedVariable = (*iter);
							}
							Value *anno_ptr = callInst->getOperand(1);
							std::string Result;
							Result = "call_inst_op->getType() ";
							raw_string_ostream OS(Result);
							array_ptr->getType()->print(OS, false, false);
							DEBUG_WITH_TYPE("annotation",
									dbgs() << OS.str() << "\n");
							ConstantExpr *ce = cast<ConstantExpr>(anno_ptr);
							if (ce) {
								if (ce->getOpcode()
										== Instruction::GetElementPtr) {
									if (GlobalVariable *annoteStr = dyn_cast<
											GlobalVariable>(
											ce->getOperand(0))) {
										if (ConstantDataSequential *data =
												dyn_cast<ConstantDataSequential>(
														annoteStr->getInitializer())) {
											if (data->isString()) {
												DEBUG_WITH_TYPE("annotation",
														dbgs() << "Found data "
																<< data->getAsString()
																<< "\n");
												annotated_vars_map.insert(
														std::pair<Value*,
																StringRef>(
																annotatedVariable,
																data->getAsString()));
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
	}
}

static void functionAnnotattions(Module &M) {
//TODO global variables Annotations
// Process function annotations
	auto global_annos = M.getNamedGlobal("llvm.global.annotations");
	if (global_annos) {
		auto a = cast<ConstantArray>(global_annos->getOperand(0));
		for (unsigned int i = 0; i < a->getNumOperands(); i++) {
			auto e = cast<ConstantStruct>(a->getOperand(i));
			auto anno =
					cast<ConstantDataArray>(
							cast<GlobalVariable>(
									e->getOperand(1)->getOperand(0))->getOperand(
									0))->getAsCString();
			DEBUG_WITH_TYPE("annotation", dbgs() << "anno = " << anno << "\n");
			if (auto fn = dyn_cast<Function>(e->getOperand(0)->getOperand(0))) {
				auto anno =
						cast<ConstantDataArray>(
								cast<GlobalVariable>(
										e->getOperand(1)->getOperand(0))->getOperand(
										0))->getAsCString();
				fn->addFnAttr(anno); // <-- add function annotation here
			}
		}
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

static Loop* outermostLoopForSpmHelper(Loop *L, Instruction *edgeArray,
		std::map<Instruction*, Loop*> *loadLoopMap) {
	SmallSet<Loop*, 4> innerLoops;
	bool thisHasAnnotated = false;
	bool thisAlreadyOutermost = false;

	std::vector<Loop*> subLoops = L->getSubLoops();
	Loop::iterator j, f;
	for (j = subLoops.begin(), f = subLoops.end(); j != f; ++j) {
		Loop *result = outermostLoopForSpmHelper(*j, edgeArray, loadLoopMap);
		if (result) {
			innerLoops.insert(result);
			if (result == L) {
				thisAlreadyOutermost = true;
			}
		}
	}

	for (Loop::block_iterator bb = L->block_begin(); bb != L->block_end();
			++bb) {
		BasicBlock *cur_block = *bb;
		for (Instruction &inst : *cur_block) {
			if (LoadInst *load_inst = dyn_cast<LoadInst>(&inst)) {
				Value *addr = load_inst->getPointerOperand();
				bool annotated = false;
				for (auto iter = edgeArray->user_begin();
						iter != edgeArray->user_end(); ++iter) {
					if ((*iter) == addr) {
						annotated = true;
						break;
					}
					//Or look at users of user, for pointer to pointer case
					for (auto iter2 = (*iter)->user_begin();
							iter2 != (*iter)->user_end(); ++iter2) {
						if ((*iter2) == addr) {
							annotated = true;
							break;
						}
					}
				}
				if (annotated) {
					Loop *spmRegLoop =
							loadLoopMap->insert(
									std::pair<Instruction*, Loop*>(load_inst,
											L)).first->second;
					if (spmRegLoop == L) {
						thisHasAnnotated = true;
						innerLoops.clear();
						innerLoops.insert(L);
					}
				}
			}
		}
	}
	if (thisHasAnnotated) {
		if (L->getParentLoop()) {
			return L->getParentLoop();
		} else { //This is a top-level loop
			return L;
		}
	} else if (thisAlreadyOutermost) {
		return L;
	} else if (innerLoops.size() >= 1) {
		return (*innerLoops.begin());
	} else {
		return nullptr;
	}
}

//TODO Dominator Tree....
//Returns load instruction locations for spmreg and parent loop location for spmdel
static void outermostLoopForSpm(Loop *L, ScalarEvolution *SE, LoopInfo *LI,
		DominatorTree *DT, Instruction *edgeArray,
		std::vector<Instruction*> &spmRegLocations,
		std::map<Instruction*, Loop*> &loadLoopMap,
		SmallSet<SPMDELInfo*, 4> &spmDelInfos) {
	L->dump();

//Recursive method for loop processing
	std::map<Instruction*, Loop*> localLoadLoopMap;
	Loop *result = outermostLoopForSpmHelper(L, edgeArray, &localLoadLoopMap);
	if (result) {
		DEBUG_WITH_TYPE("loops",
				dbgs() << "result : " << result->getName() << "\n");
		DEBUG_WITH_TYPE("loops", dbgs() << "-----Load map-----\n");
		for (auto const &it : localLoadLoopMap) {
			DEBUG_WITH_TYPE("loops",
					dbgs() << *(it.first) << " <-> " << (it.second)->getName()
							<< "\n");
			DEBUG_WITH_TYPE("loops", dbgs() << "Bounds are:\n");
			dumpLoopBounds(it.second, *SE);
			DEBUG_WITH_TYPE("loops", dbgs() << "\n");
		}
		DEBUG_WITH_TYPE("loops", dbgs() << "----Loadmap Done----\n");
	} else {
		DEBUG_WITH_TYPE("loops", dbgs() << "No result\n");
	}

//Get the spmlocation values from map to stack
	SmallSet<Loop*, 4> innerLoops;
	for (auto const &it : localLoadLoopMap) {
		spmRegLocations.push_back(it.first);
		innerLoops.insert(it.second);
		loadLoopMap.insert(std::pair<Instruction*, Loop*>(it.first, it.second));
	}

	if (result) {
		SPMDELInfo *spmDelInfo = new SPMDELInfo(*result, *SE, *LI, *DT,
				innerLoops);
		spmDelInfos.insert(spmDelInfo);
	}
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

//===----------------------------------------------------------------------===//
// GraphSPMInstPass Implementation
//
bool GraphSPMInstPass::runOnModule(Module &M) {
	bool modified = false;

	Function *memspm_intrinsic = Intrinsic::getDeclaration(&M,
			Intrinsic::memspm, Type::getInt32PtrTy(M.getContext(), 0));
	Function *spmreg_intrinsic = Intrinsic::getDeclaration(&M,
			Intrinsic::spmreg, Type::getInt32PtrTy(M.getContext(), 0));
	Function *spmdel_intrinsic = Intrinsic::getDeclaration(&M,
			Intrinsic::spmdel, Type::getInt32PtrTy(M.getContext(), 0));
	Function *spmcon_intrinsic = Intrinsic::getDeclaration(&M,
			Intrinsic::spmcon, Type::getInt32PtrTy(M.getContext(), 0));

	functionAnnotattions(M);

//Get calls to annotations
	std::map<Value*, StringRef> annotated_vars_map;
	std::map<StringRef, AllocaInst*> spmcon_locations;
	Value *edgeArray = nullptr;
	Value *vertexArray = nullptr;
	SmallVector<Instruction*, 4> annotationCalls;

//Pre_annotated_vars
	findAnnotatedVariables(M, annotated_vars_map, annotationCalls);
	DEBUG_WITH_TYPE("annotation", dbgs() << "The annotated elements are : \n");
//Instead of auto, you can change it to Value* const&
	for (auto const &i : annotated_vars_map) {
		DEBUG_WITH_TYPE("annotation",
				dbgs() << i.first->getName() << " - " << i.second << "\n");
	}

//SPMCON
// Get spmcon locations
	DEBUG_WITH_TYPE("annotation", dbgs() << "SPMCON Locations...\n");
	for (Function &fn : M) {
		for (BasicBlock &bb : fn) {
			for (Instruction &inst : bb) {
				if (AllocaInst *allocaInst = dyn_cast<AllocaInst>(&inst)) {
					DEBUG_WITH_TYPE("annotation", dbgs() << inst << "\n");
					std::map<Value*, StringRef>::iterator it;
					it = annotated_vars_map.find(allocaInst);
					if (it != annotated_vars_map.end()) {
						DEBUG_WITH_TYPE("annotation",
								dbgs() << "SPMCON: Found at "
										<< it->first->getName() << " - "
										<< it->second << "\n");
						spmcon_locations.insert(
								std::pair<StringRef, AllocaInst*>(it->second,
										allocaInst));
					}
				}
			}
		}
	}

//Insert SPMCon instructions
	findEdgeArray(spmcon_locations, edgeArray);
	findVertexArray(spmcon_locations, vertexArray);

	assert(edgeArray && "No edge array found!");
	assert(vertexArray && "No vertex array found!");

	modified |= insertSPMCON(spmcon_locations, M.getContext(),
			spmcon_intrinsic);

	DEBUG_WITH_TYPE("annotation", dbgs() << "Edge Array Users:\n");
	Instruction *allocaInst = cast<Instruction>(edgeArray);
	for (auto iter = allocaInst->user_begin(); iter != allocaInst->user_end();
			++iter) {
		DEBUG_WITH_TYPE("annotation", dbgs() << *(*iter) << "\n");
	}

//TODO there should be no store for edge array, check for that
	Instruction *edgeArrayInst = cast<Instruction>(edgeArray);

	for (Function &fn : M) {
		if (fn.isDeclaration()) {
			continue;
		}
		//Loops
		std::vector<Instruction*> spmRegLocations;
		std::map<Instruction*, Loop*> loadLoopMap;
		std::map<Loop*, int> loopLevels;
		SmallSet<SPMDELInfo*, 4> spmdelInfos;

		ScalarEvolution &SE =
				getAnalysis<ScalarEvolutionWrapperPass>(fn).getSE();
		LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>(fn).getLoopInfo();
		DominatorTree &DT =
				getAnalysis<DominatorTreeWrapperPass>(fn).getDomTree();
		//Pre-process loops to get their level information, iterate only on top-level loops
		for (LoopInfo::iterator LIT = LI.begin(); LIT != LI.end(); ++LIT) {
			Loop *ll = *LIT;
			outermostLoopForSpm(ll, &SE, &LI, &DT, edgeArrayInst,
					spmRegLocations, loadLoopMap, spmdelInfos);
		}

		DEBUG_WITH_TYPE("loops", dbgs() << "SPMREG Locations: \n");
		for (auto &it : spmRegLocations) {
			Instruction *inst = it;
			DEBUG_WITH_TYPE("loops", dbgs() << *it << "\n");
			DEBUG_WITH_TYPE("loops",
					dbgs() << "What is this instruction using?\n");
			for (auto iter = inst->op_begin(); iter != inst->op_end(); ++iter) {
				DEBUG_WITH_TYPE("loops", dbgs() << (*iter)->getName() << "\n");
			}
			DEBUG_WITH_TYPE("loops",
					dbgs() << "What is using this instruction?\n");
			for (auto iter = inst->user_begin(); iter != inst->user_end();
					++iter) {
				DEBUG_WITH_TYPE("loops", dbgs() << (*iter)->getName() << "\n");
			}
		}
		DEBUG_WITH_TYPE("loops", dbgs() << "SPMREG Locations(LoadMap: \n");
		for (auto const &it : loadLoopMap) {
			DEBUG_WITH_TYPE("loops",
					dbgs() << *it.first << " <-> " << *it.second);
		}

		DEBUG_WITH_TYPE("loops", dbgs() << "SPMDEL Information: \n");
		for (auto it : spmdelInfos) {
			DEBUG_WITH_TYPE("loops",
					dbgs() << "Parent loop: " << it->outerMostLoop.getName()
							<< "\n");
			DEBUG_WITH_TYPE("loops", dbgs() << "Inner loops: \n");
			for (auto innerLoop : it->innerLoops) {
				DEBUG_WITH_TYPE("loops",
						dbgs() << innerLoop->getName() << "\n");
			}
		}

		DEBUG_WITH_TYPE("loops", dbgs() << "\n SPMDEL Insertion....\n");
		//SPMDEL insertion
		for (auto it : spmdelInfos) {
			//		modified |= insertSPMDEL(*it, M.getContext(), edgeArrayInst,
			//				spmdel_intrinsic);
			modified |= insertSPMDEL(spmcon_locations, M.getContext(),
					edgeArray, spmdel_intrinsic);
		}

		//SPMREG insertion
		DEBUG_WITH_TYPE("loops", dbgs() << "\n SPMREG Insertion....\n");
		for (auto const &it : loadLoopMap) {
			Instruction *inst = it.first;
			Loop *L = it.second;
			LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>(
					*(inst->getParent()->getParent())).getLoopInfo();
			DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>(
					*(inst->getParent()->getParent())).getDomTree();
			LoadInst *I = cast<LoadInst>(inst);
			modified |= insertSPMREG(I, L, M.getContext(), LI, DT,
					spmreg_intrinsic);
			LI.verify(DT);
		}

		//MEMSPM insertion
		DEBUG_WITH_TYPE("annotation", dbgs() << "\n MEMSPM Insertion....\n");
		modified |= insertMEMSPM(spmcon_locations, M.getContext(), vertexArray,
				memspm_intrinsic);

	}

//Remove annotation calls, so that O1 level optimizations works better
	DEBUG_WITH_TYPE("annotation", dbgs() << "\n Remove annotation calls....\n");
	for (auto const &it : annotationCalls) {
		it->eraseFromParent();
	}

	return modified;
}

void GraphSPMInstPass::getAnalysisUsage(AnalysisUsage &AU) const {
//AU.setPreservesCFG();
	AU.addRequired<LoopInfoWrapperPass>();
	AU.addRequired<ScalarEvolutionWrapperPass>();
	AU.addRequired<DominatorTreeWrapperPass>();
}

char GraphSPMInstPass::ID = 0;
/*
 // Automatically enable the pass.
 // http://adriansampson.net/blog/clangpass.html
 static void registerGraphSPMInstPass(const PassManagerBuilder &,
 legacy::PassManagerBase &PM) {
 PM.add(new GraphSPMInstPass());
 }
 static RegisterStandardPasses
 RegisterMyPass(PassManagerBuilder::EP_EarlyAsPossible,
 registerGraphSPMInstPass);
 */
static RegisterPass<GraphSPMInstPass> X("graphSPMInst", "GraphSPMInst Pass",
		false, false);
