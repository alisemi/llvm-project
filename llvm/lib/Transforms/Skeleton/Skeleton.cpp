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
#include <stack>
#include <vector>
#include <algorithm>
#include <string>
#include <map>

using namespace llvm;

namespace {
struct SkeletonPass: public ModulePass {
	static char ID;
	SkeletonPass() :
			ModulePass(ID) {
	}

	struct SpmInfo {
		std::stack<Instruction*> loadStack; //Loads to be replaced with spmreg
		BasicBlock *memspmLocation; //Basic Blocks to insert memspm instructions
		std::set<Value*> neededArrays;
	};

	//Returns itself it is already a top-level loop
	Loop* outermostParentLoop(Loop *L) {
		Loop *parent_loop = L->getParentLoop();
		if (parent_loop) {
			return outermostParentLoop(parent_loop);
		} else {
			return L;
		}
	}

	void countBlocksInLoop(Loop *L, unsigned nesAng) {
		unsigned numBlocks = 0;
		Loop::block_iterator bb;

		for (bb = L->block_begin(); bb != L->block_end(); ++bb) {
			numBlocks++;
		}
		errs() << "Loop level " << nesAng << " has " << numBlocks
				<< " blocks\n";

		BasicBlock *predecessor = L->getLoopPredecessor();
		errs() << "Loop predecessor block is " << predecessor->getName()
				<< "\n";

		SmallVector<std::pair<BasicBlock*, BasicBlock*>, 8> ExitEdges;
		L->getExitEdges(ExitEdges);
		if (ExitEdges.size() == 1) {
			errs() << "it has only one exit edge\n";
		}
		BasicBlock *from_block = ExitEdges[0].first;
		BasicBlock *to_block = ExitEdges[0].second;
		errs() << "Exit Edge from " << from_block->getName() << " to "
				<< to_block->getName() << "\n";

		errs() << "Loop depth : " << L->getLoopDepth() << "\n";
		Loop *parent_loop = L->getParentLoop();
		if (parent_loop) {
			errs() << "Parent loop is : " << parent_loop->getName() << "\n";
		} else {
			errs() << "This is a top level loop\n";
		}
		errs() << "Top level parent loop is "
				<< outermostParentLoop(L)->getName() << "\n";
		errs() << "\n";

		std::vector<Loop*> subLoops = L->getSubLoops();
		Loop::iterator j, f;
		for (j = subLoops.begin(), f = subLoops.end(); j != f; ++j) {
			countBlocksInLoop(*j, nesAng + 1);
		}
	}

	virtual bool runOnModule(Module &M) {
		bool modified = false;
		const StringRef SPM_ANNO = StringRef("ali", 4); //For some reasons, annotated string value has length 4
//		const StringRef SPM_ANNO = "ali\0";

//		FunctionCallee memspm_func = M.getOrInsertFunction("memspm",
//				Type::getVoidTy(M.getContext()),
//				IntegerType::getInt32Ty(M.getContext()),
//				PointerType::getInt32PtrTy(M.getContext(), 0));
//		FunctionCallee dummy_func = M.getOrInsertFunction("dummy",
//				Type::getVoidTy(M.getContext()));

		Function *memspm_intrinsic = Intrinsic::getDeclaration(&M,
				Intrinsic::memspm, Type::getInt32PtrTy(M.getContext(), 0));
		Function *spmreg_intrinsic = Intrinsic::getDeclaration(&M,
				Intrinsic::spmreg, Type::getInt32PtrTy(M.getContext(), 0));
		Function *spmdel_intrinsic = Intrinsic::getDeclaration(&M,
				Intrinsic::spmdel, Type::getInt32PtrTy(M.getContext(), 0));

		//Get calls to annotations
		std::vector<Value*> pre_annotated_vars;
//		std::vector<Value*> alloca_vars;
		std::vector<Value*> true_annotated_vars;
		std::map<Value*, Value*> true_annotated_geps;
		for (Function &fn : M) {
			for (BasicBlock &bb : fn) {
				for (Instruction &inst : bb) {
					if (CallInst *callInst = dyn_cast<CallInst>(&inst)) {
						if (Function *calledFunction =
								callInst->getCalledFunction()) {
							if (calledFunction->getName().startswith(
									"llvm.var.annotation")) {
								errs()
										<< "Here we found an annotate function call..\n";
								Value *array_ptr = callInst->getOperand(0);
								Value *anno_ptr = callInst->getOperand(1);

								errs() << "call_inst_op->getName() :"
										<< array_ptr->getName() << "\n";
								std::string Result;
								Result = "call_inst_op->getType() ";
								raw_string_ostream OS(Result);
								array_ptr->getType()->print(OS, false, false);
								errs() << OS.str() << "\n";

								ConstantExpr *ce = cast<ConstantExpr>(anno_ptr);
								if (ce) {
									if (ce->getOpcode()
											== Instruction::GetElementPtr) {
										if (GlobalVariable *annoteStr =
												dyn_cast<GlobalVariable>(
														ce->getOperand(0))) {
											if (ConstantDataSequential *data =
													dyn_cast<
															ConstantDataSequential>(
															annoteStr->getInitializer())) {
												if (data->isString()) {
													errs() << "Found data "
															<< data->getAsString()
															<< "\n";
													if (data->getAsString()
															== SPM_ANNO) {
														errs()
																<< "data->getAsString() == SPM_ANNO\n";
														pre_annotated_vars.push_back(
																array_ptr);
													}
												}
											}
										}
									}
								}
							}
						}
					}
//					else if (AllocaInst *allocaInst = dyn_cast<AllocaInst>(
//							&inst)) {
//						//Value *array_ptr = allocaInst;
//						errs() << "allocaIns_op->getName() :"
//								<< allocaInst->getName() << "\n";
//						std::string Result;
//						Result = "allocaIns_op->getType() ";
//						raw_string_ostream OS(Result);
//						allocaInst->getType()->print(OS, false, false);
//						errs() << OS.str() << "\n";
//						alloca_vars.push_back(allocaInst);
//					}
				}
			}
		}
		//Pre_annotated_vars
		// Declaring iterator to a vector
		// Displaying vector elements using begin() and end()
		errs() << "The vector elements are : \n";
		//Instead of auto, you can change it to Value* const&
		for (auto const &i : pre_annotated_vars) {
			errs() << i->getName() << "\n";
		}
		//Match the alloca vars with their annotated vars
		for (Function &fn : M) {
			for (BasicBlock &bb : fn) {
				for (Instruction &inst : bb) {
					if (BitCastInst *bitCastInst = dyn_cast<BitCastInst>(
							&inst)) {
						Value *array_ptr = bitCastInst->getOperand(0);
						errs() << "Bitcast instruction: " << *bitCastInst
								<< "\n";
						errs() << "Looking for " << bitCastInst->getName()
								<< "\n";

						std::vector<Value*>::iterator it;
						it = std::find(pre_annotated_vars.begin(),
								pre_annotated_vars.end(), bitCastInst);
						if (it != pre_annotated_vars.end()) {
							errs() << "Found at " << *it << "\n";
							true_annotated_vars.push_back(array_ptr);

						} else {
							errs() << "Not found\n";
						}

						errs() << "bitCastInstt_op->getName() :"
								<< array_ptr->getName() << "\n";
						std::string Result;
						Result = "bitCastInstt_op->getType() ";
						raw_string_ostream OS(Result);
						array_ptr->getType()->print(OS, false, false);
						errs() << OS.str() << "\n";

					}

				}
			}
		}
		errs() << "True annotated variables:\n";
		for (auto const &i : true_annotated_vars) {
			errs() << i->getName() << "\n";
		}

		//Get GEPS for annotated variables
		for (Function &fn : M) {
			for (BasicBlock &bb : fn) {
				for (Instruction &inst : bb) {
					if (GetElementPtrInst *getElementPtrInst = dyn_cast<
							GetElementPtrInst>(&inst)) {
						Value *ptrOperand =
								getElementPtrInst->getPointerOperand();
						errs() << "Ptr operand is " << ptrOperand->getName()
								<< "\n";
						std::vector<Value*>::iterator it;
						it = std::find(true_annotated_vars.begin(),
								true_annotated_vars.end(), ptrOperand);
						if (it != true_annotated_vars.end()) {
							errs() << "Found at " << *it << "\n";
							true_annotated_geps.insert(
									std::pair<Value*, Value*>(getElementPtrInst,
											ptrOperand));
						} else {
							errs() << "GEP Not found\n";
						}
					}
				}
			}
		}

		//Loops
		std::vector<SpmInfo> spmInfoList;
		for (Function &fn : M) {
			//LoopInfo gives error for declaration-only functions
			if (fn.isDeclaration()) {
				continue;
			}
			int loopCounter = 0;
			LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>(fn).getLoopInfo();
			//TODO will use ScalarEvolution for smart spm instruction injections
			ScalarEvolution &se =
					getAnalysis<ScalarEvolutionWrapperPass>(fn).getSE();

			//We only need to traverse on top level loops
			int loopNo = 0;
			for (LoopInfo::iterator i = LI.begin(), e = LI.end(); i != e; ++i) {
				Loop *L = *i;
				int bbCounter = 0;
				bool needMemspm = false;
				loopCounter++;
				errs() << "Loop ";
				errs() << loopCounter;
				errs() << ": Blocks = \n";
				spmInfoList.push_back(SpmInfo());

				for (Loop::block_iterator bb = L->block_begin();
						bb != L->block_end(); ++bb) {
					BasicBlock *cur_block = *bb;
//					errs() << cur_block->getName() << "\n";
					bbCounter += 1;
					for (Instruction &inst : *cur_block) {
						if (LoadInst *load_inst = dyn_cast<LoadInst>(&inst)) {
							Value *addr = load_inst->getPointerOperand();
							errs() << "Pointer operand is " << addr->getName()
									<< "\n";
							std::map<Value*, Value*>::iterator it;
							it = true_annotated_geps.find(addr);
							if (it != true_annotated_geps.end()) {
								errs() << "Found at pairs";
								needMemspm = true;
								spmInfoList[loopNo].loadStack.push(load_inst);
								spmInfoList[loopNo].neededArrays.insert(
										it->second);
								//loadStack.push(load_inst);
							} else {
								errs() << "Not found\n";
							}
						}
					}
				}

				if (needMemspm) {
					BasicBlock *predecessor = L->getLoopPredecessor();
					spmInfoList[loopNo].memspmLocation = predecessor;
					//memspmStack.push(predecessor);
				}
				needMemspm = false;
				loopNo++;

				errs() << "Loop ";
				errs() << loopCounter;
				errs() << ": #BBs = ";
				errs() << bbCounter;
				errs() << "\n";

				//countBlocksInLoop(*i, 0);
			}
		}

		int spmInfoCount = 0;
		llvm::Type *i32_type = llvm::IntegerType::getInt32Ty(M.getContext());
		Type *i32_ptr_type = PointerType::getInt32PtrTy(M.getContext());
		for (SpmInfo i : spmInfoList) {
			errs() << "Spm info no : " << spmInfoCount++ << "\n";
			errs() << "LoadStack: \n";
			while (!i.loadStack.empty()) {
				LoadInst *I = cast<LoadInst>(i.loadStack.top());
				errs() << *I << "\n";
				BasicBlock::iterator ii(I);
				std::string Result;
				Result = "I->getPointerOperand() ";
				raw_string_ostream OS(Result);
				I->getPointerOperand()->getType()->print(OS, false, false);
				errs() << OS.str() << "\n";

				Value *spm_args[] = { I->getPointerOperand(), ConstantInt::get(
						i32_type, 0/*value*/, true) };
				CallInst *call_inst = CallInst::Create(spmreg_intrinsic,
						spm_args);
				ReplaceInstWithInst(I->getParent()->getInstList(), ii,
						call_inst);

				modified = true;
				i.loadStack.pop();
			}
			errs() << "memspm Locations Stack: \n";
			BasicBlock *BB = i.memspmLocation;
			if (BB) {
				errs() << "needed arrays: \n";
				std::set<Value*>::iterator it;
				for (it = i.neededArrays.begin(); it != i.neededArrays.end();
						++it) {
					Value *array_ptr = *it;
					errs() << array_ptr->getName() << "\n";
					std::string Result;
					Result = "Value has type ";
					raw_string_ostream OS(Result);
					array_ptr->getType()->print(OS, false, false);
					errs() << OS.str() << "\n";
					bool canBeNull = false;
					unsigned long int offsetBytes =
							array_ptr->getPointerDereferenceableBytes(
									M.getDataLayout(), canBeNull);

					errs() << BB->getName() << "\n";

					IRBuilder<> Builder(BB);
					Instruction *branch_inst = BB->getTerminator();
					errs() << "TERMINATOR INST " << *branch_inst << "\n";

					Builder.SetInsertPoint(branch_inst);
					Value *InterValue = Builder.CreateAdd(
							ConstantInt::get(i32_type, offsetBytes/*value*/,
									true),
							ConstantInt::get(i32_type, 976/*value*/, true));
					Value *NewValue = Builder.CreateAdd(InterValue,
							ConstantInt::get(i32_type, 4531/*value*/, true));

//					Value *i32ptr = Builder.CreateConstInBoundsGEP1_32(
//							array_ptr->getType(), array_ptr, 0);
					Value *indexList[2] = { ConstantInt::get(i32_type,
							0/*value*/, true), ConstantInt::get(i32_type,
							0/*value*/, true) };
					Value *i32ptr = Builder.CreateInBoundsGEP(array_ptr,indexList);

					Result = "i32ptr has type ";
					i32ptr->getType()->print(OS, false, false);
					errs() << OS.str() << "\n";

//					Value *i32ptr = Builder.CreateGEP(i32_ptr_type,array_ptr,"olumnue");
//					Builder.CreateGEP()

					if (i32ptr) {
						errs() << "YES IT Is";
					}
					//Builder.CreateCall(me)

					Value *args[] = { i32ptr, ConstantInt::get(i32_type,
							offsetBytes/*value*/, true) };
					Builder.CreateCall(memspm_intrinsic,args);

//					CallInst *call_inst = CallInst::Create(memspm_intrinsic,
//							args);
//					BB->getInstList().push_back(call_inst);
				}

			}
		}

		//TODO gloval variables Annotations
//		auto global_annos = M.getNamedGlobal("llvm.global.annotations");
//		if (global_annos) {
//			auto a = cast<ConstantArray>(global_annos->getOperand(0));
//			for (unsigned int i = 0; i < a->getNumOperands(); i++) {
//				auto e = cast<ConstantStruct>(a->getOperand(i));
//				auto anno =
//						cast<ConstantDataArray>(
//								cast<GlobalVariable>(
//										e->getOperand(1)->getOperand(0))->getOperand(
//										0))->getAsCString();
//				errs() << "anno = " << anno << "\n";
//				Value *anno_operand = e->getOperand(0)->getOperand(0);
//				if (auto fn = dyn_cast<Function>(
//						e->getOperand(0)->getOperand(0))) {
//					auto anno =
//							cast<ConstantDataArray>(
//									cast<GlobalVariable>(
//											e->getOperand(1)->getOperand(0))->getOperand(
//											0))->getAsCString();
//					fn->addFnAttr(anno); // <-- add function annotation here
//				}
//			}
//		}

//
//		for (Function &fn : M) {
//			errs() << "I saw a function called " << fn.getName() << "!\n";
//			if (fn.hasFnAttribute("ali")) {
//				errs() << fn.getName() << " has my attribute!\n";
//			}
//		}

//		std::stack<Instruction*> workList; //Instructions to be deleted
//		std::stack<Instruction*> allocaStack;
//
//		for (Function &fn : M) {
//			errs() << "I saw a function called " << fn.getName() << "!\n";
//			for (BasicBlock &bb : fn) {
//				errs() << fn.getName() << "'s basic block: " << bb.getName()
//						<< "!\n";
//				for (Instruction &inst : bb) {
//					errs() << inst << "\n";
////					AllocaInst *casted_inst = dyn_cast<AllocaInst>(&inst);
////					if (casted_inst) {
////						errs() << "Casted instruction is Alloca" << "!\n";
////						errs() << "casted_inst->getOperand(0)->getName() : "
////								<< casted_inst->getOperand(0)->getName()
////								<< "\n";
////					}
//					std::string Result;
//					Result = "Instruction has type ";
//					raw_string_ostream OS(Result);
//					inst.getType()->print(OS, false, false);
//					errs() << OS.str() << "\n";
//
//					StoreInst *casted_inst2 = dyn_cast<StoreInst>(&inst);
//					if (casted_inst2) {
//						errs() << "Casted instruction is Store" << "!\n";
//						workList.push(casted_inst2);
//					}
////					LoadInst *casted_inst3 = dyn_cast<LoadInst>(&inst);
////					if (casted_inst3) {
////						errs() << "Casted instruction is Load" << "!\n";
////						errs() << "casted_inst->getOperand(0)->getName() : "
////								<< casted_inst3->getOperand(0)->getName()
////								<< "\n";
////					}
//
//					BinaryOperator *binary_op_inst = dyn_cast<BinaryOperator>(
//							&inst);
//					if (binary_op_inst) {
//						errs() << "we have a binary op case \n";
//						//workList.push(binary_op_inst);
//
//						//modified = true;
//
//					}
//				}
//			}
//		}
//
//		//Delete Instructions
////		int count = 0;
////		while (!workList.empty()) {
////			count++;
////			Instruction *I = workList.top();
////			I->eraseFromParent();
////			workList.pop();
////			errs() << count << "\n";
////			modified = true;
////		}
//		errs() << "\nLet the transformation began........\n\n";
//
//		while (!workList.empty()) {
//			Instruction *I = workList.top();
//			IRBuilder<> builder(I->getNextNode());
//			llvm::Type *i32_type = llvm::IntegerType::getInt32Ty(
//					M.getContext());
//
//			// Create an instruction representing (a + ~b) + 1
////			Value *InterValue = builder.CreateAdd(I->getOperand(0),
////					builder.CreateNot(I->getOperand(0)));
////
////
////			llvm::Constant *i32_val = llvm::ConstantInt::get(i32_type,
////					1/*value*/, true);
////			Value *NewValue = builder.CreateAdd(InterValue, i32_val);
//
//			Value *spm_args[] = { I->getOperand(1), I->getOperand(0) };
//			builder.CreateCall(memspm_intrinsic, spm_args);
//
////			auto *A = builder.CreateAlloca(i32_type, nullptr, "a");
////			builder.CreateStore(NewValue, A, /*isVolatile=*/false);
////
////			builder.CreateCall(dummy_func);
////			Value *args[] = { I->getOperand(0), I->getOperand(1)};
////			builder.CreateCall(memspm_func, args);
//
////			//Prefetch Call
////			Value *prefetch_args[] = {I->getOperand(1), ConstantInt::get(i32_type,1),ConstantInt::get(i32_type,0), ConstantInt::get(i32_type,1) };
////			builder.CreateCall(prefetch_intrinsic, prefetch_args);
////			//ReplaceInstWithInst(I, NewValue);
////
////			//Sin call
////			Value *sin_args [] = {ConstantFP::get(Type::getFloatTy(M.getContext()),1.45) };
////			builder.CreateCall(another_intrinsic,sin_args);
//
//			workList.pop();
//			modified = true;
//		}

		return modified;
	}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
		//AU.setPreservesCFG();
		AU.addRequired<LoopInfoWrapperPass>();
		AU.addRequired<ScalarEvolutionWrapperPass>();
	}
}
;
}

char SkeletonPass::ID = 0;
/*
 // Automatically enable the pass.
 // http://adriansampson.net/blog/clangpass.html
 static void registerSkeletonPass(const PassManagerBuilder &,
 legacy::PassManagerBase &PM) {
 PM.add(new SkeletonPass());
 }
 static RegisterStandardPasses
 RegisterMyPass(PassManagerBuilder::EP_EarlyAsPossible,
 registerSkeletonPass);
 */
static RegisterPass<SkeletonPass> X("skeleton", "Skeleton Pass", false, false);
