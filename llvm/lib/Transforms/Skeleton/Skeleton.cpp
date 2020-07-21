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
#include <stack>
#include <vector>
#include <algorithm>
#include <string>

using namespace llvm;

namespace {
struct SkeletonPass: public ModulePass {
	static char ID;
	SkeletonPass() :
			ModulePass(ID) {
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
		errs() << "True annotated variables: \n";
		for (auto const &i : true_annotated_vars) {
			errs() << i->getName() << "\n";
		}

		//Annotations
		auto global_annos = M.getNamedGlobal("llvm.global.annotations");
		if (global_annos) {
			auto a = cast<ConstantArray>(global_annos->getOperand(0));
			errs() << "a->getNumOperands() = " << a->getNumOperands() << "\n";
			for (int i = 0; i < a->getNumOperands(); i++) {
				auto e = cast<ConstantStruct>(a->getOperand(i));
				errs() << "e->NumUserOperands = " << e->getNumOperands()
						<< "\n";
				auto anno =
						cast<ConstantDataArray>(
								cast<GlobalVariable>(
										e->getOperand(1)->getOperand(0))->getOperand(
										0))->getAsCString();
				errs() << "anno = " << anno << "\n";
				Value *anno_operand = e->getOperand(0)->getOperand(0);
				errs() << "anno_operand(0)->getName() = "
						<< anno_operand->getName() << "\n";

				if (auto fn = dyn_cast<Function>(
						e->getOperand(0)->getOperand(0))) {
					auto anno =
							cast<ConstantDataArray>(
									cast<GlobalVariable>(
											e->getOperand(1)->getOperand(0))->getOperand(
											0))->getAsCString();
					fn->addFnAttr(anno); // <-- add function annotation here
				}
			}
		}

		for (auto &global_var : M.getGlobalList()) {
			errs() << "global_var.getName() = " << global_var.getName()
					<< " \n";
			errs() << "global_var.getValueName()->getValue() = "
					<< global_var.getValueName()->getValue() << "\n";
			errs() << "global_var.getValueName() = "
					<< global_var.getValueName() << "\n";
		}

		auto global_vars = M.getNamedGlobal("");
		if (global_vars) {
			auto a = cast<ConstantArray>(global_vars->getOperand(0));
			for (int i = 0; i < a->getNumOperands(); i++) {
				auto e = cast<ConstantStruct>(a->getOperand(i));
				errs() << "e->NumUserOperands = " << e->getName() << "\n";
			}
		} else {
			errs() << "That's not working...\n";
		}

		for (Function &fn : M) {
			errs() << "I saw a function called " << fn.getName() << "!\n";
			if (fn.hasFnAttribute("ali")) {
				errs() << fn.getName() << " has my attribute!\n";
			}
		}

//		std::stack<Instruction*> workList; //Instructions to be deleted
//		for (Function &fn : M) {
//			errs() << "I saw a function called " << fn.getName() << "!\n";
//			for (BasicBlock &bb : fn) {
//				errs() << fn.getName() << "'s basic block: " << bb.getName()
//						<< "!\n";
//				for (Instruction &inst : bb) {
//					errs() << inst << "'\n";
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

		//Delete Instructions
//		int count = 0;
//		while (!workList.empty()) {
//			count++;
//			Instruction *I = workList.top();
//			I->eraseFromParent();
//			workList.pop();
//			errs() << count << "\n";
//			modified = true;
//		}
//		errs() << "\nLet the transformation began........\n\n";
//
//		while (!workList.empty()) {
//			Instruction *I = workList.top();
//			IRBuilder<> builder(I->getNextNode());
//			// Create an instruction representing (a + ~b) + 1
//			Value *InterValue = builder.CreateAdd(I->getOperand(0),
//					builder.CreateNot(I->getOperand(0)));
//
//			llvm::Type *i32_type = llvm::IntegerType::getInt32Ty(
//					M.getContext());
////			llvm::Constant *i32_val = llvm::ConstantInt::get(i32_type,
////					1/*value*/, true);
////			Value *NewValue = builder.CreateAdd(InterValue, i32_val);
//
//			errs() << "The number of operands of the instruction is "
//					<< I->getNumOperands() << "\n";
//
//			std::string Result;
//			Result = "Instruction's type is ";
//			raw_string_ostream OS(Result);
//			I->getType()->print(OS, false, false);
//			errs() << OS.str() << "\n";
//
//			Result = "getOperand(0) type is ";
//			I->getOperand(0)->getType()->print(OS, false, false);
//			errs() << OS.str() << "\n";
//
//			Result = "getOperand(1) type is ";
//			I->getOperand(1)->getType()->print(OS, false, false);
//			errs() << OS.str() << "\n";
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
