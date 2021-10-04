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
		Module &M, Function *spmcon_intrinsic);


static bool insertSPMDEL(std::map<StringRef, AllocaInst*> &spmcon_locations,
		LLVMContext &llvmContext, Value *edgeArray, Function *delspm_intrinsic);

static void findAnnotatedVariables(Module &M,
		std::map<Value*, StringRef> &annotated_vars_map,
		SmallVector<Instruction*, 4> &annotationCalls);

static void functionAnnotattions(Module &M);

static Loop* outermostLoopForSpmHelper(Loop *L, Instruction *edgeArray,
		std::map<Instruction*, Loop*> *loadLoopMap);

static void outermostLoopForSpm(Loop *L, ScalarEvolution *SE, LoopInfo *LI,
		DominatorTree *DT, Instruction *edgeArray,
		std::vector<Instruction*> &spmRegLocations,
		std::map<Instruction*, Loop*> &loadLoopMap,
		SmallSet<SPMDELInfo*, 4> &spmDelInfos);

static bool insertSPMREG(LoadInst *I, Loop *L, LLVMContext &llvmContext,
		LoopInfo &LI, DominatorTree &DT, Function *spmreg_intrinsic);

static bool insertMEMSPM(std::map<StringRef, AllocaInst*> &spmcon_locations,
		LLVMContext &llvmContext, Value *vertexArray,
		Function *memspm_intrinsic);

static Value* insertGEP(AllocaInst *inst, Value *IndexValue,
		Instruction *insertionPoint, LLVMContext &llvmContext);


//===----------------------------------------------------------------------===//
//Static Function Implementations
//

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

		Value *bitCasted = Builder.CreateBitCast(prei32Ptr,
				Type::getInt32PtrTy(llvmContext, 0));

		return Builder.CreateGEP(bitCasted, indexList);
	}
	return nullptr;
}

static bool insertSPMCON(std::map<StringRef, AllocaInst*> &spmcon_locations,
		Module &M, Function *spmcon_intrinsic) {
	bool modified = false;
	llvm::Type *i32_type = llvm::IntegerType::getInt32Ty(M.getContext());
	std::map<StringRef, AllocaInst*>::iterator it;

	//Inserting the first spmcon, for the edge data address
	it = spmcon_locations.find(ANNO_RISCV_EDGES);
	if (it != spmcon_locations.end()) {
		DEBUG_WITH_TYPE("annotation",
				dbgs() << "SPMCON: Found at " << it->second->getName() << " - "
						<< it->first << "\n");
		Value *i32ptr = insertGEP(it->second,
				ConstantInt::get(i32_type, 0/*value*/, true),
				it->second->getParent()->getTerminator(), M.getContext());
		assert(i32ptr && "No pointer to the edges of the graph");
		errs() << "i32ptr is " << *i32ptr << "\n";
		Value *args[] = { i32ptr, ConstantInt::get(i32_type, 0/*value*/, true) };
		IRBuilder<> Builder(cast<Instruction>(i32ptr)->getNextNode());
		Builder.CreateCall(spmcon_intrinsic, args);
		modified = true;
	}

	//Inserting the second and third spmcons, for graph data and size of graph data
	it = spmcon_locations.find(ANNO_RISCV_VERSPDATA);
	if (it != spmcon_locations.end()) {
		DEBUG_WITH_TYPE("annotation",
				dbgs() << "SPMCON: Found at " << it->second->getName() << " - "
						<< it->first << "\n");
		Value *i32ptr = insertGEP(it->second,
				ConstantInt::get(i32_type, 0/*value*/, true),
				it->second->getParent()->getTerminator(), M.getContext());
		assert(i32ptr && "No pointer to the versp data of the graph");

		IRBuilder<> Builder(it->second->getParent()->getTerminator());
		Value *args[] = { i32ptr, ConstantInt::get(i32_type, 0/*value*/, true) };

		//Address of graph data
		Builder.CreateCall(spmcon_intrinsic, args);

		//Inserting the spmcon for the size of graph data
		DEBUG_WITH_TYPE("annotation",
				dbgs() << "Allocated type is"
						<< *(dyn_cast<PointerType>(
								it->second->getAllocatedType())->getElementType())
						<< "\n");

		//Imitating the sizeof operator, refer to https://stackoverflow.com/questions/14608250/how-can-i-find-the-size-of-a-type
		Value *graphDataSize =
				Builder.CreateGEP(
						dyn_cast<PointerType>(it->second->getAllocatedType())->getElementType(),
						ConstantPointerNull::get(
								dyn_cast<PointerType>(
										it->second->getAllocatedType())),
						ConstantInt::get(i32_type, 1/*value*/, true));

		Value *byteSize = Builder.CreatePtrToInt(graphDataSize,
				llvm::IntegerType::getInt32Ty(M.getContext()));

		//Value *bitCasted = Builder.CreateBitCast(byteSize, Type::getInt32PtrTy(M.getContext(), 0));
		Value *byteSizePotr = Builder.CreateIntToPtr(byteSize,
				Type::getInt32PtrTy(M.getContext(), 0));

		args[0] = byteSizePotr;
		Builder.CreateCall(spmcon_intrinsic, args);

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
	IRBuilder<> Builder(I);
	Value *spm_args[] = { I->getPointerOperand(), ConstantInt::get(i32_type,
			0/*value*/, true) };
	CallInst *call_inst = Builder.CreateCall(spmreg_intrinsic, spm_args,
			"valueFromSpm");

	I->replaceAllUsesWith(call_inst);
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
			//dumpLoopBounds(it.second, *SE);
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

	modified |= insertSPMCON(spmcon_locations, M, spmcon_intrinsic);

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
