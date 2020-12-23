/*
 * GraphSPMInstInternal.h
 *
 *  Created on: Sep 9, 2020
 *      Author: ali
 */

#ifndef LIB_TRANSFORMS_GRAPHSPMINST_GRAPHSPMINSTINTERNAL_H_
#define LIB_TRANSFORMS_GRAPHSPMINST_GRAPHSPMINSTINTERNAL_H_

#include <stack>
#include <set>
#include <map>
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SetVector.h"

namespace llvm {
class Instruction;
class BasicBlock;
class Value;
class LLVMContext;
class ScalarEvolution;
class Loop;
class DominatorTree;
class LoopInfo;
class SCEV;

static const StringRef SPM_ANNO = StringRef("ali", 4); //For some reasons, annotated string value has length 4
static const StringRef SPM_ANNO3 = StringRef("ali", 3); //For some reasons, annotated string value has length 4

static const StringRef ANNO_RISCV_EDGES = StringRef("riscv_edges", 12); //For some reasons, annotated string value has length plus one of strings
static const StringRef ANNO_RISCV_EDGES_ = StringRef("riscv_edges", 11); //For some reasons, annotated string value has length 4

static const StringRef ANNO_RISCV_OFFSETS = StringRef("riscv_offsets", 14); //For some reasons, annotated string value has length plus one of strings
static const StringRef ANNO_RISCV_OFFSETS_ = StringRef("riscv_offsets", 13); //For some reasons, annotated string value has length 4

static const StringRef ANNO_RISCV_VERSPDATA = StringRef("riscv_versp-data", 17); //For some reasons, annotated string value has length plus one of strings
static const StringRef ANNO_RISCV_VERSPDATA_ = StringRef("riscv_versp-data", 16); //For some reasons, annotated string value has length 4

static const StringRef ANNO_RISCV_VERSPDATA_SIZE = StringRef("riscv_versp_data_size",22);
static const StringRef ANNO_RISCV_OFFSETS_SIZE = StringRef("riscv_offsets_size",19);

static const StringRef ANNO_RISCV_MEMSPM = StringRef("riscv_memspm", 13);
static const StringRef ANNO_RISCV_DELSPM = StringRef("riscv_spmdel", 13);

static const int SPM_REG_SPECIAL_VALUE = 0xF0F0F0F0;

struct SpmInfo {
	std::stack<Instruction*> loadStack; //Loads to be replaced with spmreg
	BasicBlock *memspmLocation; //Basic Blocks to insert memspm instructions
	std::set<Value*> neededArrays;
};

class SPMDELInfo {

public:
	Loop &outerMostLoop;
	ScalarEvolution &SE;
	LoopInfo &LI;
	DominatorTree &DT;
	SmallSet<Loop*, 4> innerLoops;
	SPMDELInfo(Loop &outerMostLoop, ScalarEvolution &SE, LoopInfo &LI,
			DominatorTree &DT, SmallSet<Loop*, 4> &innerLoops) :
			outerMostLoop(outerMostLoop), SE(SE), LI(LI), DT(DT), innerLoops(
					innerLoops) {
	}
};

//Find all values referenced in SCEVUnknowns.
class SCEVFindValues {
	ScalarEvolution &SE;
	SetVector<Value*> &Values;

public:
	SCEVFindValues(ScalarEvolution &SE, SetVector<Value*> &Values) :
			SE(SE), Values(Values) {
	}

	bool follow(const SCEV *S);
	bool isDone() {
		return false;
	}
};



} //End namespace
#endif /* LIB_TRANSFORMS_GRAPHSPMINST_GRAPHSPMINSTINTERNAL_H_ */
