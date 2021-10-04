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

static const StringRef ANNO_RISCV_EDGES = StringRef("riscv_edges", 12); //For some reasons, annotated string value has length plus one of strings

static const StringRef ANNO_RISCV_OFFSETS = StringRef("riscv_offsets", 14); //For some reasons, annotated string value has length plus one of strings

static const StringRef ANNO_RISCV_VERSPDATA = StringRef("riscv_versp-data", 17); //For some reasons, annotated string value has length plus one of strings

static const StringRef ANNO_RISCV_MEMSPM = StringRef("riscv_memspm", 13);
static const StringRef ANNO_RISCV_DELSPM = StringRef("riscv_spmdel", 13);

static const int SPM_REG_SPECIAL_VALUE = 0xF0F0F0F0;

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
