#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm//IR/Module.h"

//you may not need all of the following:
#include <vector>
#include <deque>
#include <set>
#include <algorithm>
#include <ostream>
#include <fstream>
#include <iostream>

using namespace llvm;

namespace {

struct LivenessHistogram: public ModulePass {
	static char ID;
	LivenessHistogram() :
			ModulePass(ID) {
	}

	std::vector<unsigned> counts;

	//in the counts histogram, increment category c
	//call once for each program point with c simultaneously live values
	void increment(unsigned c) {
		if (counts.size() <= c)
			counts.resize(c + 1, 0);
		counts[c]++;
	}

	//output the histogram to a file
	void printHistogram(Module &M) {
		std::string name = M.getModuleIdentifier() + ".lhist";
		std::ofstream file(name.c_str());
		for (unsigned i = 0, n = counts.size(); i < n; i++) {
			file << i << ": " << counts[i] << "\n";
		}
	}

	// We don't modify the program, so we preserve all analyses
	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
		AU.setPreservesAll();
	}

	virtual bool runOnFunction(Function &F) {
		//implement this
		return false;
	}

	virtual bool runOnModule(Module &M) {
		std::cerr << "Hello\n"; //remove this
		for (Module::iterator MI = M.begin(), ME = M.end(); MI != ME; ++MI) {
			runOnFunction(*MI);
		}
		printHistogram(M);
		return false;
	}
};
}

char LivenessHistogram::ID = 0;
static RegisterPass<LivenessHistogram> X("liveness-hist", "Liveness Histogram", false, false);
