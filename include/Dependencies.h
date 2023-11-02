#ifndef DEPENDENCIES_H_
#define DEPENDENCIES_H_

#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include <set>
#include <deque>
#include <stack>
#include <queue>

struct caller_inst
{
	llvm::Function *function;
	llvm::Instruction * inst;
	std::set<int> indexes = {};
	// bool operator==(const caller_inst& other) const {
    //     return (function == other.function && inst == other.inst && index == other.index && bbl_bfs_index == other.bbl_bfs_index);
    // }
};

using namespace llvm;

void traverseFunctionDepth(Function* function);
std::string Value2str(llvm::Value * val);
std::set<std::string> getOutsetReverse(BasicBlock * bbl, std::set<std::string> inset);
std::set<std::string> getOutset(BasicBlock * bbl, std::set<std::string> inset);
std::set<int> usedArgsinAssert(BasicBlock* bbl);
std::set<BasicBlock*> getBBLwithAssert(Function * func);
void dfsTraversal(llvm::BasicBlock* startBlock, std::set<llvm::BasicBlock*>& visitedBlocks);
void listInstructionsWithCommonOperands(llvm::Instruction* instruction);
void listBasicBlocksBetween( llvm::Function* function, llvm::BasicBlock* startBlock,  llvm::BasicBlock* endBlock);
bool dependsOnArguments(const llvm::Instruction *inst, const llvm::Function *func);
bool canReachFunction(llvm::Function *startFunc, llvm::Function *targetFunc);
bool reachesBBL(llvm::BasicBlock* bbl1, llvm::BasicBlock * bbl2);
void findPaths(llvm::BasicBlock* currentBlock, llvm::BasicBlock* endBlock, std::set<llvm::BasicBlock*>& visitedBlocks, std::vector<llvm::BasicBlock*>& currentPath, std::vector<std::vector<llvm::BasicBlock*>>& allPaths);
std::vector<std::vector<llvm::BasicBlock*>> listPathsBetween(llvm::BasicBlock* startBlock, llvm::BasicBlock* endBlock);
bool hasDFEdge(llvm::BasicBlock* bbl1, llvm::BasicBlock * bbl2);
std::set<int> affectingArgs(BasicBlock * bbl, std::set<std::string> vars);
std::vector<caller_inst> getCallingFunctions(llvm::Function *targetFunction);
std::set<int> usedArgsinCall(Function * func, Instruction * inst, std::set<int> rel_indexes, bool all) ; // has a dataflow edge from bbl 1 to bbl 2


class Dependencies
{
	public:
		Dependencies();
		~Dependencies();
};


#endif
