#ifndef THREADDETAILS_H_
#define THREADDETAILS_H_

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/InitializePasses.h"
#include "llvm/Analysis/LoopInfo.h" 
#include "llvm/IR/Dominators.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include <deque>
#include <vector>
#include <map>
#include <set>

#define clocksize 25



struct value_details
{
	llvm::Value * value;
	bool is_operator = false;
	const char * opcode_name;
	bool is_predicate = false;
	llvm::CmpInst::Predicate pred;
};

struct uid
{
  llvm::Function* function;
  int bbl_bfs_index = -1;
  int index = -1;
};

struct lockDetails
{
  llvm::Function * function;
  std::map<int, int> lock_unlock = {};
  std::map<int *, int*> lock_unlock_clocks = {};
};


struct invariant
{
	std::deque<value_details> lhs{};
	std::deque<value_details> relation{};
	std::deque<value_details> rhs{};
	bool is_cond_invar = false;
};

struct Trace
{
  std::vector<std::pair<llvm::Value*, uid>> instructions = {}; // Thread id, instruction details  
};


struct globalInvar
{
  int index = -1;
  int bbl_bfs_index = -1;
  std::map<Trace *, std::vector<std::vector<invariant>>> invariants = {};
};

struct path_inst_invariants
{
	std::vector<invariant> invars = {};
	std::vector<std::string> path = {};
	int bbl_bfs_index = -1;
	int inst_count = 0;
};

struct rw_inst_invariants
{
	bool covered_treminal = false;
	std::map<llvm::BasicBlock*, int> exec_diffBBL = {}; // keep track of instructions that are from a different basic block
	std::string type = "x"; // "r" or "w"
	std::vector<invariant> invars = {};
	std::vector<int> missed_inst = {};
	int inst_count = 0; // index of instruction
	bool is_relaxed = false;
	int bbl_bfs_index;
	llvm::Instruction * inst = NULL;
	int index = 0;
	std::vector<int> covered = {};
};


struct bbl_path_invariants
{
	std::vector<std::string> path = {}; // list of predecessor blocks
	// std::vector<BasicBlock*> bbl_list = {}; // details of predecessor bbls
	std::vector<rw_inst_invariants> inst_invars = {};
};

struct localInvar
{
  int index;
  int bbl_bfs_index;
  std::vector<std::vector<invariant>> invariants;
};
struct path_invariants
{
	std::vector<invariant> invars{};
	std::vector<std::string> path{};
};

struct variable
{
	llvm::StringRef name;
	llvm::Type * type;
	llvm::Constant * value;
};


struct global_invariant
{
	bbl_path_invariants path_invar1;
	bbl_path_invariants path_invar2;
	std::vector<invariant> invars = {};
};

void printTrace(Trace * trace);
class ThreadDetails
{
	public:
		ThreadDetails();
		~ThreadDetails();
		int threadId = 0;
		int *timestamp_create = new int[clocksize];
		int *timestamp_join = new int[clocksize];
		llvm::Value * threadIdVar;
		llvm::Value * element_op0;
		llvm::Value * element_op1;
		llvm::Value * element_op2;
		std::set<std::string> activeVars;
		std::vector<llvm::Value*> funcList;
		std::vector<invariant> invarList;
		llvm::Value * currThreadVar;
		llvm::Value * init_func;
		std::string initial_method;
		std::string parent_method;
		std::map<llvm::Value *, std::map<int, int>> lock_unlock_map;
		std::map<std::string, std::string> var_type_map;
		std::pair<llvm::Value*, llvm::Value*> create_join_value;
		std::pair<int, int> create_join_stamp;
		bool joined = false;
		int create_index = -1;
		int join_index = -1;
};


#endif
