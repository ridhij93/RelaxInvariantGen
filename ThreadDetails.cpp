#include "ThreadDetails.h"

ThreadDetails::ThreadDetails()
{
	initial_method = "";
	parent_method = "";
	
}



void printTrace(Trace * trace)
{
	llvm::errs() << "TRACE TRACE TRACE TRACE TRACE TRACE TRACE TRACE TRACE TRACE TRACE TRACE TRACE TRACE TRACE TRACE TRACE TRACE \n";
	for (auto instruction : trace->instructions)
		llvm::errs() << *(instruction.first) << " -- "<< instruction.second.function->getName() << " -- " << instruction.second.index << " -- " << instruction.second.bbl_bfs_index <<"\n" ;
	llvm::errs() << "----------------------------------------------------------------------------------------------------------\n";	
}