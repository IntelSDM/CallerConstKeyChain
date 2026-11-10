#pragma once

#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"

struct CallerConstKeyPass : llvm::PassInfoMixin<CallerConstKeyPass>
{
    llvm::PreservedAnalyses run(llvm::Module& m, llvm::ModuleAnalysisManager&);
};

bool RunCallerConstKey(llvm::Module& m);

extern llvm::cl::opt<bool> CallerConstKeyEnable;