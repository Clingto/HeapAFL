/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   Copyright 2015, 2016 Google Inc. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.

 */

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <typeinfo>

#include <fcntl.h>
#include <sys/ipc.h>//ipc
#include <sys/shm.h>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Constant.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/Support/raw_ostream.h"




using namespace llvm;

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;

      // StringRef getPassName() const override {
      //  return "American Fuzzy Lop Instrumentation";
      // }

  };

}


char AFLCoverage::ID = 0;


bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  //IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  IntegerType *Int64Ty = IntegerType::getInt64Ty(C);
  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }



  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

    /* 添加函数声明，插桩用途 */
  llvm::LLVMContext& context = M.getContext ();
  llvm::IRBuilder<> builder(context); 
  
  
  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  GlobalVariable *AFLPerfPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_perf_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int64Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);


  ConstantInt* PerfMask = ConstantInt::get(Int64Ty, PERF_SIZE-1);

  /* Instrument all the things! */

  int inst_blocks = 0;

  for (auto &F : M){
    Function::iterator B_iter = F.begin(); 
    for (auto &BB : F) {

      BasicBlock* BBptr = &*B_iter; //BB的指针
      ++B_iter;

      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      if (AFL_R(100) >= inst_ratio) continue;

      /* Make up cur_loc */

      unsigned int cur_loc = AFL_R(MAP_SIZE);
         

      ConstantInt *CurLoc = ConstantInt::get(Int64Ty, cur_loc);

      /* Load prev_loc */

      LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
      PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt64Ty());

      /* Load SHM pointer */

      LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
      MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *MapPtrIdx =
          IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

      /* Update bitmap */

      LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
      Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Set prev_loc to cur_loc >> 1 */

      StoreInst *Store =
          IRB.CreateStore(ConstantInt::get(Int64Ty, cur_loc >> 1), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));


      int insetMallocFlag = 0;
      Value *tmpMallocInst;
      Value *tmpMallocSizeInst;

      int insetCallocFlag = 0;
      Value *tmpCallocInst;
      Value *tmpCallocSizeInst;
      Value *tmpCallocSizeInst2;

      int insetReallocFlag = 0;
      Value *tmpReallocInst;
      Value *tmpReallocp;
      Value *tmpReallocSizeInst;    

      for(BasicBlock::iterator i = BB.begin(), i2 = BB.end(); i!=i2; i++) {

        IRBuilder<> MemFuzzBuilder(&(*i)); //插桩的位置

        if(Instruction *inst = dyn_cast<Instruction>(i)) {
          
          //在call指令中搜索
          if(inst->getOpcode() == Instruction::Call) {
           
            //malloc函数，插后方
            std::string instr_malloc1 = "malloc";
            //std::string instr_malloc2 = "xmalloc";
            std::string instr_malloc3 = "valloc";
            std::string instr_malloc4 = "safe_malloc";
            std::string instr_malloc5 = "safemalloc";
            std::string instr_malloc6 = "safexmalloc";
            if(inst->getNumOperands() >= 2 ){ //操作数大于二
              if ( instr_malloc1 == std::string(inst->getOperand(1)->getName()) || 
              /*instr_malloc2 == std::string(inst->getOperand(1)->getName()) || */
              instr_malloc3 == std::string(inst->getOperand(1)->getName()) || 
              instr_malloc4 == std::string(inst->getOperand(1)->getName()) || 
              instr_malloc5 == std::string(inst->getOperand(1)->getName()) || 
              instr_malloc6 == std::string(inst->getOperand(1)->getName()) ) {
                //此处不插，判断返回值后再插
                insetMallocFlag = 1;
                tmpMallocInst = inst;
                tmpMallocSizeInst = inst->getOperand(0);

                /* Load SHM pointer */
                LoadInst *PerfPtr = MemFuzzBuilder.CreateLoad(AFLPerfPtr);
                PerfPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
                Value *MapPerfPtrIdx =
                    MemFuzzBuilder.CreateGEP(PerfPtr, MemFuzzBuilder.CreateAnd(tmpMallocSizeInst, PerfMask));

                /* Update perfmap */
                LoadInst *PerfCounter = MemFuzzBuilder.CreateLoad(MapPerfPtrIdx);
                PerfCounter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
                Value *PerfIncr = MemFuzzBuilder.CreateAdd(PerfCounter, ConstantInt::get(Int8Ty, 1));
                MemFuzzBuilder.CreateStore(PerfIncr, MapPerfPtrIdx)
                    ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));             
              }

            }

            //calloc函数，插后方
            std::string instr_calloc1 = "calloc";
            //std::string instr_calloc2 = "xcalloc";
            std::string instr_calloc3 = "memalign";
            std::string instr_calloc4 = "aligned_alloc";
            std::string instr_calloc5 = "safe_calloc";
            std::string instr_calloc6 = "safecalloc";
            std::string instr_calloc7 = "safexcalloc";
            if(inst->getNumOperands() >= 3 ){ //操作数大于二
              if ( instr_calloc1 == std::string(inst->getOperand(2)->getName()) || 
              /*instr_calloc2 == std::string(inst->getOperand(2)->getName()) || */
              instr_calloc3 == std::string(inst->getOperand(2)->getName()) ||
              instr_calloc4 == std::string(inst->getOperand(2)->getName()) ||
              instr_calloc5 == std::string(inst->getOperand(2)->getName()) ||
              instr_calloc6 == std::string(inst->getOperand(2)->getName()) ||
              instr_calloc7 == std::string(inst->getOperand(2)->getName()) ){
                //此处不插，判断返回值后再插
                insetCallocFlag = 1;
                tmpCallocInst = inst;
                tmpCallocSizeInst = inst->getOperand(0);
                tmpCallocSizeInst2 = inst->getOperand(1);

                /* Load SHM pointer */
                LoadInst *PerfPtr = MemFuzzBuilder.CreateLoad(AFLPerfPtr);
                PerfPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
                Value *MapPerfPtrIdx =
                    MemFuzzBuilder.CreateGEP(PerfPtr, MemFuzzBuilder.CreateAnd(tmpCallocSizeInst, PerfMask));

                /* Update perfmap */
                LoadInst *PerfCounter = MemFuzzBuilder.CreateLoad(MapPerfPtrIdx);
                PerfCounter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
                Value *PerfIncr = MemFuzzBuilder.CreateAdd(PerfCounter, ConstantInt::get(Int8Ty, 1));
                MemFuzzBuilder.CreateStore(PerfIncr, MapPerfPtrIdx)
                    ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));  
              }
            }

            //realloc函数，插后方,前方插了Ahead
            std::string instr_realloc1 = "realloc"; 
            if(inst->getNumOperands() >= 3 ){ //操作数大于二
              if ( instr_realloc1 == std::string(inst->getOperand(2)->getName()) ){
                //outs() << "realloc: Heap memory reallocation. " << "(In Function: " << F.getName() << ")\n";
                

                //插桩后方
                insetReallocFlag = 1;
                tmpReallocInst = inst;
                tmpReallocp = inst->getOperand(0);
                tmpReallocSizeInst = inst->getOperand(1);

                /* Load SHM pointer */
                LoadInst *PerfPtr = MemFuzzBuilder.CreateLoad(AFLPerfPtr);
                PerfPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
                Value *MapPerfPtrIdx =
                    MemFuzzBuilder.CreateGEP(PerfPtr, MemFuzzBuilder.CreateAnd(tmpReallocSizeInst, PerfMask));

                /* Update perfmap */
                LoadInst *PerfCounter = MemFuzzBuilder.CreateLoad(MapPerfPtrIdx);
                PerfCounter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
                Value *PerfIncr = MemFuzzBuilder.CreateAdd(PerfCounter, ConstantInt::get(Int8Ty, 1));
                MemFuzzBuilder.CreateStore(PerfIncr, MapPerfPtrIdx)
                    ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));  				
              }
            }

            //new函数, 插后方
            std::string instr_new1 = "_Znwm";
            std::string instr_new2 = "_Znam";
            std::string instr_new3 = "_Znaj";
            std::string instr_new4 = "_Znwj";
            if(inst->getNumOperands() >= 2 )
            { //操作数大于二
              if ( instr_new1 == std::string(inst->getOperand(1)->getName()) || instr_new2 == std::string(inst->getOperand(1)->getName()) || instr_new3 == std::string(inst->getOperand(1)->getName()) || instr_new4 == std::string(inst->getOperand(1)->getName()) )
              {
                insetMallocFlag = 1;
                tmpMallocInst = inst;
                tmpMallocSizeInst = inst->getOperand(0);

                /* Load SHM pointer */
                LoadInst *PerfPtr = MemFuzzBuilder.CreateLoad(AFLPerfPtr);
                PerfPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
                Value *MapPerfPtrIdx =
                    MemFuzzBuilder.CreateGEP(PerfPtr, MemFuzzBuilder.CreateAnd(tmpMallocSizeInst, PerfMask));

                /* Update perfmap */
                LoadInst *PerfCounter = MemFuzzBuilder.CreateLoad(MapPerfPtrIdx);
                PerfCounter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
                Value *PerfIncr = MemFuzzBuilder.CreateAdd(PerfCounter, ConstantInt::get(Int8Ty, 1));
                MemFuzzBuilder.CreateStore(PerfIncr, MapPerfPtrIdx)
                    ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));  
            }
          }
          }
          //针对有些new在invoke指令中搜索
          if(inst->getOpcode() == Instruction::Invoke) {
            std::string instr_malloc1 = "malloc";
            std::string instr_new1 = "_Znwm";
            std::string instr_new2 = "_Znam";
            std::string instr_new3 = "_Znaj";
            std::string instr_new4 = "_Znwj";
            if(inst->getNumOperands() >= 2 ){ //操作数大于二
              if (instr_malloc1 == std::string(inst->getOperand(1)->getName()) || instr_new1 == std::string(inst->getOperand(1)->getName()) || instr_new2 == std::string(inst->getOperand(1)->getName()) || instr_new3 == std::string(inst->getOperand(1)->getName()) || instr_new4 == std::string(inst->getOperand(1)->getName()) ){
                //outs() << "new: Heap memory allocation. " << "(In Function: " << F.getName() << ")\n";          
                insetMallocFlag = 1;
                tmpMallocInst = inst;
                tmpMallocSizeInst = inst->getOperand(0);
                i++;
                if (i == BB.end()){
                  BasicBlock *succ_BBptr = BBptr->getTerminator()->getSuccessor(0);//后继
                  BasicBlock::iterator succ_i = succ_BBptr->begin();
                  IRBuilder<> TmpBuilder(&*succ_i); //插桩的位置,invoke跳转的BLock
                  insetMallocFlag = 0;

                }
                i--;

                /* Load SHM pointer */
                LoadInst *PerfPtr = MemFuzzBuilder.CreateLoad(AFLPerfPtr);
                PerfPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
                Value *MapPerfPtrIdx =
                    MemFuzzBuilder.CreateGEP(PerfPtr, MemFuzzBuilder.CreateAnd(tmpMallocSizeInst, PerfMask));

                /* Update perfmap */
                LoadInst *PerfCounter = MemFuzzBuilder.CreateLoad(MapPerfPtrIdx);
                PerfCounter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
                Value *PerfIncr = MemFuzzBuilder.CreateAdd(PerfCounter, ConstantInt::get(Int8Ty, 1));
                MemFuzzBuilder.CreateStore(PerfIncr, MapPerfPtrIdx)
                    ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));  						
              }
            }
          }

        }
      }

      inst_blocks++;

    }
  }
  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

  }

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

}


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_OptimizerLast, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
