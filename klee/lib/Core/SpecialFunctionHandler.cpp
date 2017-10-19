//===-- SpecialFunctionHandler.cpp ----------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "Memory.h"
#include "SpecialFunctionHandler.h"
#include "TimingSolver.h"

#include "klee/ExecutionState.h"

#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/Support/Debug.h"
#include "klee/Internal/Support/ErrorHandling.h"

#include "Executor.h"
#include "MemoryManager.h"

#include "klee/CommandLine.h"

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Module.h"
#else
#include "llvm/Module.h"
#endif
#include "llvm/ADT/Twine.h"

#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
#include "llvm/Target/TargetData.h"
#elif LLVM_VERSION_CODE <= LLVM_VERSION(3, 2)
#include "llvm/DataLayout.h"
#else
#include "llvm/IR/DataLayout.h"
#endif

#include "llvm/IR/Constants.h"
#include <errno.h>

using namespace llvm;
using namespace klee;

namespace {
  cl::opt<bool>
  ReadablePosix("readable-posix-inputs",
            cl::init(false),
            cl::desc("Prefer creation of POSIX inputs (command-line arguments, files, etc.) with human readable bytes. "
                     "Note: option is expensive when creating lots of tests (default=false)"));

  cl::opt<bool>
  SilentKleeAssume("silent-klee-assume",
                   cl::init(false),
                   cl::desc("Silently terminate paths with an infeasible "
                            "condition given to klee_assume() rather than "
                            "emitting an error (default=false)"));
}


/// \todo Almost all of the demands in this file should be replaced
/// with terminateState calls.

///



// FIXME: We are more or less committed to requiring an intrinsic
// library these days. We can move some of this stuff there,
// especially things like realloc which have complicated semantics
// w.r.t. forking. Among other things this makes delayed query
// dispatch easier to implement.
static SpecialFunctionHandler::HandlerInfo handlerInfo[] = {
#define add(name, handler, ret) { name, \
                                  &SpecialFunctionHandler::handler, \
                                  false, ret, false }
#define addDNR(name, handler) { name, \
                                &SpecialFunctionHandler::handler, \
                                true, false, false }
  addDNR("__assert_rtn", handleAssertFail),
  addDNR("__assert_fail", handleAssertFail),
  addDNR("_assert", handleAssert),
  addDNR("abort", handleAbort),
  addDNR("_exit", handleExit),
  { "exit", &SpecialFunctionHandler::handleExit, true, false, true },
  addDNR("klee_abort", handleAbort),
  addDNR("klee_silent_exit", handleSilentExit),  
  addDNR("klee_report_error", handleReportError),

  add("calloc", handleCalloc, true),
  add("free", handleFree, false),
  add("klee_assume", handleAssume, false),
  add("klee_check_memory_access", handleCheckMemoryAccess, false),
  add("klee_get_valuef", handleGetValue, true),
  add("klee_get_valued", handleGetValue, true),
  add("klee_get_valuel", handleGetValue, true),
  add("klee_get_valuell", handleGetValue, true),
  /*************************************/
  /* true is for returning a value ... */
  /*************************************/
  add("MyAtoi",                      handleMyAtoi,                      true),
  add("MyIntAssign",                 handleMyIntAssign,                 false),
  add("My_p_assign_NULL",            handleMy_p_assign_NULL,            false),
  add("MyCharAssign",                handleMyCharAssign,                false),
  add("MyConstStringAssign",         handleMyConstStringAssign,         false),
  add("MyWriteCharToStringAtOffset", handleMyWriteCharToStringAtOffset, false),
  add("MyReadCharFromStringAtOffset",handleMyReadCharFromStringAtOffset,false),
  add("MyMalloc",                    handleMyMalloc,                    false),
  add("MyStrcpy",                    handleMyStrcpy,                    false),
  add("MyStrchr",                    handleMyStrchr,                    false),
  add("MyStrcmp",                    handleMyStrcmp,                    true),
  add("MyStrlen",                    handleMyStrlen,                    true),
  add("klee_get_value_i32", handleGetValue, true),
  add("klee_get_value_i64", handleGetValue, true),
  add("klee_define_fixed_object", handleDefineFixedObject, false),
  add("klee_get_obj_size", handleGetObjSize, true),
  add("klee_get_errno", handleGetErrno, true),
  add("klee_is_symbolic", handleIsSymbolic, true),
  add("klee_make_symbolic", handleMakeSymbolic, false),
  add("klee_mark_global", handleMarkGlobal, false),
  add("klee_merge", handleMerge, false),
  add("klee_prefer_cex", handlePreferCex, false),
  add("klee_posix_prefer_cex", handlePosixPreferCex, false),
  add("klee_print_expr", handlePrintExpr, false),
  add("klee_print_range", handlePrintRange, false),
  add("klee_set_forking", handleSetForking, false),
  add("klee_stack_trace", handleStackTrace, false),
  add("klee_warning", handleWarning, false),
  add("klee_warning_once", handleWarningOnce, false),
  add("klee_alias_function", handleAliasFunction, false),
  add("malloc", handleMalloc, true),
  add("realloc", handleRealloc, true),



  // operator delete[](void*)
  add("_ZdaPv", handleDeleteArray, false),
  // operator delete(void*)
  add("_ZdlPv", handleDelete, false),

  // operator new[](unsigned int)
  add("_Znaj", handleNewArray, true),
  // operator new(unsigned int)
  add("_Znwj", handleNew, true),

  // FIXME-64: This is wrong for 64-bit long...

  // operator new[](unsigned long)
  add("_Znam", handleNewArray, true),
  // operator new(unsigned long)
  add("_Znwm", handleNew, true),

  // clang -fsanitize=unsigned-integer-overflow
  add("__ubsan_handle_add_overflow", handleAddOverflow, false),
  add("__ubsan_handle_sub_overflow", handleSubOverflow, false),
  add("__ubsan_handle_mul_overflow", handleMulOverflow, false),
  add("__ubsan_handle_divrem_overflow", handleDivRemOverflow, false),

#undef addDNR
#undef add  
};

SpecialFunctionHandler::const_iterator SpecialFunctionHandler::begin() {
  return SpecialFunctionHandler::const_iterator(handlerInfo);
}

SpecialFunctionHandler::const_iterator SpecialFunctionHandler::end() {
  // NULL pointer is sentinel
  return SpecialFunctionHandler::const_iterator(0);
}

SpecialFunctionHandler::const_iterator& SpecialFunctionHandler::const_iterator::operator++() {
  ++index;
  if ( index >= SpecialFunctionHandler::size())
  {
    // Out of range, return .end()
    base=0; // Sentinel
    index=0;
  }

  return *this;
}

int SpecialFunctionHandler::size() {
	return sizeof(handlerInfo)/sizeof(handlerInfo[0]);
}

SpecialFunctionHandler::SpecialFunctionHandler(Executor &_executor) 
  : executor(_executor) {}


void SpecialFunctionHandler::prepare() {
  unsigned N = size();

  for (unsigned i=0; i<N; ++i) {
    HandlerInfo &hi = handlerInfo[i];
    Function *f = executor.kmodule->module->getFunction(hi.name);
    
    // No need to create if the function doesn't exist, since it cannot
    // be called in that case.
  
    if (f && (!hi.doNotOverride || f->isDeclaration())) {
      // Make sure NoReturn attribute is set, for optimization and
      // coverage counting.
      if (hi.doesNotReturn)
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        f->addFnAttr(Attribute::NoReturn);
#elif LLVM_VERSION_CODE >= LLVM_VERSION(3, 2)
        f->addFnAttr(Attributes::NoReturn);
#else
        f->addFnAttr(Attribute::NoReturn);
#endif

      // Change to a declaration since we handle internally (simplifies
      // module and allows deleting dead code).
      if (!f->isDeclaration())
        f->deleteBody();
    }
  }
}

void SpecialFunctionHandler::bind() {
  unsigned N = sizeof(handlerInfo)/sizeof(handlerInfo[0]);

  for (unsigned i=0; i<N; ++i) {
    HandlerInfo &hi = handlerInfo[i];
    Function *f = executor.kmodule->module->getFunction(hi.name);
    
    if (f && (!hi.doNotOverride || f->isDeclaration()))
      handlers[f] = std::make_pair(hi.handler, hi.hasReturnValue);
  }
}


bool SpecialFunctionHandler::handle(ExecutionState &state, 
                                    Function *f,
                                    KInstruction *target,
                                    std::vector< ref<Expr> > &arguments) {
  handlers_ty::iterator it = handlers.find(f);
  if (it != handlers.end()) {    
    Handler h = it->second.first;
    bool hasReturnValue = it->second.second;
     // FIXME: Check this... add test?
    if (!hasReturnValue && !target->inst->use_empty())
    {
      executor.terminateStateOnExecError(state, 
                                         "expected return value from void special function");
    }
    else
    {
      /*************************************************/
      /* OISH: this is where the malloc effect happens */
      /*************************************************/
      // llvm::errs() << "[OISH] Update malloc effect here" << "\n";
      (this->*h)(state, target, arguments);
    }
    return true;
  } else {
    return false;
  }
}

/****/

// reads a concrete string from memory
std::string 
SpecialFunctionHandler::readStringAtAddress(ExecutionState &state, 
                                            ref<Expr> addressExpr) {
  ObjectPair op;
  addressExpr = executor.toUnique(state, addressExpr);
  ref<ConstantExpr> address = cast<ConstantExpr>(addressExpr);
  if (!state.addressSpace.resolveOne(address, op))
    assert(0 && "XXX out of bounds / multiple resolution unhandled");
  bool res __attribute__ ((unused));
  assert(executor.solver->mustBeTrue(state, 
                                     EqExpr::create(address, 
                                                    op.first->getBaseExpr()),
                                     res) &&
         res &&
         "XXX interior pointer unhandled");
  const MemoryObject *mo = op.first;
  const ObjectState *os = op.second;

  char *buf = new char[mo->size];

  unsigned i;
  for (i = 0; i < mo->size - 1; i++) {
    ref<Expr> cur = os->read8(i);
    cur = executor.toUnique(state, cur);
    assert(isa<ConstantExpr>(cur) && 
           "hit symbolic char while reading concrete string");
    buf[i] = cast<ConstantExpr>(cur)->getZExtValue(8);
  }
  buf[i] = 0;
  
  std::string result(buf);
  delete[] buf;
  return result;
}

/****/

void SpecialFunctionHandler::handleAbort(ExecutionState &state,
                           KInstruction *target,
                           std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==0 && "invalid number of arguments to abort");
  executor.terminateStateOnError(state, "abort failure", Executor::Abort);
}

void SpecialFunctionHandler::handleExit(ExecutionState &state,
                           KInstruction *target,
                           std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 && "invalid number of arguments to exit");
  executor.terminateStateOnExit(state);
}

void SpecialFunctionHandler::handleSilentExit(ExecutionState &state,
                                              KInstruction *target,
                                              std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 && "invalid number of arguments to exit");
  executor.terminateState(state);
}

void SpecialFunctionHandler::handleAliasFunction(ExecutionState &state,
						 KInstruction *target,
						 std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==2 && 
         "invalid number of arguments to klee_alias_function");
  std::string old_fn = readStringAtAddress(state, arguments[0]);
  std::string new_fn = readStringAtAddress(state, arguments[1]);
  KLEE_DEBUG_WITH_TYPE("alias_handling", llvm::errs() << "Replacing " << old_fn
                                           << "() with " << new_fn << "()\n");
  if (old_fn == new_fn)
    state.removeFnAlias(old_fn);
  else state.addFnAlias(old_fn, new_fn);
}

void SpecialFunctionHandler::handleAssert(ExecutionState &state,
                                          KInstruction *target,
                                          std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==3 && "invalid number of arguments to _assert");  
  executor.terminateStateOnError(state,
				 "ASSERTION FAIL: " + readStringAtAddress(state, arguments[0]),
				 Executor::Assert);
}

void SpecialFunctionHandler::handleAssertFail(ExecutionState &state,
                                              KInstruction *target,
                                              std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==4 && "invalid number of arguments to __assert_fail");
  executor.terminateStateOnError(state,
				 "ASSERTION FAIL: " + readStringAtAddress(state, arguments[0]),
				 Executor::Assert);
}

void SpecialFunctionHandler::handleReportError(ExecutionState &state,
                                               KInstruction *target,
                                               std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==4 && "invalid number of arguments to klee_report_error");
  
  // arguments[0], arguments[1] are file, line
  executor.terminateStateOnError(state,
				 readStringAtAddress(state, arguments[2]),
				 Executor::ReportError,
				 readStringAtAddress(state, arguments[3]).c_str());
}

void SpecialFunctionHandler::handleMerge(ExecutionState &state,
                           KInstruction *target,
                           std::vector<ref<Expr> > &arguments) {
  // nop
}

void SpecialFunctionHandler::handleNew(ExecutionState &state,
                         KInstruction *target,
                         std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 && "invalid number of arguments to new");

  executor.executeAlloc(state, arguments[0], false, target);
}

void SpecialFunctionHandler::handleDelete(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  // FIXME: Should check proper pairing with allocation type (malloc/free,
  // new/delete, new[]/delete[]).

  // XXX should type check args
  assert(arguments.size()==1 && "invalid number of arguments to delete");
  executor.executeFree(state, arguments[0]);
}

void SpecialFunctionHandler::handleNewArray(ExecutionState &state,
                              KInstruction *target,
                              std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 && "invalid number of arguments to new[]");
  executor.executeAlloc(state, arguments[0], false, target);
}

void SpecialFunctionHandler::handleDeleteArray(ExecutionState &state,
                                 KInstruction *target,
                                 std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 && "invalid number of arguments to delete[]");
  executor.executeFree(state, arguments[0]);
}

void SpecialFunctionHandler::handleMalloc(ExecutionState &state,
                                  KInstruction *target,
                                  std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 && "invalid number of arguments to malloc");
  // OISH :: MALLOC FROM HERE
  llvm::errs() << "execute alloc from here" << "\n";
  executor.executeAlloc(state, arguments[0], false, target);
}

void SpecialFunctionHandler::handleAssume(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 && "invalid number of arguments to klee_assume");
  
  ref<Expr> e = arguments[0];
  
  if (e->getWidth() != Expr::Bool)
    e = NeExpr::create(e, ConstantExpr::create(0, e->getWidth()));
  
  bool res;
  bool success __attribute__ ((unused)) = executor.solver->mustBeFalse(state, e, res);
  assert(success && "FIXME: Unhandled solver failure");
  if (res) {
    if (SilentKleeAssume) {
      executor.terminateState(state);
    } else {
      executor.terminateStateOnError(state,
                                     "invalid klee_assume call (provably false)",
                                     Executor::User);
    }
  } else {
    executor.addConstraint(state, e);
  }
}

void SpecialFunctionHandler::handleIsSymbolic(ExecutionState &state,
                                KInstruction *target,
                                std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 && "invalid number of arguments to klee_is_symbolic");

  executor.bindLocal(target, state, 
                     ConstantExpr::create(!isa<ConstantExpr>(arguments[0]),
                                          Expr::Int32));
}

void SpecialFunctionHandler::handlePreferCex(ExecutionState &state,
                                             KInstruction *target,
                                             std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_prefex_cex");

  ref<Expr> cond = arguments[1];
  if (cond->getWidth() != Expr::Bool)
    cond = NeExpr::create(cond, ConstantExpr::alloc(0, cond->getWidth()));

  Executor::ExactResolutionList rl;
  executor.resolveExact(state, arguments[0], rl, "prefex_cex");
  
  assert(rl.size() == 1 &&
         "prefer_cex target must resolve to precisely one object");

  rl[0].first.first->cexPreferences.push_back(cond);
}

void SpecialFunctionHandler::handlePosixPreferCex(ExecutionState &state,
                                             KInstruction *target,
                                             std::vector<ref<Expr> > &arguments) {
  if (ReadablePosix)
    return handlePreferCex(state, target, arguments);
}

void SpecialFunctionHandler::handlePrintExpr(ExecutionState &state,
                                  KInstruction *target,
                                  std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_print_expr");

  std::string msg_str = readStringAtAddress(state, arguments[0]);
  llvm::errs() << msg_str << ":" << arguments[1] << "\n";
}

void SpecialFunctionHandler::handleSetForking(ExecutionState &state,
                                              KInstruction *target,
                                              std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_set_forking");
  ref<Expr> value = executor.toUnique(state, arguments[0]);
  
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(value)) {
    state.forkDisabled = CE->isZero();
  } else {
    executor.terminateStateOnError(state, 
                                   "klee_set_forking requires a constant arg",
                                   Executor::User);
  }
}

void SpecialFunctionHandler::handleStackTrace(ExecutionState &state,
                                              KInstruction *target,
                                              std::vector<ref<Expr> > &arguments) {
  state.dumpStack(outs());
}

void SpecialFunctionHandler::handleWarning(ExecutionState &state,
                                           KInstruction *target,
                                           std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 && "invalid number of arguments to klee_warning");

  std::string msg_str = readStringAtAddress(state, arguments[0]);
  klee_warning("%s: %s", state.stack.back().kf->function->getName().data(), 
               msg_str.c_str());
}

void SpecialFunctionHandler::handleWarningOnce(ExecutionState &state,
                                               KInstruction *target,
                                               std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_warning_once");

  std::string msg_str = readStringAtAddress(state, arguments[0]);
  klee_warning_once(0, "%s: %s", state.stack.back().kf->function->getName().data(),
                    msg_str.c_str());
}

void SpecialFunctionHandler::handlePrintRange(ExecutionState &state,
                                  KInstruction *target,
                                  std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_print_range");

  std::string msg_str = readStringAtAddress(state, arguments[0]);
  llvm::errs() << msg_str << ":" << arguments[1];
  if (!isa<ConstantExpr>(arguments[1])) {
    // FIXME: Pull into a unique value method?
    ref<ConstantExpr> value;
    bool success __attribute__ ((unused)) = executor.solver->getValue(state, arguments[1], value);
    assert(success && "FIXME: Unhandled solver failure");
    bool res;
    success = executor.solver->mustBeTrue(state, 
                                          EqExpr::create(arguments[1], value), 
                                          res);
    assert(success && "FIXME: Unhandled solver failure");
    if (res) {
      llvm::errs() << " == " << value;
    } else { 
      llvm::errs() << " ~= " << value;
      std::pair< ref<Expr>, ref<Expr> > res =
        executor.solver->getRange(state, arguments[1]);
      llvm::errs() << " (in [" << res.first << ", " << res.second <<"])";
    }
  }
  llvm::errs() << "\n";
}

void SpecialFunctionHandler::handleGetObjSize(ExecutionState &state,
                                  KInstruction *target,
                                  std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_get_obj_size");
  Executor::ExactResolutionList rl;
  executor.resolveExact(state, arguments[0], rl, "klee_get_obj_size");
  for (Executor::ExactResolutionList::iterator it = rl.begin(), 
         ie = rl.end(); it != ie; ++it) {
    executor.bindLocal(
        target, *it->second,
        ConstantExpr::create(it->first.first->size,
                             executor.kmodule->targetData->getTypeSizeInBits(
                                 target->inst->getType())));
  }
}

void SpecialFunctionHandler::handleGetErrno(ExecutionState &state,
                                            KInstruction *target,
                                            std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==0 &&
         "invalid number of arguments to klee_get_errno");
  executor.bindLocal(target, state,
                     ConstantExpr::create(errno, Expr::Int32));
}

void SpecialFunctionHandler::handleCalloc(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==2 &&
         "invalid number of arguments to calloc");

  ref<Expr> size = MulExpr::create(arguments[0],
                                   arguments[1]);
  executor.executeAlloc(state, size, false, target, true);
}

void SpecialFunctionHandler::handleRealloc(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==2 &&
         "invalid number of arguments to realloc");
  ref<Expr> address = arguments[0];
  ref<Expr> size = arguments[1];

  Executor::StatePair zeroSize = executor.fork(state, 
                                               Expr::createIsZero(size), 
                                               true);
  
  if (zeroSize.first) { // size == 0
    executor.executeFree(*zeroSize.first, address, target);   
  }
  if (zeroSize.second) { // size != 0
    Executor::StatePair zeroPointer = executor.fork(*zeroSize.second, 
                                                    Expr::createIsZero(address), 
                                                    true);
    
    if (zeroPointer.first) { // address == 0
      executor.executeAlloc(*zeroPointer.first, size, false, target);
    } 
    if (zeroPointer.second) { // address != 0
      Executor::ExactResolutionList rl;
      executor.resolveExact(*zeroPointer.second, address, rl, "realloc");
      
      for (Executor::ExactResolutionList::iterator it = rl.begin(), 
             ie = rl.end(); it != ie; ++it) {
        executor.executeAlloc(*it->second, size, false, target, false, 
                              it->first.second);
      }
    }
  }
}

void SpecialFunctionHandler::handleFree(ExecutionState &state,
                          KInstruction *target,
                          std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 &&
         "invalid number of arguments to free");
  executor.executeFree(state, arguments[0]);
}

void SpecialFunctionHandler::handleCheckMemoryAccess(ExecutionState &state,
                                                     KInstruction *target,
                                                     std::vector<ref<Expr> > 
                                                       &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_check_memory_access");

  ref<Expr> address = executor.toUnique(state, arguments[0]);
  ref<Expr> size = executor.toUnique(state, arguments[1]);
  if (!isa<ConstantExpr>(address) || !isa<ConstantExpr>(size)) {
    executor.terminateStateOnError(state, 
                                   "check_memory_access requires constant args",
				   Executor::User);
  } else {
    ObjectPair op;

    if (!state.addressSpace.resolveOne(cast<ConstantExpr>(address), op)) {
      executor.terminateStateOnError(state,
                                     "check_memory_access: memory error",
				     Executor::Ptr, NULL,
                                     executor.getAddressInfo(state, address));
    } else {
      ref<Expr> chk = 
        op.first->getBoundsCheckPointer(address, 
                                        cast<ConstantExpr>(size)->getZExtValue());
      if (!chk->isTrue()) {
        executor.terminateStateOnError(state,
                                       "check_memory_access: memory error",
				       Executor::Ptr, NULL,
                                       executor.getAddressInfo(state, address));
      }
    }
  }
}

/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/

ObjectPair op;
const MemoryObject *mo;
const ObjectState  *os;

/*******************************************************/
/* Make the string a global variable for usability ... */
/*******************************************************/
ref<Expr> offset_of_p_within_MISHMISH;

/***************************************************************/
/* constant: everything is sign extended to 32 bits by default */
/***************************************************************/
ref<Expr> constant(int d)
{
	return klee::ConstantExpr::create(d,Expr::Int32);
}

/*************************************************************************/
/* char_c_at_location: everything is sign extended to 32 bits by default */
/*************************************************************************/
ref<Expr> char_c_at_location(int n)
{
	return
		SExtExpr::create
		(
			os->read
			(
				AddExpr::create
				(
					offset_of_p_within_MISHMISH,
					klee::ConstantExpr::create
					(
						n,
						offset_of_p_within_MISHMISH->getWidth()
					)
				),
				Expr::Int8
			),
			Expr::Int32
		);
}

/**********************************************************************/
/* char_c_is_not_0_at_location: for my atoi string length assumptions */
/**********************************************************************/
ref<Expr> char_c_is_0_at_location(int n)
{
	return
		SExtExpr::create
		(
			EqExpr::create
			(
				char_c_at_location(n),
				constant(0)
			),
			Expr::Int32
		);
}

/**********************************************************************/
/* char_c_is_not_0_at_location: for my atoi string length assumptions */
/**********************************************************************/
ref<Expr> char_c_is_not_0_at_location(int n)
{
	return
		SExtExpr::create
		(
			NeExpr::create
			(
				char_c_at_location(n),
				constant(0)
			),
			Expr::Int32
		);
}

/**************************************************************************/
/* char_c_is_not_0_at_location_leq: for my atoi string length assumptions */
/**************************************************************************/
ref<Expr> char_c_is_not_0_at_location_leq(int n)
{
	if (n == 0)
	{
		return char_c_is_not_0_at_location(0);
	}
	else
	{
		return
			MulExpr::create
			(
				char_c_is_not_0_at_location(n),
				char_c_is_not_0_at_location_leq(n-1)
			);
	}
}

/************************************************************************/
/* char_c_is_a_digit_at_location: for my atoi string length assumptions */
/************************************************************************/
ref<Expr> char_c_is_ge_than_0_at_location(int n)
{
	return
		SExtExpr::create
		(
			SgeExpr::create
			(
				char_c_at_location(n),
				constant('0')
			),
			Expr::Int32
		);
}

/************************************************************************/
/* char_c_is_a_digit_at_location: for my atoi string length assumptions */
/************************************************************************/
ref<Expr> char_c_is_le_than_9_at_location(int n)
{
	return
		SExtExpr::create
		(
			SleExpr::create
			(
				char_c_at_location(n),
				constant('9')
			),
			Expr::Int32
		);
}

/************************************************************************/
/* char_c_is_a_digit_at_location: for my atoi string length assumptions */
/************************************************************************/
ref<Expr> char_c_is_a_digit_at_location(int n)
{
	return
		MulExpr::create
		(
			char_c_is_ge_than_0_at_location(n),
			char_c_is_le_than_9_at_location(n)
		);
}

/************************************************************************/
/* char_c_is_a_digit_at_location: for my atoi string length assumptions */
/************************************************************************/
ref<Expr> char_c_is_a_digit_at_location_leq(int n)
{
	if (n == 0)
	{
		return char_c_is_a_digit_at_location(0);
	}
	else
	{
		return
			MulExpr::create
			(
				char_c_is_a_digit_at_location(n),
				char_c_is_a_digit_at_location_leq(n-1)
			);
	}
}

ref<Expr> all_digits_base_10_atoi_for_non_empty_strings_with_length_eq(int n)
{
	/**********/
	/* n >= 1 */
	/**********/
	if (n == 1)
	{
		return
			SubExpr::create
			(
				char_c_at_location(0),
				constant('0')
			);
	}
	else
	{
		/**********/
		/* n >= 2 */
		/**********/
		return
			AddExpr::create
			(
				SubExpr::create
				(
					char_c_at_location(n-1),
					constant('0')
				),
				MulExpr::create
				(
					constant(10),
					all_digits_base_10_atoi_for_non_empty_strings_with_length_eq(n-1)
				)
			);		
	}
}

ref<Expr> MyAtoiFormula_for_non_empty_strings_with_length_eq(int n)
{
	/**********/
	/* n >= 1 */
	/**********/
	if (n == 1)
	{
		return
			MulExpr::create
			(
				MulExpr::create
				(
					char_c_is_a_digit_at_location(0),
					char_c_is_0_at_location(1)
				),
				SubExpr::create
				(
					char_c_at_location(0),
					constant('0')
				)
			);
	}
	else
	{
		/**********/
		/* n >= 2 */
		/**********/
		return
			MulExpr::create
			(
				char_c_is_0_at_location(n),
				MulExpr::create
				(
					char_c_is_a_digit_at_location_leq(n-1),
					all_digits_base_10_atoi_for_non_empty_strings_with_length_eq(n)
				)
			);
	}
}

ref<Expr> MyAtoiFormula_for_non_empty_strings_with_length_leq(int n)
{
	/**********/
	/* n >= 1 */
	/**********/
	if (n == 1)
	{
		return MyAtoiFormula_for_non_empty_strings_with_length_eq(1);
	}
	else
	{
		/**********/
		/* n >= 2 */
		/**********/
		return
			AddExpr::create
			(
				MyAtoiFormula_for_non_empty_strings_with_length_eq(n),
				MyAtoiFormula_for_non_empty_strings_with_length_leq(n-1)
			);	
	}		
}

ref<Expr> MyAtoiFormula_for_strings_with_length_leq(int maxStringLength)
{
	return
		MulExpr::create
		(
			char_c_is_not_0_at_location(0),
			MyAtoiFormula_for_non_empty_strings_with_length_leq(maxStringLength)
		);
}

ref<Expr> MyStrlenFormula_for_null_terminated_strings(void)
{
	return constant(-1);
	//	IteExpr::create
	//	(
	//		SgeExpr::create
	//		(
	//			first_backslash_x00(),
	//			StrlenExpr::create(offset_of_p_within_MISHMISH)
	//		),
	//		StrlenExpr::create(offset_of_p_within_MISHMISH),
	//		first_backslash_x00()
	//	);
}

ref<Expr> MyStrlenFormula(void)
{
	return constant(-1);
	//	IteExpr::create
	//	(
	//		no_0_inside_string,
	//		constant(-1),
	//		MyStrlenFormula_for_null_terminated_strings()
	//	);
}

void SpecialFunctionHandler::handleMyStrlen(
	ExecutionState &state,
	KInstruction *target,
	std::vector<ref<Expr> > &arguments)
{
	bool success=true;

	/**************************************************************/
	/* [1] Make sure MyStrlen uses the SMT-formula implementation */
	/**************************************************************/
	llvm::errs() << "***************************************" << "\n";
	llvm::errs() << "* [0] MyStrlen formula implementation *" << "\n";
	llvm::errs() << "***************************************" << "\n";

	/******************************************************************/
	/* [2] resolveExact is commented out -- wrong guy for the job ... */
	/******************************************************************/
	//Executor::ExactResolutionList resolutionList;
	//executor.resolveExact(
	//	state,
	//	arguments[0],
	//	resolutionList,
	//	"MyAtoi");
	//const MemoryObject *mo = resolutionList[0].first.first;
	//const ObjectState  *os = resolutionList[0].first.second;
	
	/*********************************************************/
	/* [3] This is the right guy for the job: resolveOne ... */
	/*********************************************************/
	state.addressSpace.resolveOne(
		state,
		executor.solver,
		arguments[0],
		op,
		success);

	/************************************/
	/* [3] Yes ! Everything went well ! */
	/************************************/
	llvm::errs() << "********************************" << "\n";
	llvm::errs() << "* [1] resolveOne succeeded ... *" << "\n";
	llvm::errs() << "********************************" << "\n";
	
	/************************************************************************/
	/* [4] Use MemoryObject & ObjectState that returned from resolveOne ... */
	/************************************************************************/
	mo = op.first;
	os = op.second;

	/**********************************/
	/* [4] Yes! Everything went well! */
	/**********************************/
	llvm::errs() << "*****************************************" << "\n";
	llvm::errs() << "* [2] mo + os assignments succeeded ... *" << "\n";
	llvm::errs() << "*****************************************" << "\n";

	/**********************************************************/
	/* [5] where does arg0 points inside the symbolic array ? */
	/**********************************************************/
	offset_of_p_within_MISHMISH = mo->getOffsetExpr(arguments[0]);

	/**********************************/
	/* [5] Yes! Everything went well! */
	/**********************************/
	llvm::errs() << "*************************************************" << "\n";
	llvm::errs() << "* [3] offset of p within MISHMISH succeeded ... *" << "\n";
	llvm::errs() << "*************************************************" << "\n";

	/********************************************************************************/
	/* [6] Use (many) helper functions to assemble the overall formula for MyStrlen */
	/********************************************************************************/
	ref<Expr> MyStrlenFormula = constant(3);//MyStrlenFormula();
	
	/****************************************************************/
	/* [7] use bindLocal to bind the returned value of the function */
	/****************************************************************/
	executor.bindLocal(
		target, 
		state,
		MyStrlenFormula);
}

void SpecialFunctionHandler::handleMyStrcpy(
	ExecutionState &state,
	KInstruction *target,
	std::vector<ref<Expr> > &arguments)
{
	/*****************************************/
	/* [1] Extract the llvm call instruction */
	/*****************************************/
	llvm::CallInst *callInst = (llvm::CallInst *) target->inst;

	/*********************************************/
	/* [2] Extract the all three input arguments */
	/*********************************************/
	llvm::Value *value0 = callInst->getArgOperand(0);
	llvm::Value *value1 = callInst->getArgOperand(1);
		
	/********************************************/
	/* [3] Take the name of the input arguments */
	/********************************************/
	std::string varName0 = value0->getName().str();
	std::string varName1 = value1->getName().str();

	/*****************************************************/
	/* [4] Go back to the original local variables names */
	/*****************************************************/
	std::string p = state.varNames[varName0];
	std::string q = state.varNames[varName1];

	/***************************************************************************/
	/* [5] Apply the relevant semantics transformer:                           */
	/*     for strcpy(p,q) this involves the following:                        */
	/*                                                                         */
	/*     -----------------------------------------------------               */
	/*     -------------------- DEFINITIONS --------------------               */
	/*     -----------------------------------------------------               */
	/*                                                                         */
	/*     offset_p := offset(p);                                              */
	/*     serial_p := serial(p);                                              */
	/*     last     := last(serial_p);                                         */
	/*     AB_p_tag := AB_{serial_p,last_p}                                    */
	/*     AB_p     := Substr(AB,offset_q,Strlen(AB) - offset_p)               */
	/*                                                                         */
	/*     offset_q := offset(q);                                              */
	/*     serial_q := serial(q);                                              */
	/*     last     := last(serial_q);                                         */
	/*     AB_q_tag := AB_{serial_q,last_q}                                    */
	/*     AB_q     := Substr(AB_q_tag,offset_q,Strlen(AB_q_tag)-offset_q)     */
	/*     AB_q_C   := ite((= -1 indexof(AB_q,"\x00"))                         */
	/*                     AB_q                                                */
	/*                     Substr(AB_q,0,indexof(AB_q,"\x00"))                 */
	/*                                                                         */
	/*     -----------------------------------------------------               */
	/*     -----------------------------------------------------               */
	/*     -----------------------------------------------------               */
	/*                                                                         */
	/*     if (!= AB_q_C AB_q)                                    { error(); } */
	/*     else if (Strlen(AB_q_C) > (size(serial_p) - offset_p)) { error(); } */
	/*     else                                                                */
	/*     {                                                                   */
	/*         Cons.add(= AB_q_C Substr(AB_{serial_p,last_p+1}                 */
	/*     }                                                                   */
	/*                                                                         */
	/***************************************************************************/
	int offset_p = state.ab_offset[p];
	int serial_p = state.ab_serial[p];
	int last_p   = state.ab_last[serial_p];
	

	/***********************************/
	/* [6] For debug purposes only ... */
	/***********************************/
	llvm::errs() << varName0 << "\n";
	llvm::errs() << varName1 << "\n";
}

void SpecialFunctionHandler::handleMyConstStringAssign(
	ExecutionState &state,
	KInstruction *target,
	std::vector<ref<Expr> > &arguments)
{
	llvm::Value *value0;
	llvm::Value *value1;

	std::string varName0;
	std::string varName1;
	std::string varName1Tag;

	llvm::GetElementPtrInst * value1Gep;

	/*****************************************/
	/* [1] Extract the llvm call instruction */
	/*****************************************/
	llvm::CallInst *callInst = (llvm::CallInst *) target->inst;
	
	/***************************************/
	/* [2] Extract the two input arguments */
	/***************************************/
	value0 = callInst->getArgOperand(0);
	value1 = callInst->getArgOperand(1);

	/******************/
	/* [3] Gep it !!! */
	/******************/
	value1Gep = ((llvm::GetElementPtrInst *) value1);

	/***********************************************/
	/* [4] Extract the name of the input arguments */
	/***********************************************/
	varName0      = value0->getName();
	varName1      = value1Gep->getName();
	varName1Tag   = value1Gep->getOperand(0)->getName();

	/**********************************************/
	/* [5] Extract the actual underlying c string */
	/**********************************************/
	llvm::GlobalVariable    *actualCStringVar     = (llvm::GlobalVariable    *) (value1Gep->getOperand(0));
	llvm::ConstantDataArray *actualCStringVarTag  = (llvm::ConstantDataArray *) (actualCStringVar->getInitializer());
	std::string actualCStringContent              = actualCStringVarTag->getAsCString();

	/***********************************************************************/
	/* [6] Print the name of the input arguments + actual c string content */
	/***********************************************************************/
	llvm::errs() << "varName0             = " << varName0             << "\n";
	llvm::errs() << "varName1             = " << varName1             << "\n";
	llvm::errs() << "varName1Tag          = " << varName1Tag          << "\n";
	llvm::errs() << "actualCStringContent = " << actualCStringContent << "\n";

	/*********************************************/
	/* [2] Extract the all three input arguments */
	/*********************************************/
	// llvm::Value *value0 = callInst->getArgOperand(0);
	// llvm::Value *value1 = callInst->getArgOperand(1);
		
	/********************************************/
	/* [3] Take the name of the input arguments */
	/********************************************/
	// std::string varName0 = value0->getName().str();
	// std::string varName1 = ((llvm::GetElementPtrInst *) value1)->getOperand(0)->getName();

	/*****************************************************/
	/* [4] Go back to the original local variables names */
	/*****************************************************/
	//std::string p = state.varNames[varName0];
	//std::string q = state.varNames[varName1];

	/***************************************************************************/
	/* [5] Apply the relevant semantics transformer:                           */
	/*     for strcpy(p,q) this involves the following:                        */
	/*                                                                         */
	/*     -----------------------------------------------------               */
	/*     -------------------- DEFINITIONS --------------------               */
	/*     -----------------------------------------------------               */
	/*                                                                         */
	/*     offset_p := offset(p);                                              */
	/*     serial_p := serial(p);                                              */
	/*     last     := last(serial_p);                                         */
	/*     AB_p_tag := AB_{serial_p,last_p}                                    */
	/*     AB_p     := Substr(AB,offset_q,Strlen(AB) - offset_p)               */
	/*                                                                         */
	/*     offset_q := offset(q);                                              */
	/*     serial_q := serial(q);                                              */
	/*     last     := last(serial_q);                                         */
	/*     AB_q_tag := AB_{serial_q,last_q}                                    */
	/*     AB_q     := Substr(AB_q_tag,offset_q,Strlen(AB_q_tag)-offset_q)     */
	/*     AB_q_C   := ite((= -1 indexof(AB_q,"\x00"))                         */
	/*                     AB_q                                                */
	/*                     Substr(AB_q,0,indexof(AB_q,"\x00"))                 */
	/*                                                                         */
	/*     -----------------------------------------------------               */
	/*     -----------------------------------------------------               */
	/*     -----------------------------------------------------               */
	/*                                                                         */
	/*     if (!= AB_q_C AB_q)                                    { error(); } */
	/*     else if (Strlen(AB_q_C) > (size(serial_p) - offset_p)) { error(); } */
	/*     else                                                                */
	/*     {                                                                   */
	/*         Cons.add(= AB_q_C Substr(AB_{serial_p,last_p+1}                 */
	/*     }                                                                   */
	/*                                                                         */
	/***************************************************************************/
	//int offset_p = state.ab_offset[p];
	//int serial_p = state.ab_serial[p];
	//int last_p   = state.ab_last[serial_p];
	

	/***********************************/
	/* [6] For debug purposes only ... */
	/***********************************/
	//llvm::errs() << varName0 << "\n";
	//llvm::errs() << varName1 << "\n";	
}

void SpecialFunctionHandler::handleMyStrcmp(
	ExecutionState &state,
	KInstruction *target,
	std::vector<ref<Expr> > &arguments){}

void SpecialFunctionHandler::handleMyReadCharFromStringAtOffset(
	ExecutionState &state,
	KInstruction *target,
	std::vector<ref<Expr> > &arguments){}

void SpecialFunctionHandler::handleMyWriteCharToStringAtOffset(
	ExecutionState &state,
	KInstruction *target,
	std::vector<ref<Expr> > &arguments){}

void SpecialFunctionHandler::handleMyCharAssign(
	ExecutionState &state,
	KInstruction *target,
	std::vector<ref<Expr> > &arguments){}

void SpecialFunctionHandler::handleMy_p_assign_NULL(
	ExecutionState &state,
	KInstruction *target,
	std::vector<ref<Expr> > &arguments)
{
	/*****************************************/
	/* [1] Extract the llvm call instruction */
	/*****************************************/
	llvm::CallInst *callInst = (llvm::CallInst *) target->inst;

	/***************************************************/
	/* [2] Extract the first (and only) input argument */
	/***************************************************/
	llvm::Value *value = callInst->getArgOperand(0);
		
	/****************************************************/
	/* [3] Take the name of the input (string) argument */
	/****************************************************/
	std::string varName = value->getName().str();

	/*************************************************/
	/* [4] Apply the relevant semantics transformer: */
	/*     for p := NULL, this involves only setting */
	/*     serial(p) := 0                            */
	/*     that is, a non existing serial            */
	/*************************************************/
	state.ab_serial[varName] = 0;

	/***********************************/
	/* [5] For debug purposes only ... */
	/***********************************/
	llvm::errs() << varName << "\n";
}

void SpecialFunctionHandler::handleMyIntAssign(
	ExecutionState &state,
	KInstruction *target,
	std::vector<ref<Expr> > &arguments)
{
	/*****************************************/
	/* [1] Extract the llvm call instruction */
	/*****************************************/
	llvm::CallInst *callInst = (llvm::CallInst *) target->inst;

	/*********************************************/
	/* [2] Extract the all three input arguments */
	/*********************************************/
	llvm::Value *value0 = callInst->getArgOperand(0);
	llvm::Value *value1 = callInst->getArgOperand(1);
	// llvm::Value *value2 = callInst->getArgOperand(2);
		
	/********************************************/
	/* [3] Take the name of the input arguments */
	/********************************************/
	std::string varName0 = value0->getName().str();
	std::string varName1 = value1->getName().str();
	// std::string varName2 = value2->getName().str();

	/****************************************************************/
	/* [4] Apply the relevant semantics transformer:                */
	/*     for p[i] := c, this involves only setting the following: */
	/*     serial(p) := 0                                           */
	/*     that is, a non existing serial                           */
	/****************************************************************/
	// state.oren_serials[varName] = 0;

	/***********************************/
	/* [5] For debug purposes only ... */
	/***********************************/
	llvm::errs() << varName0 << "\n";
	llvm::errs() << varName1 << "\n";
	// llvm::errs() << varName2 << "\n";
}

void SpecialFunctionHandler::handleMyMalloc(
	ExecutionState &state,
	KInstruction *target,
	std::vector<ref<Expr> > &arguments)
{
	/*****************************************/
	/* [1] Extract the llvm call instruction */
	/*****************************************/
	llvm::CallInst *callInst = (llvm::CallInst *) target->inst;

	/*********************************************/
	/* [2] Extract the all three input arguments */
	/*********************************************/
	llvm::Value *value0 = callInst->getArgOperand(0);
	llvm::Value *value1 = callInst->getArgOperand(1);
		
	/********************************************/
	/* [3] Take the name of the input arguments */
	/********************************************/
	std::string varName0 = value0->getName().str();
	std::string varName1 = value1->getName().str();

	/*****************************************************/
	/* [4] Go back to the original local variables names */
	/*****************************************************/
	std::string p = state.varNames[varName0];
	std::string size = state.varNames[varName1];

	/***************************************************************************/
	/* [5] Apply the relevant semantics transformer:                           */
	/*     for p = malloc(size) this involves the following:                   */
	/*                                                                         */
	/*     serial(p) = some-new-serial                                         */
	/*     last(serial(p)) = 0                                                 */
	/*     offset(p) = 0                                                       */
	/*                                                                         */
	/***************************************************************************/
	state.ab_serial[p] = ++state.numABSerials;
	state.ab_last[state.ab_serial[p]] = 0;
	state.ab_offset[p] = 0;

	/***********************************/
	/* [6] For debug purposes only ... */
	/***********************************/
	llvm::errs() << p << "\n";
	llvm::errs() << size << "\n";
}

void SpecialFunctionHandler::handleMyStrchr(
	ExecutionState &state,
	KInstruction *target,
	std::vector<ref<Expr> > &arguments)
{
	/**************************************************************/
	/* [1] Make sure MyStrchr uses the SMT-formula implementation */
	/**************************************************************/
	llvm::errs() << "***************************************" << "\n";
	llvm::errs() << "* [0] MyStrchr formula implementation *" << "\n";
	llvm::errs() << "***************************************" << "\n";	
}

void SpecialFunctionHandler::handleMyAtoi(
	ExecutionState &state,
	KInstruction *target,
	std::vector<ref<Expr> > &arguments)
{
	bool success=true;
	const int maxStringLength = 10;

	/************************************************************/
	/* [1] Make sure MyAtoi uses the SMT-formula implementation */
	/************************************************************/
	llvm::errs() << "*************************************" << "\n";
	llvm::errs() << "* [0] MyAtoi formula implementation *" << "\n";
	llvm::errs() << "*************************************" << "\n";

	/******************************************************************/
	/* [2] resolveExact is commented out -- wrong guy for the job ... */
	/******************************************************************/
	//Executor::ExactResolutionList resolutionList;
	//executor.resolveExact(
	//	state,
	//	arguments[0],
	//	resolutionList,
	//	"MyAtoi");
	//const MemoryObject *mo = resolutionList[0].first.first;
	//const ObjectState  *os = resolutionList[0].first.second;
	
	/*********************************************************/
	/* [3] This is the right guy for the job: resolveOne ... */
	/*********************************************************/
	state.addressSpace.resolveOne(
		state,
		executor.solver,
		arguments[0],
		op,
		success);

	llvm::errs() << "********************************" << "\n";
	llvm::errs() << "* [1] resolveOne succeeded ... *" << "\n";
	llvm::errs() << "********************************" << "\n";
	
	/************************************************************************/
	/* [4] Use MemoryObject & ObjectState that returned from resolveOne ... */
	/************************************************************************/
	mo = op.first;
	os = op.second;

	llvm::errs() << "*****************************************" << "\n";
	llvm::errs() << "* [2] mo + os assignments succeeded ... *" << "\n";
	llvm::errs() << "*****************************************" << "\n";

	/**********************************************************/
	/* [5] where does arg0 points inside the symbolic array ? */
	/**********************************************************/
	offset_of_p_within_MISHMISH = mo->getOffsetExpr(arguments[0]);

	llvm::errs() << "*************************************************" << "\n";
	llvm::errs() << "* [3] offset of p within MISHMISH succeeded ... *" << "\n";
	llvm::errs() << "*************************************************" << "\n";

	/*****************************************************************/
	/* [6] Use many helper functions to assemble the overall formula */
	/*     for MyAtoi. Use maxStringLength as a parameter ...        */
	/*****************************************************************/
	ref<Expr> MyAtoiFormula =
	MyAtoiFormula_for_strings_with_length_leq(maxStringLength);
	
	/****************************************************************/
	/* [7] use bindLocal to bind the returned value of the function */
	/****************************************************************/
	executor.bindLocal(
		target, 
		state,
		MyAtoiFormula);
}

void SpecialFunctionHandler::handleGetValue(ExecutionState &state,
                                            KInstruction *target,
                                            std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_get_value");

  executor.executeGetValue(state, arguments[0], target);
}

void SpecialFunctionHandler::handleDefineFixedObject(ExecutionState &state,
                                                     KInstruction *target,
                                                     std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_define_fixed_object");
  assert(isa<ConstantExpr>(arguments[0]) &&
         "expect constant address argument to klee_define_fixed_object");
  assert(isa<ConstantExpr>(arguments[1]) &&
         "expect constant size argument to klee_define_fixed_object");
  
  uint64_t address = cast<ConstantExpr>(arguments[0])->getZExtValue();
  uint64_t size = cast<ConstantExpr>(arguments[1])->getZExtValue();
  MemoryObject *mo = executor.memory->allocateFixed(address, size, state.prevPC->inst);
  executor.bindObjectInState(state, mo, false);
  mo->isUserSpecified = true; // XXX hack;
}

void SpecialFunctionHandler::handleMakeSymbolic(ExecutionState &state,
                                                KInstruction *target,
                                                std::vector<ref<Expr> > &arguments) {
  std::string name;

  // FIXME: For backwards compatibility, we should eventually enforce the
  // correct arguments.
  if (arguments.size() == 2) {
    name = "unnamed";
  } else {
    // FIXME: Should be a user.err, not an assert.
    assert(arguments.size()==3 &&
           "invalid number of arguments to klee_make_symbolic");  
    name = readStringAtAddress(state, arguments[2]);
  }

  Executor::ExactResolutionList rl;
  executor.resolveExact(state, arguments[0], rl, "make_symbolic");
  
  for (Executor::ExactResolutionList::iterator it = rl.begin(), 
         ie = rl.end(); it != ie; ++it) {
    const MemoryObject *mo = it->first.first;
    mo->setName(name);
    
    const ObjectState *old = it->first.second;
    ExecutionState *s = it->second;
    
    if (old->readOnly) {
      executor.terminateStateOnError(*s, "cannot make readonly object symbolic",
                                     Executor::User);
      return;
    } 

    // FIXME: Type coercion should be done consistently somewhere.
    bool res;
    bool success __attribute__ ((unused)) =
      executor.solver->mustBeTrue(*s, 
                                  EqExpr::create(ZExtExpr::create(arguments[1],
                                                                  Context::get().getPointerWidth()),
                                                 mo->getSizeExpr()),
                                  res);
    assert(success && "FIXME: Unhandled solver failure");
    
    if (res) {
      executor.executeMakeSymbolic(*s, mo, name);
    } else {      
      executor.terminateStateOnError(*s, 
                                     "wrong size given to klee_make_symbolic[_name]", 
                                     Executor::User);
    }
  }
}

void SpecialFunctionHandler::handleMarkGlobal(ExecutionState &state,
                                              KInstruction *target,
                                              std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_mark_global");  

  Executor::ExactResolutionList rl;
  executor.resolveExact(state, arguments[0], rl, "mark_global");
  
  for (Executor::ExactResolutionList::iterator it = rl.begin(), 
         ie = rl.end(); it != ie; ++it) {
    const MemoryObject *mo = it->first.first;
    assert(!mo->isLocal);
    mo->isGlobal = true;
  }
}

void SpecialFunctionHandler::handleAddOverflow(ExecutionState &state,
                                               KInstruction *target,
                                               std::vector<ref<Expr> > &arguments) {
  executor.terminateStateOnError(state, "overflow on unsigned addition",
                                 Executor::Overflow);
}

void SpecialFunctionHandler::handleSubOverflow(ExecutionState &state,
                                               KInstruction *target,
                                               std::vector<ref<Expr> > &arguments) {
  executor.terminateStateOnError(state, "overflow on unsigned subtraction",
                                 Executor::Overflow);
}

void SpecialFunctionHandler::handleMulOverflow(ExecutionState &state,
                                               KInstruction *target,
                                               std::vector<ref<Expr> > &arguments) {
  executor.terminateStateOnError(state, "overflow on unsigned multiplication",
                                 Executor::Overflow);
}

void SpecialFunctionHandler::handleDivRemOverflow(ExecutionState &state,
                                               KInstruction *target,
                                               std::vector<ref<Expr> > &arguments) {
  executor.terminateStateOnError(state, "overflow on division or remainder",
                                 Executor::Overflow);
}
