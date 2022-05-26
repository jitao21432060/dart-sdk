// Copyright (c) 2018, the Dart project authors.  Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include <setjmp.h>  // NOLINT
#include <stdlib.h>

#if !defined(DART_PRECOMPILED_RUNTIME) || defined(DART_DYNAMIC_RUNTIME)

#include "vm/interpreter.h"

#include "vm/class_id.h"
#include "vm/compiler/api/type_check_mode.h"
#include "vm/compiler/assembler/disassembler_kbc.h"
#include "vm/compiler/backend/flow_graph_compiler.h"
#include "vm/compiler/ffi/abi.h"
#include "vm/compiler/frontend/bytecode_reader.h"
#include "vm/compiler/jit/compiler.h"
#include "vm/cpu.h"
#include "vm/dart_entry.h"
#include "vm/debugger.h"
#include "vm/lockers.h"
#include "vm/native_arguments.h"
#include "vm/native_entry.h"
#include "vm/object.h"
#include "vm/object_store.h"
#include "vm/os_thread.h"
#include "vm/stack_frame_kbc.h"
#include "vm/symbols.h"

namespace dart {
// InterpreterSetjmpBuffer are linked together, and the last created one
// is referenced by the Interpreter. When an exception is thrown, the exception
// runtime looks at where to jump and finds the corresponding
// InterpreterSetjmpBuffer based on the stack pointer of the exception handler.
// The runtime then does a Longjmp on that buffer to return to the interpreter.
class InterpreterSetjmpBuffer {
 public:
  void Longjmp() {
    // "This" is now the last setjmp buffer.
    interpreter_->set_last_setjmp_buffer(this);
    longjmp(buffer_, 1);
  }

  explicit InterpreterSetjmpBuffer(Interpreter* interpreter) {
    interpreter_ = interpreter;
    link_ = interpreter->last_setjmp_buffer();
    interpreter->set_last_setjmp_buffer(this);
    fp_ = interpreter->fp_;
  }

  ~InterpreterSetjmpBuffer() {
    ASSERT(interpreter_->last_setjmp_buffer() == this);
    interpreter_->set_last_setjmp_buffer(link_);
  }

  InterpreterSetjmpBuffer* link() const { return link_; }

  uword fp() const { return reinterpret_cast<uword>(fp_); }

  jmp_buf buffer_;

 private:
  ObjectPtr* fp_;
  Interpreter* interpreter_;
  InterpreterSetjmpBuffer* link_;

  friend class Interpreter;

  DISALLOW_ALLOCATION();
  DISALLOW_COPY_AND_ASSIGN(InterpreterSetjmpBuffer);
};

DART_FORCE_INLINE static ObjectPtr* SavedCallerFP(ObjectPtr* FP) {
  return reinterpret_cast<ObjectPtr*>(
      static_cast<uword>(FP[kKBCSavedCallerFpSlotFromFp]));
}

DART_FORCE_INLINE static ObjectPtr* FrameArguments(ObjectPtr* FP,
                                                   intptr_t argc) {
  return FP - (kKBCDartFrameFixedSize + argc);
}

#define RAW_CAST(Type, val) (InterpreterHelpers::CastTo##Type(val))

class InterpreterHelpers {
 public:
#define DEFINE_CASTS(Type)                                                     \
  DART_FORCE_INLINE static Type##Ptr CastTo##Type(ObjectPtr obj) {             \
    ASSERT((k##Type##Cid == kSmiCid)                                           \
               ? !obj->IsHeapObject()                                          \
               : (k##Type##Cid == kIntegerCid)                                 \
                     ? (!obj->IsHeapObject() || obj->IsMint())                 \
                     : obj->Is##Type());                                       \
    return static_cast<Type##Ptr>(obj);                                        \
  }
  CLASS_LIST(DEFINE_CASTS)
#undef DEFINE_CASTS

  DART_FORCE_INLINE static SmiPtr GetClassIdAsSmi(ObjectPtr obj) {
    return Smi::New(obj->IsHeapObject() ? obj->GetClassId()
                                        : static_cast<intptr_t>(kSmiCid));
  }

  DART_FORCE_INLINE static intptr_t GetClassId(ObjectPtr obj) {
    return obj->IsHeapObject() ? obj->GetClassId()
                               : static_cast<intptr_t>(kSmiCid);
  }

  DART_FORCE_INLINE static TypeArgumentsPtr GetTypeArguments(
      Thread* thread,
      ObjectPtr instance) {
    ClassPtr instance_class =
        thread->isolate()->group()->class_table()->At(GetClassId(instance));
    return instance_class->untag()->num_type_arguments_ > 0
               ? reinterpret_cast<TypeArgumentsPtr*>(instance->untag())
                     [instance_class->untag()
                          ->host_type_arguments_field_offset_in_words_]
               : TypeArguments::null();
  }
#if !defined(DART_DYNAMIC_RUNTIME)
  // The usage counter is actually a 'hotness' counter.
  // For an instance call, both the usage counters of the caller and of the
  // calle will get incremented, as well as the ICdata counter at the call site.
  DART_FORCE_INLINE static void IncrementUsageCounter(FunctionPtr f) {
    f->untag()->usage_counter_++;
  }

  DART_FORCE_INLINE static void IncrementICUsageCount(ObjectPtr* entries,
                                                      intptr_t offset,
                                                      intptr_t args_tested) {
    const intptr_t count_offset = ICData::CountIndexFor(args_tested);
    const intptr_t raw_smi_old =
        static_cast<intptr_t>(entries[offset + count_offset]);
    const intptr_t raw_smi_new = raw_smi_old + Smi::RawValue(1);
    *reinterpret_cast<intptr_t*>(&entries[offset + count_offset]) = raw_smi_new;
  }
#endif
  DART_FORCE_INLINE static bool CheckIndex(SmiPtr index, SmiPtr length) {
    return !index->IsHeapObject() && (static_cast<intptr_t>(index) >= 0) &&
           (static_cast<intptr_t>(index) < static_cast<intptr_t>(length));
  }

  DART_FORCE_INLINE static intptr_t ArgDescTypeArgsLen(ArrayPtr argdesc) {
    return Smi::Value(*reinterpret_cast<SmiPtr*>(
        reinterpret_cast<uword>(argdesc->untag()) +
        Array::element_offset(ArgumentsDescriptor::kTypeArgsLenIndex)));
  }

  DART_FORCE_INLINE static intptr_t ArgDescArgCount(ArrayPtr argdesc) {
    return Smi::Value(*reinterpret_cast<SmiPtr*>(
        reinterpret_cast<uword>(argdesc->untag()) +
        Array::element_offset(ArgumentsDescriptor::kCountIndex)));
  }

  DART_FORCE_INLINE static intptr_t ArgDescPosCount(ArrayPtr argdesc) {
    return Smi::Value(*reinterpret_cast<SmiPtr*>(
        reinterpret_cast<uword>(argdesc->untag()) +
        Array::element_offset(ArgumentsDescriptor::kPositionalCountIndex)));
  }

  DART_FORCE_INLINE static BytecodePtr FrameBytecode(ObjectPtr* FP) {
    ASSERT(GetClassId(FP[kKBCPcMarkerSlotFromFp]) == kBytecodeCid);
    return static_cast<BytecodePtr>(FP[kKBCPcMarkerSlotFromFp]);
  }

  DART_FORCE_INLINE static bool FieldNeedsGuardUpdate(FieldPtr field,
                                                      ObjectPtr value) {
    // The interpreter should never see a cloned field.
    ASSERT(field->untag()->owner_->GetClassId() != kFieldCid);

    const classid_t guarded_cid = field->untag()->guarded_cid_;

    if (guarded_cid == kDynamicCid) {
      // Field is not guarded.
      return false;
    }

    ASSERT(Isolate::Current()->group()->use_field_guards());

    const classid_t nullability_cid = field->untag()->is_nullable_;
    const classid_t value_cid = InterpreterHelpers::GetClassId(value);

    if (nullability_cid == value_cid) {
      // Storing null into a nullable field.
      return false;
    }

    if (guarded_cid != value_cid) {
      // First assignment (guarded_cid == kIllegalCid) or
      // field no longer monomorphic or
      // field has become nullable.
      return true;
    }

    intptr_t guarded_list_length =
        Smi::Value(field->untag()->guarded_list_length_);

    if (UNLIKELY(guarded_list_length >= Field::kUnknownFixedLength)) {
      // Guarding length, check this in the runtime.
      return true;
    }

    if (UNLIKELY(field->untag()->static_type_exactness_state_ >=
                 StaticTypeExactnessState::Uninitialized().Encode())) {
      // Guarding "exactness", check this in the runtime.
      return true;
    }

    // Everything matches.
    return false;
  }

  DART_FORCE_INLINE static bool IsAllocateFinalized(ClassPtr cls) {
    return Class::ClassFinalizedBits::decode(cls->untag()->state_bits_) ==
           UntaggedClass::kAllocateFinalized;
  }
};

DART_FORCE_INLINE static const KBCInstr* SavedCallerPC(ObjectPtr* FP) {
  return reinterpret_cast<const KBCInstr*>(
      static_cast<uword>(FP[kKBCSavedCallerPcSlotFromFp]));
}

DART_FORCE_INLINE static FunctionPtr FrameFunction(ObjectPtr* FP) {
  FunctionPtr function = static_cast<FunctionPtr>(FP[kKBCFunctionSlotFromFp]);
  ASSERT(InterpreterHelpers::GetClassId(function) == kFunctionCid ||
         InterpreterHelpers::GetClassId(function) == kNullCid);
  return function;
}

DART_FORCE_INLINE static ObjectPtr InitializeHeader(uword addr,
                                                    intptr_t class_id,
                                                    intptr_t instance_size) {
  uint32_t tags = 0;
  tags = UntaggedObject::ClassIdTag::update(class_id, tags);
  tags = UntaggedObject::SizeTag::update(instance_size, tags);
  tags = UntaggedObject::OldBit::update(false, tags);
  tags = UntaggedObject::OldAndNotMarkedBit::update(false, tags);
  tags = UntaggedObject::OldAndNotRememberedBit::update(false, tags);
  tags = UntaggedObject::NewBit::update(true, tags);
  // Also writes zero in the hash_ field.
  *reinterpret_cast<uword*>(addr + Object::tags_offset()) = tags;
  return UntaggedObject::FromAddr(addr);
}

DART_FORCE_INLINE static bool TryAllocate(Thread* thread,
                                          intptr_t class_id,
                                          intptr_t instance_size,
                                          ObjectPtr* result) {
  ASSERT(instance_size > 0);
  ASSERT(Utils::IsAligned(instance_size, kObjectAlignment));

  const uword top = thread->top();
  const intptr_t remaining = thread->end() - top;
  if (LIKELY(remaining >= instance_size)) {
    thread->set_top(top + instance_size);
    *result = InitializeHeader(top, class_id, instance_size);
    return true;
  }
  return false;
}

void LookupCache::Clear() {
  for (intptr_t i = 0; i < kNumEntries; i++) {
    entries_[i].receiver_cid = kIllegalCid;
  }
}

bool LookupCache::Lookup(intptr_t receiver_cid,
                         StringPtr function_name,
                         ArrayPtr arguments_descriptor,
                         FunctionPtr* target) const {
  ASSERT(receiver_cid != kIllegalCid);  // Sentinel value.

  const intptr_t hash = receiver_cid ^ static_cast<intptr_t>(function_name) ^
                        static_cast<intptr_t>(arguments_descriptor);
  const intptr_t probe1 = hash & kTableMask;
  if (entries_[probe1].receiver_cid == receiver_cid &&
      entries_[probe1].function_name == function_name &&
      entries_[probe1].arguments_descriptor == arguments_descriptor) {
    *target = entries_[probe1].target;
    return true;
  }

  intptr_t probe2 = (hash >> 3) & kTableMask;
  if (entries_[probe2].receiver_cid == receiver_cid &&
      entries_[probe2].function_name == function_name &&
      entries_[probe2].arguments_descriptor == arguments_descriptor) {
    *target = entries_[probe2].target;
    return true;
  }

  return false;
}

void LookupCache::Insert(intptr_t receiver_cid,
                         StringPtr function_name,
                         ArrayPtr arguments_descriptor,
                         FunctionPtr target) {
  // Otherwise we have to clear the cache or rehash on scavenges too.
  ASSERT(function_name->IsOldObject());
  ASSERT(arguments_descriptor->IsOldObject());
  ASSERT(target->IsOldObject());

  const intptr_t hash = receiver_cid ^ static_cast<intptr_t>(function_name) ^
                        static_cast<intptr_t>(arguments_descriptor);
  const intptr_t probe1 = hash & kTableMask;
  if (entries_[probe1].receiver_cid == kIllegalCid) {
    entries_[probe1].receiver_cid = receiver_cid;
    entries_[probe1].function_name = function_name;
    entries_[probe1].arguments_descriptor = arguments_descriptor;
    entries_[probe1].target = target;
    return;
  }

  const intptr_t probe2 = (hash >> 3) & kTableMask;
  if (entries_[probe2].receiver_cid == kIllegalCid) {
    entries_[probe2].receiver_cid = receiver_cid;
    entries_[probe2].function_name = function_name;
    entries_[probe2].arguments_descriptor = arguments_descriptor;
    entries_[probe2].target = target;
    return;
  }

  entries_[probe1].receiver_cid = receiver_cid;
  entries_[probe1].function_name = function_name;
  entries_[probe1].arguments_descriptor = arguments_descriptor;
  entries_[probe1].target = target;
}

Interpreter::Interpreter()
    : stack_(NULL),
      fp_(NULL),
      pp_(nullptr),
      argdesc_(nullptr),
      lookup_cache_() {
  // Setup interpreter support first. Some of this information is needed to
  // setup the architecture state.
  // We allocate the stack here, the size is computed as the sum of
  // the size specified by the user and the buffer space needed for
  // handling stack overflow exceptions. To be safe in potential
  // stack underflows we also add some underflow buffer space.
  stack_ = new uintptr_t[(OSThread::GetSpecifiedStackSize() +
                          OSThread::kStackSizeBufferMax +
                          kInterpreterStackUnderflowSize) /
                         sizeof(uintptr_t)];
  // Low address.
  stack_base_ =
      reinterpret_cast<uword>(stack_) + kInterpreterStackUnderflowSize;
  // Limit for StackOverflowError.
  overflow_stack_limit_ = stack_base_ + OSThread::GetSpecifiedStackSize();
  // High address.
  stack_limit_ = overflow_stack_limit_ + OSThread::kStackSizeBufferMax;

  last_setjmp_buffer_ = NULL;

  // Make sure interpreter's unboxing view is consistent with compiler.
  supports_unboxed_doubles_ = FlowGraphCompiler::SupportsUnboxedDoubles();
  supports_unboxed_simd128_ = FlowGraphCompiler::SupportsUnboxedSimd128();
}

Interpreter::~Interpreter() {
  delete[] stack_;
  pp_ = NULL;
  argdesc_ = NULL;
}

// Get the active Interpreter for the current isolate.
Interpreter* Interpreter::Current() {
  Thread* thread = Thread::Current();
  Interpreter* interpreter = thread->interpreter();
  if (interpreter == nullptr) {
    NoSafepointScope no_safepoint;
    interpreter = new Interpreter();
    thread->set_interpreter(interpreter);
  }
  return interpreter;
}

void Interpreter::Exit(Thread* thread,
                       ObjectPtr* base,
                       ObjectPtr* frame,
                       const KBCInstr* pc) {
  frame[0] = Function::null();
  frame[1] = Bytecode::null();
  frame[2] = static_cast<ObjectPtr>(reinterpret_cast<uword>(pc));
  frame[3] = static_cast<ObjectPtr>(reinterpret_cast<uword>(base));

  ObjectPtr* exit_fp = frame + kKBCDartFrameFixedSize;
  thread->set_top_exit_frame_info(reinterpret_cast<uword>(exit_fp));
  fp_ = exit_fp;
}

void Interpreter::Unexit(Thread* thread) {
#if defined(DART_DYNAMIC_RUNTIME)
  // For the profiler.
  ObjectPtr* exit_fp =
      reinterpret_cast<ObjectPtr*>(thread->top_exit_frame_info());
  ASSERT(exit_fp != 0);
  pc_ = SavedCallerPC(exit_fp);
  fp_ = SavedCallerFP(exit_fp);
#endif
  thread->set_top_exit_frame_info(0);
}

// Calling into runtime may trigger garbage collection and relocate objects,
// so all ObjectPtr pointers become outdated and should not be used across
// runtime calls.
// Note: functions below are marked DART_NOINLINE to recover performance where
// inlining these functions into the interpreter loop seemed to cause some code
// quality issues. Functions with the "returns_twice" attribute, such as setjmp,
// prevent reusing spill slots and large frame sizes.
static DART_NOINLINE bool InvokeRuntime(Thread* thread,
                                        Interpreter* interpreter,
                                        RuntimeFunction drt,
                                        const NativeArguments& args) {
  InterpreterSetjmpBuffer buffer(interpreter);
  if (!setjmp(buffer.buffer_)) {
    thread->set_vm_tag(reinterpret_cast<uword>(drt));
    drt(args);
    thread->set_vm_tag(VMTag::kDartInterpretedTagId);
    interpreter->Unexit(thread);
    return true;
  } else {
    return false;
  }
}

static DART_NOINLINE bool InvokeNative(Thread* thread,
                                       Interpreter* interpreter,
                                       NativeFunctionWrapper wrapper,
                                       Dart_NativeFunction function,
                                       Dart_NativeArguments args) {
  InterpreterSetjmpBuffer buffer(interpreter);
  if (!setjmp(buffer.buffer_)) {
    thread->set_vm_tag(reinterpret_cast<uword>(function));
    wrapper(args, function);
    thread->set_vm_tag(VMTag::kDartInterpretedTagId);
    interpreter->Unexit(thread);
    return true;
  } else {
    return false;
  }
}

extern "C" {
// Note: The invocation stub follows the C ABI, so we cannot pass C++ struct
// values like ObjectPtr. In some calling conventions (IA32), ObjectPtr is
// passed/returned different from a pointer.
typedef uword /*ObjectPtr*/ (*invokestub)(uword /*CodePtr*/ code,
                                          uword /*ArrayPtr*/ argdesc,
                                          ObjectPtr* arg0,
                                          Thread* thread);
}

DART_NOINLINE bool Interpreter::InvokeCompiled(Thread* thread,
                                               FunctionPtr function,
                                               ObjectPtr* call_base,
                                               ObjectPtr* call_top,
                                               const KBCInstr** pc,
                                               ObjectPtr** FP,
                                               ObjectPtr** SP) {
  ASSERT(Function::HasCode(function));
  CodePtr code = function->untag()->code_;
  ASSERT(code != StubCode::LazyCompile().ptr());
  // TODO(regis): Once we share the same stack, try to invoke directly.

#if defined(DART_DYNAMIC_RUNTIME)
    // Note: The invocation stub follows the C ABI, so we cannot pass C++ struct
    // values like ObjectPtr. In some calling conventions (IA32), ObjectPtr is
    // passed/returned different from a pointer.

    typedef uword /*ObjectPtr*/ (*invokestub)(
            uword entry_point,
            const Array& arguments_descriptor,
            const Array& arguments,
            Thread* thread);
    invokestub entrypoint_bare =
          reinterpret_cast<invokestub>(StubCode::InvokeDartCode().EntryPoint());
#endif
  ObjectPtr result;
  Exit(thread, *FP, call_top + 1, *pc);
  {
    InterpreterSetjmpBuffer buffer(this);
    if (!setjmp(buffer.buffer_)) {
#if defined(DART_DYNAMIC_RUNTIME)
      #if defined(ENABLE_DEBUG_INTERPRETER)
      logCount++;
      OS::PrintErr("%dBegin CallC %s", logCount,
                   Function::Handle(function).ToFullyQualifiedCString());
      #endif
      int count = call_top - call_base;
      Array& arguments = Array::Handle(Array::New(count));
      arguments.StoreArrayPointers(arguments.ObjectAddr(0), call_base, count);
      const Array& arguments_descriptor = Array::Handle(argdesc_);
      thread->isolate()->beginCallCompiled();
      result = static_cast<ObjectPtr>(entrypoint_bare(
          Function::Handle(function).entry_point(), arguments_descriptor,
          arguments, thread));
      thread->isolate()->endCallCompiled();
      #if defined(ENABLE_DEBUG_INTERPRETER)
      OS::PrintErr("End Call[%d]: %s", logCount,
                   Function::Handle(function).ToFullyQualifiedCString());
      logCount--;
      #endif
#endif
      ASSERT(thread->vm_tag() == VMTag::kDartInterpretedTagId);
      ASSERT(thread->execution_state() == Thread::kThreadInGenerated);
      Unexit(thread);
    } else {
      return false;
    }
  }
  // Pop args and push result.
  *SP = call_base;
  **SP = result;
  pp_ = InterpreterHelpers::FrameBytecode(*FP)->untag()->object_pool_;

  // If the result is an error (not a Dart instance), it must either be rethrown
  // (in the case of an unhandled exception) or it must be returned to the
  // caller of the interpreter to be propagated.
  if (result->IsHeapObject()) {
    const intptr_t result_cid = result->GetClassId();
    if (result_cid == kUnhandledExceptionCid) {
      (*SP)[0] = UnhandledException::RawCast(result)->untag()->exception_;
      (*SP)[1] = UnhandledException::RawCast(result)->untag()->stacktrace_;
      (*SP)[2] = 0;  // Space for result.
      Exit(thread, *FP, *SP + 3, *pc);
      NativeArguments args(thread, 2, *SP, *SP + 2);
      if (!InvokeRuntime(thread, this, DRT_ReThrow, args)) {
        return false;
      }
      UNREACHABLE();
    }
    if (IsErrorClassId(result_cid)) {
      // Unwind to entry frame.
      fp_ = *FP;
      pc_ = SavedCallerPC(fp_);
      while (!IsEntryFrameMarker(pc_)) {
        fp_ = SavedCallerFP(fp_);
        pc_ = SavedCallerPC(fp_);
      }
      // Pop entry frame.
      fp_ = SavedCallerFP(fp_);
      special_[KernelBytecode::kExceptionSpecialIndex] = result;
      return false;
    }
  }
  return true;
}

DART_FORCE_INLINE bool Interpreter::InvokeBytecode(Thread* thread,
                                                   FunctionPtr function,
                                                   ObjectPtr* call_base,
                                                   ObjectPtr* call_top,
                                                   const KBCInstr** pc,
                                                   ObjectPtr** FP,
                                                   ObjectPtr** SP) {
  ASSERT(Function::HasBytecode(function));
#if defined(DEBUG)
  if (IsTracingExecution()) {
    THR_Print("%" Pu64 " ", icount_);
    THR_Print("invoking %s\n",
              Function::Handle(function).ToFullyQualifiedCString());
  }
#endif
  ObjectPtr* callee_fp = call_top + kKBCDartFrameFixedSize;
  ASSERT(function == FrameFunction(callee_fp));
  BytecodePtr bytecode = function->untag()->bytecode_;
  callee_fp[kKBCPcMarkerSlotFromFp] = bytecode;
  callee_fp[kKBCSavedCallerPcSlotFromFp] =
      static_cast<ObjectPtr>(reinterpret_cast<uword>(*pc));
  callee_fp[kKBCSavedCallerFpSlotFromFp] =
      static_cast<ObjectPtr>(reinterpret_cast<uword>(*FP));
  pp_ = bytecode->untag()->object_pool_;
  *pc = reinterpret_cast<const KBCInstr*>(bytecode->untag()->instructions_);
//  NOT_IN_PRODUCT(pc_ = *pc);  // For the profiler.
#if defined(DART_DYNAMIC_RUNTIME) || !defined (PRODUCT)
    pc_ = *pc;
#endif
  *FP = callee_fp;
//  NOT_IN_PRODUCT(fp_ = callee_fp);  // For the profiler.
#if defined(DART_DYNAMIC_RUNTIME) || !defined (PRODUCT)
    fp_ = callee_fp;
#endif
  *SP = *FP - 1;
  return true;
}

DART_FORCE_INLINE bool Interpreter::Invoke(Thread* thread,
                                           ObjectPtr* call_base,
                                           ObjectPtr* call_top,
                                           const KBCInstr** pc,
                                           ObjectPtr** FP,
                                           ObjectPtr** SP) {
  ObjectPtr* callee_fp = call_top + kKBCDartFrameFixedSize;
  FunctionPtr function = FrameFunction(callee_fp);
#if defined(DART_DYNAMIC_RUNTIME)
  if (function == Function::null()) {
    THR_Print("Invoke: Function Null!!! Caller:%s",
              Function::Handle(FrameFunction(*FP)).ToFullyQualifiedCString());
  }
  if (Function::HasCode(function)) {
    return InvokeCompiled(thread, function, call_base, call_top, pc, FP, SP);
  }

  if (!Function::HasBytecode(function)) {
      call_top[1] = 0;  // Code result.
      call_top[2] = function;
      Exit(thread, *FP, call_top + 3, *pc);
      NativeArguments native_args(thread, 1, call_top + 2, call_top + 1);
      if (!InvokeRuntime(thread, this, DRT_CompileFunction, native_args)) {
        OS::PrintErr("%s has no code and no bytecode",
                     Function::Handle(function).ToFullyQualifiedCString());
        return false;
      }
      // Reload objects after the call which may trigger GC.
      function = Function::RawCast(call_top[2]);
  }
#if defined(ENABLE_DEBUG_INTERPRETER)
  logCount++;
  OS::PrintErr("%dBegin CallBC2 %s ", logCount,
               Function::Handle(function).ToFullyQualifiedCString());
#endif
  if (Function::HasBytecode(function)) {
    return InvokeBytecode(thread, function, call_base, call_top, pc, FP, SP);
  } else {
    OS::PrintErr("%s has no code and no bytecode",
                 Function::Handle(function).ToFullyQualifiedCString());
    Exit(thread, *FP, call_top + 1, *pc);
    InterpreterSetjmpBuffer buffer(this);
    if (!setjmp(buffer.buffer_)) {
        thread->set_vm_tag(reinterpret_cast<uword>(this));
        std::string msg =
            Function::Handle(function).ToFullyQualifiedCString();
        msg +=  " has no code and no bytecode";
        String& message = String::Handle(String::New(msg.c_str()));
        const Array& args = Array::Handle(Array::New(1));
        args.SetAt(0, message);
        Exceptions::ThrowByType(Exceptions::kUnsupported, args);
        thread->set_vm_tag(VMTag::kDartInterpretedTagId);
        Unexit(thread);
    }
    return false;
  }
#else
  for (;;) {
    if (Function::HasCode(function)) {
      return InvokeCompiled(thread, function, call_base, call_top, pc, FP, SP);
    }
    if (Function::HasBytecode(function)) {
      return InvokeBytecode(thread, function, call_base, call_top, pc, FP, SP);
    }

    // Compile the function to either generate code or load bytecode.
    call_top[1] = 0;  // Code result.
    call_top[2] = function;
    Exit(thread, *FP, call_top + 3, *pc);
    NativeArguments native_args(thread, 1, call_top + 2, call_top + 1);
    if (!InvokeRuntime(thread, this, DRT_CompileFunction, native_args)) {
      return false;
    }
    // Reload objects after the call which may trigger GC.
    function = Function::RawCast(call_top[2]);

    ASSERT(Function::HasCode(function) || Function::HasBytecode(function));
  }
#endif
}

DART_FORCE_INLINE bool Interpreter::InstanceCall(Thread* thread,
                                                 StringPtr target_name,
                                                 ObjectPtr* call_base,
                                                 ObjectPtr* top,
                                                 const KBCInstr** pc,
                                                 ObjectPtr** FP,
                                                 ObjectPtr** SP) {
  ObjectPtr null_value = Object::null();
  const intptr_t type_args_len =
      InterpreterHelpers::ArgDescTypeArgsLen(argdesc_);
  const intptr_t receiver_idx = type_args_len > 0 ? 1 : 0;

  intptr_t receiver_cid =
      InterpreterHelpers::GetClassId(call_base[receiver_idx]);

  FunctionPtr target;
  if (UNLIKELY(!lookup_cache_.Lookup(receiver_cid, target_name, argdesc_,
                                     &target))) {
    // Table lookup miss.
    top[0] = null_value;  // Clean up slot as it may be visited by GC.
    top[1] = call_base[receiver_idx];
    top[2] = target_name;
    top[3] = argdesc_;
    top[4] = null_value;  // Result slot.

    Exit(thread, *FP, top + 5, *pc);
    NativeArguments native_args(thread, 3, /* argv */ top + 1,
                                /* result */ top + 4);
    if (!InvokeRuntime(thread, this, DRT_InterpretedInstanceCallMissHandler,
                       native_args)) {
      return false;
    }

    target = static_cast<FunctionPtr>(top[4]);
    target_name = static_cast<StringPtr>(top[2]);
    argdesc_ = static_cast<ArrayPtr>(top[3]);
  }

  if (target != Function::null()) {
    lookup_cache_.Insert(receiver_cid, target_name, argdesc_, target);
    top[0] = target;
    return Invoke(thread, call_base, top, pc, FP, SP);
  }

  // The miss handler should only fail to return a function if lazy dispatchers
  // are disabled, in which case we need to call DRT_InvokeNoSuchMethod, which
  // walks the receiver appropriately in this case.
  ASSERT(!FLAG_lazy_dispatchers);

  // The receiver, name, and argument descriptor are already in the appropriate
  // places on the stack from the previous call.
  ASSERT(top[4] == null_value);

  // Allocate array of arguments.
  {
    const intptr_t argc =
        InterpreterHelpers::ArgDescArgCount(argdesc_) + receiver_idx;
    ASSERT_EQUAL(top - call_base, argc);

    top[5] = Smi::New(argc);  // length
    top[6] = null_value;      // type
    Exit(thread, *FP, top + 7, *pc);
    NativeArguments native_args(thread, 2, /* argv */ top + 5,
                                /* result */ top + 4);
    if (!InvokeRuntime(thread, this, DRT_AllocateArray, native_args)) {
      return false;
    }

    // Copy arguments into the newly allocated array.
    ArrayPtr array = Array::RawCast(top[4]);
    for (intptr_t i = 0; i < argc; i++) {
      array->untag()->data()[i] = call_base[i];
    }
  }

  {
    Exit(thread, *FP, top + 5, *pc);
    NativeArguments native_args(thread, 4, /* argv */ top + 1,
                                /* result */ top);
    if (!InvokeRuntime(thread, this, DRT_InvokeNoSuchMethod, native_args)) {
      return false;
    }

    // Pop the call args and push the result.
    ObjectPtr result = top[0];
    *SP = call_base;
    **SP = result;
    pp_ = InterpreterHelpers::FrameBytecode(*FP)->untag()->object_pool_;
  }

  return true;
}

// Note:
// All macro helpers are intended to be used only inside Interpreter::Call.

#define TRACE_INSTRUCTION

// Decode opcode and A part of the given value and dispatch to the
// corresponding bytecode handler.
#ifdef DART_HAS_COMPUTED_GOTO
#define DISPATCH_OP(val)                                                       \
  do {                                                                         \
    op = (val);                                                                \
    TRACE_INSTRUCTION                                                          \
    goto* dispatch[op];                                                        \
  } while (0)
#else
#define DISPATCH_OP(val)                                                       \
  do {                                                                         \
    op = (val);                                                                \
    TRACE_INSTRUCTION                                                          \
    goto SwitchDispatch;                                                       \
  } while (0)
#endif

// Fetch next operation from PC and dispatch.
#define DISPATCH() DISPATCH_OP(*pc)

// Load target of a jump instruction into PC.
#define LOAD_JUMP_TARGET() pc = rT

#define BYTECODE_ENTRY_LABEL(Name) bc##Name:
#define BYTECODE_WIDE_ENTRY_LABEL(Name) bc##Name##_Wide:
#define BYTECODE_IMPL_LABEL(Name) bc##Name##Impl:
#define GOTO_BYTECODE_IMPL(Name) goto bc##Name##Impl;

// Define entry point that handles bytecode Name with the given operand format.
#define BYTECODE(Name, Operands) BYTECODE_HEADER_##Operands(Name)

// Helpers to decode common instruction formats. Used in conjunction with
// BYTECODE() macro.

#define BYTECODE_HEADER_0(Name)                                                \
  BYTECODE_ENTRY_LABEL(Name)                                                   \
  pc += 1;

#define BYTECODE_HEADER_A(Name)                                                \
  uint32_t rA;                                                                 \
  USE(rA);                                                                     \
  BYTECODE_ENTRY_LABEL(Name)                                                   \
  rA = pc[1];                                                                  \
  pc += 2;

#define BYTECODE_HEADER_D(Name)                                                \
  uint32_t rD;                                                                 \
  USE(rD);                                                                     \
  BYTECODE_WIDE_ENTRY_LABEL(Name)                                              \
  rD = static_cast<uint32_t>(pc[1]) | (static_cast<uint32_t>(pc[2]) << 8) |    \
       (static_cast<uint32_t>(pc[3]) << 16) |                                  \
       (static_cast<uint32_t>(pc[4]) << 24);                                   \
  pc += 5;                                                                     \
  GOTO_BYTECODE_IMPL(Name);                                                    \
  BYTECODE_ENTRY_LABEL(Name)                                                   \
  rD = pc[1];                                                                  \
  pc += 2;                                                                     \
  BYTECODE_IMPL_LABEL(Name)

#define BYTECODE_HEADER_X(Name)                                                \
  int32_t rX;                                                                  \
  USE(rX);                                                                     \
  BYTECODE_WIDE_ENTRY_LABEL(Name)                                              \
  rX = static_cast<int32_t>(static_cast<uint32_t>(pc[1]) |                     \
                            (static_cast<uint32_t>(pc[2]) << 8) |              \
                            (static_cast<uint32_t>(pc[3]) << 16) |             \
                            (static_cast<uint32_t>(pc[4]) << 24));             \
  pc += 5;                                                                     \
  GOTO_BYTECODE_IMPL(Name);                                                    \
  BYTECODE_ENTRY_LABEL(Name)                                                   \
  rX = static_cast<int8_t>(pc[1]);                                             \
  pc += 2;                                                                     \
  BYTECODE_IMPL_LABEL(Name)

#define BYTECODE_HEADER_T(Name)                                                \
  const KBCInstr* rT;                                                          \
  USE(rT);                                                                     \
  BYTECODE_WIDE_ENTRY_LABEL(Name)                                              \
  rT = pc + (static_cast<int32_t>((static_cast<uint32_t>(pc[1]) << 8) |        \
                                  (static_cast<uint32_t>(pc[2]) << 16) |       \
                                  (static_cast<uint32_t>(pc[3]) << 24)) >>     \
             8);                                                               \
  pc += 4;                                                                     \
  GOTO_BYTECODE_IMPL(Name);                                                    \
  BYTECODE_ENTRY_LABEL(Name)                                                   \
  rT = pc + static_cast<int8_t>(pc[1]);                                        \
  pc += 2;                                                                     \
  BYTECODE_IMPL_LABEL(Name)

#define BYTECODE_HEADER_A_E(Name)                                              \
  uint32_t rA, rE;                                                             \
  USE(rA);                                                                     \
  USE(rE);                                                                     \
  BYTECODE_WIDE_ENTRY_LABEL(Name)                                              \
  rA = pc[1];                                                                  \
  rE = static_cast<uint32_t>(pc[2]) | (static_cast<uint32_t>(pc[3]) << 8) |    \
       (static_cast<uint32_t>(pc[4]) << 16) |                                  \
       (static_cast<uint32_t>(pc[5]) << 24);                                   \
  pc += 6;                                                                     \
  GOTO_BYTECODE_IMPL(Name);                                                    \
  BYTECODE_ENTRY_LABEL(Name)                                                   \
  rA = pc[1];                                                                  \
  rE = pc[2];                                                                  \
  pc += 3;                                                                     \
  BYTECODE_IMPL_LABEL(Name)

#define BYTECODE_HEADER_A_Y(Name)                                              \
  uint32_t rA;                                                                 \
  int32_t rY;                                                                  \
  USE(rA);                                                                     \
  USE(rY);                                                                     \
  BYTECODE_WIDE_ENTRY_LABEL(Name)                                              \
  rA = pc[1];                                                                  \
  rY = static_cast<int32_t>(static_cast<uint32_t>(pc[2]) |                     \
                            (static_cast<uint32_t>(pc[3]) << 8) |              \
                            (static_cast<uint32_t>(pc[4]) << 16) |             \
                            (static_cast<uint32_t>(pc[5]) << 24));             \
  pc += 6;                                                                     \
  GOTO_BYTECODE_IMPL(Name);                                                    \
  BYTECODE_ENTRY_LABEL(Name)                                                   \
  rA = pc[1];                                                                  \
  rY = static_cast<int8_t>(pc[2]);                                             \
  pc += 3;                                                                     \
  BYTECODE_IMPL_LABEL(Name)

#define BYTECODE_HEADER_D_F(Name)                                              \
  uint32_t rD, rF;                                                             \
  USE(rD);                                                                     \
  USE(rF);                                                                     \
  BYTECODE_WIDE_ENTRY_LABEL(Name)                                              \
  rD = static_cast<uint32_t>(pc[1]) | (static_cast<uint32_t>(pc[2]) << 8) |    \
       (static_cast<uint32_t>(pc[3]) << 16) |                                  \
       (static_cast<uint32_t>(pc[4]) << 24);                                   \
  rF = pc[5];                                                                  \
  pc += 6;                                                                     \
  GOTO_BYTECODE_IMPL(Name);                                                    \
  BYTECODE_ENTRY_LABEL(Name)                                                   \
  rD = pc[1];                                                                  \
  rF = pc[2];                                                                  \
  pc += 3;                                                                     \
  BYTECODE_IMPL_LABEL(Name)

#define BYTECODE_HEADER_A_B_C(Name)                                            \
  uint32_t rA, rB, rC;                                                         \
  USE(rA);                                                                     \
  USE(rB);                                                                     \
  USE(rC);                                                                     \
  BYTECODE_ENTRY_LABEL(Name)                                                   \
  rA = pc[1];                                                                  \
  rB = pc[2];                                                                  \
  rC = pc[3];                                                                  \
  pc += 4;

#define HANDLE_EXCEPTION                                                       \
  do {                                                                         \
    goto HandleException;                                                      \
  } while (0)

#define HANDLE_RETURN                                                          \
  do {                                                                         \
    pp_ = InterpreterHelpers::FrameBytecode(FP)->untag()->object_pool_;        \
  } while (0)

// Runtime call helpers: handle invocation and potential exception after return.
#define INVOKE_RUNTIME(Func, Args)                                             \
  if (!InvokeRuntime(thread, this, Func, Args)) {                              \
    HANDLE_EXCEPTION;                                                          \
  } else {                                                                     \
    HANDLE_RETURN;                                                             \
  }

#define INVOKE_NATIVE(Wrapper, Func, Args)                                     \
  if (!InvokeNative(thread, this, Wrapper, Func, Args)) {                      \
    HANDLE_EXCEPTION;                                                          \
  } else {                                                                     \
    HANDLE_RETURN;                                                             \
  }

// #define LOAD_CONSTANT(index) (pp_->ptr()->data()[(index)].raw_obj_)
#define LOAD_CONSTANT(index) (pp_->untag()->data()[(index)].raw_obj_)

#define UNBOX_INT64(value, obj, selector)                                      \
  int64_t value;                                                               \
  {                                                                            \
    word raw_value = static_cast<word>(obj);                                   \
    if (LIKELY((raw_value & kSmiTagMask) == kSmiTag)) {                        \
      value = raw_value >> kSmiTagShift;                                       \
    } else {                                                                   \
      if (UNLIKELY(obj == null_value)) {                                       \
        SP[0] = selector.ptr();                                                \
        goto ThrowNullError;                                                   \
      }                                                                        \
      value = Integer::GetInt64Value(RAW_CAST(Integer, obj));                  \
    }                                                                          \
  }

#define BOX_INT64_RESULT(result)                                               \
  if (LIKELY(Smi::IsValid(result))) {                                          \
    SP[0] = Smi::New(static_cast<intptr_t>(result));                           \
  } else if (!AllocateMint(thread, result, pc, FP, SP)) {                      \
    HANDLE_EXCEPTION;                                                          \
  }                                                                            \
  ASSERT(Integer::GetInt64Value(RAW_CAST(Integer, SP[0])) == result);

#define UNBOX_DOUBLE(value, obj, selector)                                     \
  double value;                                                                \
  {                                                                            \
    if (UNLIKELY(obj == null_value)) {                                         \
      SP[0] = selector.ptr();                                                  \
      goto ThrowNullError;                                                     \
    }                                                                          \
    value = Double::RawCast(obj)->untag()->value_;                             \
  }

#define BOX_DOUBLE_RESULT(result)                                              \
  if (!AllocateDouble(thread, result, pc, FP, SP)) {                           \
    HANDLE_EXCEPTION;                                                          \
  }                                                                            \
  ASSERT(Utils::DoublesBitEqual(Double::RawCast(SP[0])->untag()->value_,       \
                                result));


#ifdef PRODUCT
#define DEBUG_CHECK
#else
// The DEBUG_CHECK macro must only be called from bytecodes listed in
// KernelBytecode::IsDebugCheckedOpcode.
#define DEBUG_CHECK
#endif  // PRODUCT

bool Interpreter::CopyParameters(Thread* thread,
                                 const KBCInstr** pc,
                                 ObjectPtr** FP,
                                 ObjectPtr** SP,
                                 const intptr_t num_fixed_params,
                                 const intptr_t num_opt_pos_params,
                                 const intptr_t num_opt_named_params) {
  const intptr_t min_num_pos_args = num_fixed_params;
  const intptr_t max_num_pos_args = num_fixed_params + num_opt_pos_params;

  // Decode arguments descriptor.
  const intptr_t arg_count = InterpreterHelpers::ArgDescArgCount(argdesc_);
  const intptr_t pos_count = InterpreterHelpers::ArgDescPosCount(argdesc_);
  const intptr_t named_count = (arg_count - pos_count);

  // Check that got the right number of positional parameters.
  if ((min_num_pos_args > pos_count) || (pos_count > max_num_pos_args)) {
    return false;
  }

  // Copy all passed position arguments.
  ObjectPtr* first_arg = FrameArguments(*FP, arg_count);
  memmove(*FP, first_arg, pos_count * kWordSize);

  if (num_opt_named_params != 0) {
    // This is a function with named parameters.
    // Walk the list of named parameters and their
    // default values encoded as pairs of LoadConstant instructions that
    // follows the entry point and find matching values via arguments
    // descriptor.
    ObjectPtr* argdesc_data = argdesc_->untag()->data();

    intptr_t i = 0;  // argument position
    intptr_t j = 0;  // parameter position
    while ((j < num_opt_named_params) && (i < named_count)) {
      // Fetch formal parameter information: name, default value, target slot.
      const KBCInstr* load_name = *pc;
      const KBCInstr* load_value = KernelBytecode::Next(load_name);
      *pc = KernelBytecode::Next(load_value);
      ASSERT(KernelBytecode::IsLoadConstantOpcode(load_name));
      ASSERT(KernelBytecode::IsLoadConstantOpcode(load_value));
      const uint8_t reg = KernelBytecode::DecodeA(load_name);
      ASSERT(reg == KernelBytecode::DecodeA(load_value));

      StringPtr name = static_cast<StringPtr>(
          LOAD_CONSTANT(KernelBytecode::DecodeE(load_name)));
      if (name == argdesc_data[ArgumentsDescriptor::name_index(i)]) {
        // Parameter was passed. Fetch passed value.
        const intptr_t arg_index = Smi::Value(static_cast<SmiPtr>(
            argdesc_data[ArgumentsDescriptor::position_index(i)]));
        (*FP)[reg] = first_arg[arg_index];
        ++i;  // Consume passed argument.
      } else {
        // Parameter was not passed. Fetch default value.
        (*FP)[reg] = LOAD_CONSTANT(KernelBytecode::DecodeE(load_value));
      }
      ++j;  // Next formal parameter.
    }

    // If we have unprocessed formal parameters then initialize them all
    // using default values.
    while (j < num_opt_named_params) {
      const KBCInstr* load_name = *pc;
      const KBCInstr* load_value = KernelBytecode::Next(load_name);
      *pc = KernelBytecode::Next(load_value);
      ASSERT(KernelBytecode::IsLoadConstantOpcode(load_name));
      ASSERT(KernelBytecode::IsLoadConstantOpcode(load_value));
      const uint8_t reg = KernelBytecode::DecodeA(load_name);
      ASSERT(reg == KernelBytecode::DecodeA(load_value));

      (*FP)[reg] = LOAD_CONSTANT(KernelBytecode::DecodeE(load_value));
      ++j;
    }

    // If we have unprocessed passed arguments that means we have mismatch
    // between formal parameters and concrete arguments. This can only
    // occur if the current function is a closure.
    if (i < named_count) {
      return false;
    }

    // SP points past copied arguments.
    *SP = *FP + num_fixed_params + num_opt_named_params - 1;
  } else {
    ASSERT(num_opt_pos_params != 0);
    if (named_count != 0) {
      // Function can't have both named and optional positional parameters.
      // This kind of mismatch can only occur if the current function
      // is a closure.
      return false;
    }

    // Process the list of default values encoded as a sequence of
    // LoadConstant instructions after EntryOpt bytecode.
    // Execute only those that correspond to parameters that were not passed.
    for (intptr_t i = num_fixed_params; i < pos_count; ++i) {
      ASSERT(KernelBytecode::IsLoadConstantOpcode(*pc));
      *pc = KernelBytecode::Next(*pc);
    }
    for (intptr_t i = pos_count; i < max_num_pos_args; ++i) {
      const KBCInstr* load_value = *pc;
      *pc = KernelBytecode::Next(load_value);
      ASSERT(KernelBytecode::IsLoadConstantOpcode(load_value));
      ASSERT(KernelBytecode::DecodeA(load_value) == i);
      (*FP)[i] = LOAD_CONSTANT(KernelBytecode::DecodeE(load_value));
    }

    // SP points past the last copied parameter.
    *SP = *FP + max_num_pos_args - 1;
  }

  return true;
}

bool Interpreter::AssertAssignable(Thread* thread,
                                   const KBCInstr* pc,
                                   ObjectPtr* FP,
                                   ObjectPtr* call_top,
                                   ObjectPtr* args,
                                   SubtypeTestCachePtr cache) {
  ObjectPtr null_value = Object::null();
  if (cache != null_value) {
    InstancePtr instance = static_cast<InstancePtr>(args[0]);
    TypeArgumentsPtr instantiator_type_arguments =
        static_cast<TypeArgumentsPtr>(args[2]);
    TypeArgumentsPtr function_type_arguments =
        static_cast<TypeArgumentsPtr>(args[3]);

    const intptr_t cid = InterpreterHelpers::GetClassId(instance);

    TypeArgumentsPtr instance_type_arguments =
        static_cast<TypeArgumentsPtr>(null_value);
    ObjectPtr instance_cid_or_function;

    TypeArgumentsPtr parent_function_type_arguments;
    TypeArgumentsPtr delayed_function_type_arguments;
    if (cid == kClosureCid) {
      ClosurePtr closure = static_cast<ClosurePtr>(instance);
      instance_type_arguments = closure->untag()->instantiator_type_arguments_;
      parent_function_type_arguments =
          closure->untag()->function_type_arguments_;
      delayed_function_type_arguments =
          closure->untag()->delayed_type_arguments_;
      instance_cid_or_function = closure->untag()->function_;
    } else {
      instance_cid_or_function = Smi::New(cid);

      ClassPtr instance_class =
          thread->isolate()->group()->class_table()->At(cid);
      if (instance_class->untag()->num_type_arguments_ < 0) {
        goto AssertAssignableCallRuntime;
      } else if (instance_class->untag()->num_type_arguments_ > 0) {
        instance_type_arguments = reinterpret_cast<TypeArgumentsPtr*>(
            instance->untag())[instance_class->untag()
                                 ->host_type_arguments_field_offset_in_words_];
      }
      parent_function_type_arguments =
          static_cast<TypeArgumentsPtr>(null_value);
      delayed_function_type_arguments =
          static_cast<TypeArgumentsPtr>(null_value);
    }

    for (ObjectPtr* entries = cache->untag()->cache_->untag()->data();
         entries[0] != null_value;
         entries += SubtypeTestCache::kTestEntryLength) {
      if ((entries[SubtypeTestCache::kInstanceCidOrSignature] ==
           instance_cid_or_function) &&
          (entries[SubtypeTestCache::kInstanceTypeArguments] ==
           instance_type_arguments) &&
          (entries[SubtypeTestCache::kInstantiatorTypeArguments] ==
           instantiator_type_arguments) &&
          (entries[SubtypeTestCache::kFunctionTypeArguments] ==
           function_type_arguments) &&
          (entries[SubtypeTestCache::kInstanceParentFunctionTypeArguments] ==
           parent_function_type_arguments) &&
          (entries[SubtypeTestCache::kInstanceDelayedFunctionTypeArguments] ==
           delayed_function_type_arguments)) {
        if (Bool::True().ptr() == entries[SubtypeTestCache::kTestResult]) {
          return true;
        } else {
          break;
        }
      }
    }
  }

AssertAssignableCallRuntime:
  // args[0]: Instance.
  // args[1]: Type.
  // args[2]: Instantiator type args.
  // args[3]: Function type args.
  // args[4]: Name.
  args[5] = cache;
  args[6] = Smi::New(kTypeCheckFromInline);
  args[7] = 0;  // Unused result.
  Exit(thread, FP, args + 8, pc);
  NativeArguments native_args(thread, 7, args, args + 7);
  return InvokeRuntime(thread, this, DRT_TypeCheck, native_args);
}

template <bool is_getter>
bool Interpreter::AssertAssignableField(Thread* thread,
                                        const KBCInstr* pc,
                                        ObjectPtr* FP,
                                        ObjectPtr* SP,
                                        ObjectPtr instance,
                                        FieldPtr field,
                                        ObjectPtr value) {
  AbstractTypePtr field_type = field->untag()->type_;
  // Perform type test of value if field type is not one of dynamic, object,
  // or void, and if the value is not null.
  if (field_type->GetClassId() == kTypeCid) {
    classid_t cid = Type::RawCast(field_type)->untag()->type_class_id_;
    // TODO(regis): Revisit shortcut for NNBD.
    if (cid == kDynamicCid || cid == kInstanceCid || cid == kVoidCid) {
      return true;
    }
  }
  ObjectPtr null_value = Object::null();
  if (value == null_value) {
    // TODO(regis): Revisit null shortcut for NNBD.
    return true;
  }

  Exit(thread, FP, SP + 1, pc);
  const Object& obj = Object::Handle(value);
  Unexit(thread);
  if (obj.GetClassId() == kNeverCid) {
    return true;
  }

  SubtypeTestCachePtr cache = field->untag()->type_test_cache_;
  if (UNLIKELY(cache == null_value)) {
    // Allocate new cache.
    SP[1] = instance;    // Preserve.
    SP[2] = field;       // Preserve.
    SP[3] = value;       // Preserve.
    SP[4] = null_value;  // Result slot.

    Exit(thread, FP, SP + 5, pc);
    if (!InvokeRuntime(thread, this, DRT_AllocateSubtypeTestCache,
                       NativeArguments(thread, 0, /* argv */ SP + 4,
                                       /* retval */ SP + 4))) {
      return false;
    }

    // Reload objects after the call which may trigger GC.
    instance = static_cast<ObjectPtr>(SP[1]);
    field = static_cast<FieldPtr>(SP[2]);
    value = static_cast<ObjectPtr>(SP[3]);
    cache = static_cast<SubtypeTestCachePtr>(SP[4]);
    field_type = field->untag()->type_;
    field->untag()->type_test_cache_ = cache;
  }

  // Push arguments of type test.
  SP[1] = value;
  SP[2] = field_type;
  // Provide type arguments of instance as instantiator.
  SP[3] = InterpreterHelpers::GetTypeArguments(thread, instance);
  SP[4] = null_value;  // Implicit setters cannot be generic.
  SP[5] = is_getter ? Symbols::FunctionResult().ptr() : field->untag()->name_;
  return AssertAssignable(thread, pc, FP, /* call_top */ SP + 5,
                          /* args */ SP + 1, cache);
}

ObjectPtr Interpreter::Call(const Function& function,
                            const Array& arguments_descriptor,
                            const Array& arguments,
                            Thread* thread) {
  return Call(function.ptr(), arguments_descriptor.ptr(), arguments.Length(),
              arguments.untag()->data(), thread);
}

// Allocate a _Mint for the given int64_t value and puts it into SP[0].
// Returns false on exception.
DART_NOINLINE bool Interpreter::AllocateMint(Thread* thread,
                                             int64_t value,
                                             const KBCInstr* pc,
                                             ObjectPtr* FP,
                                             ObjectPtr* SP) {
  ASSERT(!Smi::IsValid(value));
  MintPtr result;
  if (TryAllocate(thread, kMintCid, Mint::InstanceSize(),
                  reinterpret_cast<ObjectPtr*>(&result))) {
    result->untag()->value_ = value;
    SP[0] = result;
    return true;
  } else {
    SP[0] = 0;  // Space for the result.
    // Class object.
    SP[1] = thread->isolate()->group()->object_store()->mint_class();
    SP[2] = Object::null();                                   // Type arguments.
    Exit(thread, FP, SP + 3, pc);
    NativeArguments args(thread, 2, SP + 1, SP);
    if (!InvokeRuntime(thread, this, DRT_AllocateObject, args)) {
      return false;
    }
    static_cast<MintPtr>(SP[0])->untag()->value_ = value;
    return true;
  }
}

// Allocate a _Double for the given double value and put it into SP[0].
// Returns false on exception.
DART_NOINLINE bool Interpreter::AllocateDouble(Thread* thread,
                                               double value,
                                               const KBCInstr* pc,
                                               ObjectPtr* FP,
                                               ObjectPtr* SP) {
  DoublePtr result;
  if (TryAllocate(thread, kDoubleCid, Double::InstanceSize(),
                  reinterpret_cast<ObjectPtr*>(&result))) {
    result->untag()->value_ = value;
    SP[0] = result;
    return true;
  } else {
    SP[0] = 0;  // Space for the result.
    SP[1] = thread->isolate()->group()->object_store()->double_class();
    SP[2] = Object::null();  // Type arguments.
    Exit(thread, FP, SP + 3, pc);
    NativeArguments args(thread, 2, SP + 1, SP);
    if (!InvokeRuntime(thread, this, DRT_AllocateObject, args)) {
      return false;
    }
    Double::RawCast(SP[0])->untag()->value_ = value;
    return true;
  }
}

// Allocate a _Float32x4 for the given simd value and put it into SP[0].
// Returns false on exception.
DART_NOINLINE bool Interpreter::AllocateFloat32x4(Thread* thread,
                                                  simd128_value_t value,
                                                  const KBCInstr* pc,
                                                  ObjectPtr* FP,
                                                  ObjectPtr* SP) {
  Float32x4Ptr result;
  if (TryAllocate(thread, kFloat32x4Cid, Float32x4::InstanceSize(),
                  reinterpret_cast<ObjectPtr*>(&result))) {
    value.writeTo(result->untag()->value_);
    SP[0] = result;
    return true;
  } else {
    SP[0] = 0;  // Space for the result.
    SP[1] = thread->isolate()->group()->object_store()->float32x4_class();
    SP[2] = Object::null();  // Type arguments.
    Exit(thread, FP, SP + 3, pc);
    NativeArguments args(thread, 2, SP + 1, SP);
    if (!InvokeRuntime(thread, this, DRT_AllocateObject, args)) {
      return false;
    }
    value.writeTo(Float32x4::RawCast(SP[0])->untag()->value_);
    return true;
  }
}

// Allocate _Float64x2 box for the given simd value and put it into SP[0].
// Returns false on exception.
DART_NOINLINE bool Interpreter::AllocateFloat64x2(Thread* thread,
                                                  simd128_value_t value,
                                                  const KBCInstr* pc,
                                                  ObjectPtr* FP,
                                                  ObjectPtr* SP) {
  Float64x2Ptr result;
  if (TryAllocate(thread, kFloat64x2Cid, Float64x2::InstanceSize(),
                  reinterpret_cast<ObjectPtr*>(&result))) {
    value.writeTo(result->untag()->value_);
    SP[0] = result;
    return true;
  } else {
    SP[0] = 0;  // Space for the result.
    SP[1] = thread->isolate()->group()->object_store()->float64x2_class();
    SP[2] = Object::null();  // Type arguments.
    Exit(thread, FP, SP + 3, pc);
    NativeArguments args(thread, 2, SP + 1, SP);
    if (!InvokeRuntime(thread, this, DRT_AllocateObject, args)) {
      return false;
    }
    value.writeTo(Float64x2::RawCast(SP[0])->untag()->value_);
    return true;
  }
}

// Allocate a _List with the given type arguments and length and put it into
// SP[0]. Returns false on exception.
bool Interpreter::AllocateArray(Thread* thread,
                                TypeArgumentsPtr type_args,
                                ObjectPtr length_object,
                                const KBCInstr* pc,
                                ObjectPtr* FP,
                                ObjectPtr* SP) {
  if (LIKELY(!length_object->IsHeapObject())) {
    const intptr_t length = Smi::Value(Smi::RawCast(length_object));
    if (LIKELY(Array::IsValidLength(length))) {
      ArrayPtr result;
      if (TryAllocate(thread, kArrayCid, Array::InstanceSize(length),
                      reinterpret_cast<ObjectPtr*>(&result))) {
        result->untag()->type_arguments_ = type_args;
        result->untag()->length_ = Smi::New(length);
        for (intptr_t i = 0; i < length; i++) {
          result->untag()->data()[i] = Object::null();
        }
        SP[0] = result;
        return true;
      }
    }
  }

  SP[0] = 0;  // Space for the result;
  SP[1] = length_object;
  SP[2] = type_args;
  Exit(thread, FP, SP + 3, pc);
  NativeArguments args(thread, 2, SP + 1, SP);
  return InvokeRuntime(thread, this, DRT_AllocateArray, args);
}

// Allocate a _Context with the given length and put it into SP[0].
// Returns false on exception.
bool Interpreter::AllocateContext(Thread* thread,
                                  intptr_t num_context_variables,
                                  const KBCInstr* pc,
                                  ObjectPtr* FP,
                                  ObjectPtr* SP) {
  ContextPtr result;
  if (TryAllocate(thread, kContextCid,
                  Context::InstanceSize(num_context_variables),
                  reinterpret_cast<ObjectPtr*>(&result))) {
    result->untag()->num_variables_ = num_context_variables;
    ObjectPtr null_value = Object::null();
    result->untag()->parent_ = static_cast<ContextPtr>(null_value);
    for (intptr_t i = 0; i < num_context_variables; i++) {
      result->untag()->data()[i] = null_value;
    }
    SP[0] = result;
    return true;
  } else {
    SP[0] = 0;  // Space for the result.
    SP[1] = Smi::New(num_context_variables);
    Exit(thread, FP, SP + 2, pc);
    NativeArguments args(thread, 1, SP + 1, SP);
    return InvokeRuntime(thread, this, DRT_AllocateContext, args);
  }
}

// Allocate a _Closure and put it into SP[0].
// Returns false on exception.
bool Interpreter::AllocateClosure(Thread* thread,
                                  const KBCInstr* pc,
                                  ObjectPtr* FP,
                                  ObjectPtr* SP) {
  const intptr_t instance_size = Closure::InstanceSize();
  ClosurePtr result;
  if (TryAllocate(thread, kClosureCid, instance_size,
                  reinterpret_cast<ObjectPtr*>(&result))) {
    uword start = UntaggedObject::ToAddr(result);
    ObjectPtr null_value = Object::null();
    for (intptr_t offset = sizeof(UntaggedInstance); offset < instance_size;
         offset += kWordSize) {
      *reinterpret_cast<ObjectPtr*>(start + offset) = null_value;
    }
    SP[0] = result;
    return true;
  } else {
    SP[0] = 0;  // Space for the result.
    SP[1] = thread->isolate()->group()->object_store()->closure_class();
    SP[2] = Object::null();  // Type arguments.
    Exit(thread, FP, SP + 3, pc);
    NativeArguments args(thread, 2, SP + 1, SP);
    return InvokeRuntime(thread, this, DRT_AllocateObject, args);
  }
}

ObjectPtr Interpreter::Call(FunctionPtr function,
                            ArrayPtr argdesc,
                            intptr_t argc,
                            ObjectPtr const* argv,
                            Thread* thread) {
#if defined(DART_DYNAMIC_RUNTIME)
  // Implicit closure generated by bytecode. The code inside is machine code.
  if (Function::Handle(function).kind() ==
      UntaggedFunction::kImplicitClosureFunction) {
    Function& functionHandle = Function::Handle(function);
    if (Function::HasCode(functionHandle.parent_function())) {
      // Note: The invocation stub follows the C ABI, so we cannot pass C++
      // struct values like ObjectPtr. In some calling conventions (IA32),
      // ObjectPtr is passed/returned different from a pointer.
      typedef uword /*ObjectPtr*/ (*invokestub)(const Code& target_code,
                                              const Array& arguments_descriptor,
                                              const Array& arguments,
                                              Thread* thread);
      invokestub entrypoint =
          reinterpret_cast<invokestub>(StubCode::InvokeDartCode().EntryPoint());
      Array& arguments = Array::Handle();
      if (!functionHandle.is_static()) {
        // non static function, update the receiver id
        const intptr_t type_args_len =
                InterpreterHelpers::ArgDescTypeArgsLen(argdesc);
        const intptr_t receiver_idx = type_args_len > 0 ? 1 : 0;
        const intptr_t arg_count = argc < 0 ? -argc : argc;
        arguments = Array::New(arg_count);
        for (intptr_t i = 0; i < arg_count; i++) {
          arguments.StoreArrayPointer(arguments.ObjectAddr(i),
                                      argv[argc < 0 ? -i : i]);
        }
        Object& obj = Object::Handle(arguments.At(receiver_idx));
        if (obj.IsClosure()) {
          const Closure& closure = Closure::Cast(obj);
          ObjectPtr instanceObj = Context::Handle(closure.context()).At(0);
          if (closure.function() == function &&
              instanceObj != arguments.At(receiver_idx)) {
            arguments.SetAt(receiver_idx, Object::Handle(instanceObj));
#if defined(ENABLE_DEBUG_INTERPRETER)
            OS::PrintErr("ImplicitClosureFunction fix1 instance");
#endif
          }
        }
      } else {
        // static function
        const intptr_t type_args_len =
                InterpreterHelpers::ArgDescTypeArgsLen(argdesc);
        const intptr_t receiver_idx = type_args_len > 0 ? 1 : 0;
        const intptr_t arg_count = argc < 0 ? -argc : argc;
        arguments = Array::New(arg_count-1);
        int j = 0;
        for (intptr_t i = 0; i < arg_count; i++) {
          if (i == receiver_idx) {
            continue;
          }
          arguments.StoreArrayPointer(arguments.ObjectAddr(j),
                                      argv[argc < 0 ? -i : i]);
          j++;
        }
        ArgumentsDescriptor ads = ArgumentsDescriptor(Array::Handle(argdesc));
        intptr_t namedCount =  ads.NamedCount();
        if (namedCount > 0) {
          Array& namesArr = Array::Handle(Array::New(namedCount));
          for (int j=0; j < namedCount; j++) {
            namesArr.SetAt(j, String::Handle(ads.NameAt(j)));
          }
          argdesc = ArgumentsDescriptor::NewBoxed(type_args_len, arg_count-1,
                                                  namesArr);
        } else {
          argdesc = ArgumentsDescriptor::NewBoxed(type_args_len, arg_count-1);
        }
  #if defined(ENABLE_DEBUG_INTERPRETER)
        OS::PrintErr("ImplicitClosureFunction fix1 static argcount");
  #endif
      }

      const Code& wrappercode = Code::Handle(
          Function::CurrentCodeOf(functionHandle.parent_function()));
      const Array& arguments_descriptor = Array::Handle(argdesc);
      thread->isolate()->beginCallCompiled();
      ObjectPtr result = static_cast<ObjectPtr>(entrypoint(wrappercode,
                                                           arguments_descriptor,
                                                           arguments, thread));
      thread->isolate()->endCallCompiled();
      return result;
    }
  }
#if defined(ENABLE_DEBUG_INTERPRETER)
  logCount++;
  OS::PrintErr("%dBegin CallBC1 %s",
               logCount, Function::Handle(function).ToFullyQualifiedCString());
#endif
#endif
  // Interpreter state (see constants_kbc.h for high-level overview).
  const KBCInstr* pc;  // Program Counter: points to the next op to execute.
  ObjectPtr* FP;       // Frame Pointer.
  ObjectPtr* SP;       // Stack Pointer.

  uint32_t op;  // Currently executing op.

  bool reentering = fp_ != NULL;
  if (!reentering) {
    fp_ = reinterpret_cast<ObjectPtr*>(stack_base_);
  }

  // Setup entry frame:
  //
  //                        ^
  //                        |  previous Dart frames
  //                        |
  //       | ........... | -+
  // fp_ > | exit fp_    |     saved top_exit_frame_info
  //       | argdesc_    |     saved argdesc_ (for reentering interpreter)
  //       | pp_         |     saved pp_ (for reentering interpreter)
  //       | arg 0       | -+
  //       | arg 1       |  |
  //         ...            |
  //                         > incoming arguments
  //                        |
  //       | arg argc-1  | -+
  //       | function    | -+
  //       | code        |  |
  //       | caller PC   | ---> special fake PC marking an entry frame
  //  SP > | fp_         |  |
  //  FP > | ........... |   > normal Dart frame (see stack_frame_kbc.h)
  //                        |
  //                        v
  //
  // A negative argc indicates reverse memory order of arguments.
  const intptr_t arg_count = argc < 0 ? -argc : argc;
  FP = fp_ + kKBCEntrySavedSlots + arg_count + kKBCDartFrameFixedSize;
  SP = FP - 1;
#if defined(DART_DYNAMIC_RUNTIME)
    // can not be moved, which will cause GC crash
    if (!Function::HasBytecode(function)) {
        kernel::BytecodeReader::ReadFunctionBytecode(thread,
                                                   Function::Handle(function));
    }
    if (!Function::HasBytecode(function)) {
        THR_Print("%s has no code and no bytecode",
                Function::Handle(function).ToFullyQualifiedCString());
        UNREACHABLE();
    }
    // update the arc for implicit closure
    bool isImplicitClosureFunction = false;
    bool isStaticImplicitClosureFunction = false;
    if (Function::Handle(function).kind() ==
          UntaggedFunction::kImplicitClosureFunction) {
        isImplicitClosureFunction = true;
        Function& functionHandle = Function::Handle(function);
        if (functionHandle.is_static()) {
            // Add a parameter closure
            const intptr_t type_args_len =
                    InterpreterHelpers::ArgDescTypeArgsLen(argdesc);
            ArgumentsDescriptor ads =
                    ArgumentsDescriptor(Array::Handle(argdesc));
            intptr_t namedCount =  ads.NamedCount();
            if (namedCount > 0) {
                Array& namesArr = Array::Handle(Array::New(namedCount));
                for (int j = 0; j < namedCount; j++) {
                    namesArr.SetAt(j, String::Handle(ads.NameAt(j)));
                }
                argdesc = ArgumentsDescriptor::NewBoxed(type_args_len,
                                                        arg_count-1, namesArr);
            } else {
                argdesc = ArgumentsDescriptor::NewBoxed(type_args_len,
                                                         arg_count-1);
            }
            isStaticImplicitClosureFunction = true;
        }
    }
    // For gc test
    // thread->isolate()->heap()->CollectAllGarbage();
#endif
  // Save outer top_exit_frame_info, current argdesc, and current pp.
  fp_[kKBCExitLinkSlotFromEntryFp] =
      static_cast<ObjectPtr>(thread->top_exit_frame_info());
  thread->set_top_exit_frame_info(0);
  fp_[kKBCSavedArgDescSlotFromEntryFp] = static_cast<ObjectPtr>(argdesc_);
  fp_[kKBCSavedPpSlotFromEntryFp] = static_cast<ObjectPtr>(pp_);

  // Copy arguments and setup the Dart frame.
  for (intptr_t i = 0; i < arg_count; i++) {
    fp_[kKBCEntrySavedSlots + i] = argv[argc < 0 ? -i : i];
  }
#if defined(DART_DYNAMIC_RUNTIME)
    // update the args for implicit closure
    if (isImplicitClosureFunction) {
      const intptr_t type_args_len =
              InterpreterHelpers::ArgDescTypeArgsLen(argdesc);
      const intptr_t receiver_idx = type_args_len > 0 ? 1 : 0;
      if (!isStaticImplicitClosureFunction) {
        // update the receiver for non static function
        Object& obj = Object::Handle(fp_[kKBCEntrySavedSlots+receiver_idx]);
        if (obj.IsClosure()) {
          const Closure& closure = Closure::Cast(obj);
          ObjectPtr instanceObj = Context::Handle(closure.context()).At(0);
          if (closure.function() == function &&
              instanceObj != fp_[kKBCEntrySavedSlots+receiver_idx]) {
            fp_[kKBCEntrySavedSlots+receiver_idx] = instanceObj;
#if defined(ENABLE_DEBUG_INTERPRETER)
            OS::PrintErr("ImplicitClosureFunction fix2 instance");
#endif
          }
        }
      } else {
        // An additional parameter(closure)
        if (receiver_idx == 1) {
          ObjectPtr obj = fp_[kKBCEntrySavedSlots];
          fp_[kKBCEntrySavedSlots] = fp_[kKBCEntrySavedSlots+1];
          fp_[kKBCEntrySavedSlots+1] = obj;
        }
#if defined(ENABLE_DEBUG_INTERPRETER)
        OS::PrintErr("ImplicitClosureFunction fix2 static argcount");
#endif
      }
      isImplicitClosureFunction = false;
      isStaticImplicitClosureFunction = false;
    }
#endif

  BytecodePtr bytecode = function->untag()->bytecode_;
  FP[kKBCFunctionSlotFromFp] = function;
  FP[kKBCPcMarkerSlotFromFp] = bytecode;
  FP[kKBCSavedCallerPcSlotFromFp] = static_cast<ObjectPtr>(kEntryFramePcMarker);
  FP[kKBCSavedCallerFpSlotFromFp] =
      static_cast<ObjectPtr>(reinterpret_cast<uword>(fp_));

  // Load argument descriptor.
  argdesc_ = argdesc;

  // Ready to start executing bytecode. Load entry point and corresponding
  // object pool.
  pc = reinterpret_cast<const KBCInstr*>(bytecode->untag()->instructions_);
#if defined(DART_DYNAMIC_RUNTIME) || !defined (PRODUCT)
    pc_ = pc;
    fp_ = FP;
#endif
  pp_ = bytecode->untag()->object_pool_;

  // Save current VM tag and mark thread as executing Dart code. For the
  // profiler, do this *after* setting up the entry frame (compare the machine
  // code entry stubs).
  const uword vm_tag = thread->vm_tag();
  thread->set_vm_tag(VMTag::kDartInterpretedTagId);

  // Save current top stack resource and reset the list.
  StackResource* top_resource = thread->top_resource();
  thread->set_top_resource(NULL);

  // Cache some frequently used values in the frame.
  BoolPtr true_value = Bool::True().ptr();
  BoolPtr false_value = Bool::False().ptr();
  ObjectPtr null_value = Object::null();

#ifdef DART_HAS_COMPUTED_GOTO
  static const void* dispatch[] = {
#define TARGET(name, fmt, kind, fmta, fmtb, fmtc) &&bc##name,
      KERNEL_BYTECODES_LIST(TARGET)
#undef TARGET
  };
  DISPATCH();  // Enter the dispatch loop.
#else
  DISPATCH();  // Enter the dispatch loop.
SwitchDispatch:
  switch (op & 0xFF) {
#define TARGET(name, fmt, kind, fmta, fmtb, fmtc)                              \
  case KernelBytecode::k##name:                                                \
    goto bc##name;
    KERNEL_BYTECODES_LIST(TARGET)
#undef TARGET
    default:
      FATAL1("Undefined opcode: %d\n", op);
  }
#endif

  // KernelBytecode handlers (see constants_kbc.h for bytecode descriptions).
  {
    BYTECODE(Entry, D);
    const intptr_t num_locals = rD;

    // Initialize locals with null & set SP.
    for (intptr_t i = 0; i < num_locals; i++) {
      FP[i] = null_value;
    }
    SP = FP + num_locals - 1;

    DISPATCH();
  }

  {
    BYTECODE(EntryFixed, A_E);
    const intptr_t num_fixed_params = rA;
    const intptr_t num_locals = rE;

    const intptr_t arg_count = InterpreterHelpers::ArgDescArgCount(argdesc_);
    const intptr_t pos_count = InterpreterHelpers::ArgDescPosCount(argdesc_);
    if ((arg_count != num_fixed_params) || (pos_count != num_fixed_params)) {
      SP[1] = FrameFunction(FP);
      goto NoSuchMethodFromPrologue;
    }

    // Initialize locals with null & set SP.
    for (intptr_t i = 0; i < num_locals; i++) {
      FP[i] = null_value;
    }
    SP = FP + num_locals - 1;

    DISPATCH();
  }

  {
    BYTECODE(EntryOptional, A_B_C);
    if (CopyParameters(thread, &pc, &FP, &SP, rA, rB, rC)) {
      DISPATCH();
    } else {
      SP[1] = FrameFunction(FP);
      goto NoSuchMethodFromPrologue;
    }
  }

  {
    BYTECODE(Frame, D);
    // Initialize locals with null and increment SP.
    const intptr_t num_locals = rD;
    for (intptr_t i = 1; i <= num_locals; i++) {
      SP[i] = null_value;
    }
    SP += num_locals;

    DISPATCH();
  }

  {
    BYTECODE(SetFrame, A);
    SP = FP + rA - 1;
    DISPATCH();
  }

  {
    BYTECODE(CheckStack, A);
    {
      // Check the interpreter's own stack limit for actual interpreter's stack
      // overflows, and also the thread's stack limit for scheduled interrupts.
      if (reinterpret_cast<uword>(SP) >= overflow_stack_limit() ||
          thread->HasScheduledInterrupts()) {
        Exit(thread, FP, SP + 1, pc);
        INVOKE_RUNTIME(DRT_StackOverflow,
                       NativeArguments(thread, 0, nullptr, nullptr));
      }
    }
    DISPATCH();
  }

  {
    BYTECODE(DebugCheck, 0);
    // bytecode doesn't support debug
    // DEBUG_CHECK;
    DISPATCH();
  }

  {
    BYTECODE(CheckFunctionTypeArgs, A_E);
    const intptr_t declared_type_args_len = rA;
    const intptr_t first_stack_local_index = rE;

    // Decode arguments descriptor's type args len.
    const intptr_t type_args_len =
        InterpreterHelpers::ArgDescTypeArgsLen(argdesc_);
    if ((type_args_len != declared_type_args_len) && (type_args_len != 0)) {
      SP[1] = FrameFunction(FP);
      goto NoSuchMethodFromPrologue;
    }
    if (type_args_len > 0) {
      // Decode arguments descriptor's argument count (excluding type args).
      const intptr_t arg_count = InterpreterHelpers::ArgDescArgCount(argdesc_);
      // Copy passed-in type args to first local slot.
      FP[first_stack_local_index] = *FrameArguments(FP, arg_count + 1);
    } else if (declared_type_args_len > 0) {
      FP[first_stack_local_index] = Object::null();
    }
    DISPATCH();
  }

  {
    BYTECODE(InstantiateType, D);
    // Stack: instantiator type args, function type args
    ObjectPtr type = LOAD_CONSTANT(rD);
    SP[1] = type;
    SP[2] = SP[-1];
    SP[3] = SP[0];
    Exit(thread, FP, SP + 4, pc);
    {
      INVOKE_RUNTIME(DRT_InstantiateType,
                     NativeArguments(thread, 3, SP + 1, SP - 1));
    }
    SP -= 1;
    DISPATCH();
  }

  {
    BYTECODE(InstantiateTypeArgumentsTOS, A_E);
    // Stack: instantiator type args, function type args
    TypeArgumentsPtr type_arguments =
        static_cast<TypeArgumentsPtr>(LOAD_CONSTANT(rE));

    ObjectPtr instantiator_type_args = SP[-1];
    ObjectPtr function_type_args = SP[0];
    // If both instantiators are null and if the type argument vector
    // instantiated from null becomes a vector of dynamic, then use null as
    // the type arguments.
    if ((rA == 0) || (null_value != instantiator_type_args) ||
        (null_value != function_type_args)) {
      // First lookup in the cache.
      ArrayPtr instantiations = type_arguments->untag()->instantiations_;
      for (intptr_t i = 0;
           instantiations->untag()->data()[i] !=
           static_cast<ObjectPtr>(TypeArguments::kNoInstantiator);
           i += TypeArguments::Instantiation::kSizeInWords) {
        if ((instantiations->untag()->data()
                 [i +
                  TypeArguments::Instantiation::kInstantiatorTypeArgsIndex] ==
             instantiator_type_args) &&
            (instantiations->untag()->data()
                 [i + TypeArguments::Instantiation::kFunctionTypeArgsIndex] ==
             function_type_args)) {
          // Found in the cache.
          SP[-1] =
              instantiations->untag()->data()[i + TypeArguments::Instantiation::
                                                    kInstantiatedTypeArgsIndex];
          goto InstantiateTypeArgumentsTOSDone;
        }
      }

      // Cache lookup failed, call runtime.
      SP[1] = type_arguments;
      SP[2] = instantiator_type_args;
      SP[3] = function_type_args;

      Exit(thread, FP, SP + 4, pc);
      INVOKE_RUNTIME(DRT_InstantiateTypeArguments,
                     NativeArguments(thread, 3, SP + 1, SP - 1));
    }

  InstantiateTypeArgumentsTOSDone:
    SP -= 1;
    DISPATCH();
  }

  {
    BYTECODE(Throw, A);
    {
      SP[1] = 0;  // Space for result.
      Exit(thread, FP, SP + 2, pc);
      if (rA == 0) {  // Throw
        INVOKE_RUNTIME(DRT_Throw, NativeArguments(thread, 1, SP, SP + 1));
      } else {  // ReThrow
        INVOKE_RUNTIME(DRT_ReThrow, NativeArguments(thread, 2, SP - 1, SP + 1));
      }
    }
    DISPATCH();
  }

  {
    BYTECODE(Drop1, 0);
    SP--;
    DISPATCH();
  }

  {
    BYTECODE(LoadConstant, A_E);
    FP[rA] = LOAD_CONSTANT(rE);
    DISPATCH();
  }

  {
    BYTECODE(PushConstant, D);
    *++SP = LOAD_CONSTANT(rD);
    DISPATCH();
  }

  {
    BYTECODE(PushNull, 0);
    *++SP = null_value;
    DISPATCH();
  }

  {
    BYTECODE(PushTrue, 0);
    *++SP = true_value;
    DISPATCH();
  }

  {
    BYTECODE(PushFalse, 0);
    *++SP = false_value;
    DISPATCH();
  }

  {
    BYTECODE(PushInt, X);
    *++SP = Smi::New(rX);
    DISPATCH();
  }

  {
    BYTECODE(Push, X);
    *++SP = FP[rX];
    DISPATCH();
  }

  {
    BYTECODE(StoreLocal, X);
    FP[rX] = *SP;
    DISPATCH();
  }

  {
    BYTECODE(PopLocal, X);
    FP[rX] = *SP--;
    DISPATCH();
  }

  {
    BYTECODE(MoveSpecial, A_Y);
    ASSERT(rA < KernelBytecode::kSpecialIndexCount);
    FP[rY] = special_[rA];
    DISPATCH();
  }

  {
    BYTECODE(BooleanNegateTOS, 0);
    SP[0] = (SP[0] == true_value) ? false_value : true_value;
    DISPATCH();
  }

  {
    BYTECODE(DirectCall, D_F);
    DEBUG_CHECK;
    // Invoke target function.
    {
      const uint32_t argc = rF;
      const uint32_t kidx = rD;
#if !defined(DART_DYNAMIC_RUNTIME)
      InterpreterHelpers::IncrementUsageCounter(FrameFunction(FP));
#endif
      *++SP = LOAD_CONSTANT(kidx);
      ObjectPtr* call_base = SP - argc;
      ObjectPtr* call_top = SP;
      argdesc_ = static_cast<ArrayPtr>(LOAD_CONSTANT(kidx + 1));
      if (!Invoke(thread, call_base, call_top, &pc, &FP, &SP)) {
        HANDLE_EXCEPTION;
      }
    }

    DISPATCH();
  }

  {
    BYTECODE(UncheckedDirectCall, D_F);
    DEBUG_CHECK;
    // Invoke target function.
    {
      const uint32_t argc = rF;
      const uint32_t kidx = rD;
#if !defined(DART_DYNAMIC_RUNTIME)
      InterpreterHelpers::IncrementUsageCounter(FrameFunction(FP));
#endif
      *++SP = LOAD_CONSTANT(kidx);
      ObjectPtr* call_base = SP - argc;
      ObjectPtr* call_top = SP;
      argdesc_ = static_cast<ArrayPtr>(LOAD_CONSTANT(kidx + 1));
      if (!Invoke(thread, call_base, call_top, &pc, &FP, &SP)) {
        HANDLE_EXCEPTION;
      }
    }

    DISPATCH();
  }

  {
    BYTECODE(InterfaceCall, D_F);
    DEBUG_CHECK;
    {
      const uint32_t argc = rF;
      const uint32_t kidx = rD;

      ObjectPtr* call_base = SP - argc + 1;
      ObjectPtr* call_top = SP + 1;
#if !defined(DART_DYNAMIC_RUNTIME)
      InterpreterHelpers::IncrementUsageCounter(FrameFunction(FP));
#endif
      StringPtr target_name =
          static_cast<FunctionPtr>(LOAD_CONSTANT(kidx))->untag()->name_;
      argdesc_ = static_cast<ArrayPtr>(LOAD_CONSTANT(kidx + 1));
      if (!InstanceCall(thread, target_name, call_base, call_top, &pc, &FP,
                        &SP)) {
        HANDLE_EXCEPTION;
      }
    }

    DISPATCH();
  }
  {
    BYTECODE(InstantiatedInterfaceCall, D_F);
    DEBUG_CHECK;
    {
      const uint32_t argc = rF;
      const uint32_t kidx = rD;

      ObjectPtr* call_base = SP - argc + 1;
      ObjectPtr* call_top = SP + 1;
#if !defined(DART_DYNAMIC_RUNTIME)
      InterpreterHelpers::IncrementUsageCounter(FrameFunction(FP));
#endif
      StringPtr target_name =
          static_cast<FunctionPtr>(LOAD_CONSTANT(kidx))->untag()->name_;
      argdesc_ = static_cast<ArrayPtr>(LOAD_CONSTANT(kidx + 1));
      if (!InstanceCall(thread, target_name, call_base, call_top, &pc, &FP,
                        &SP)) {
        HANDLE_EXCEPTION;
      }
    }

    DISPATCH();
  }

  {
    BYTECODE(UncheckedClosureCall, D_F);
    DEBUG_CHECK;
    {
      const uint32_t argc = rF;
      const uint32_t kidx = rD;

      ClosurePtr receiver = Closure::RawCast(*SP--);
      ObjectPtr* call_base = SP - argc + 1;
      ObjectPtr* call_top = SP + 1;
#if !defined(DART_DYNAMIC_RUNTIME)
      InterpreterHelpers::IncrementUsageCounter(FrameFunction(FP));
#endif
      if (UNLIKELY(receiver == null_value)) {
        SP[0] = Symbols::Call().ptr();
        goto ThrowNullError;
      }
      argdesc_ = static_cast<ArrayPtr>(LOAD_CONSTANT(kidx));
      call_top[0] = receiver->untag()->function_;
#if defined(DART_DYNAMIC_RUNTIME)
      ArgumentsDescriptor arguments_descriptor(
            Array::Handle(argdesc_));
    if (arguments_descriptor.TypeArgsLen() == 0) {
      const TypeArguments &typeArguments =
        TypeArguments::Handle(
            Closure::Handle(receiver).delayed_type_arguments());
      if (typeArguments.Length() > 0) {
#if defined(ENABLE_DEBUG_INTERPRETER)
        const Function &func = Function::Handle(FrameFunction(FP));
        OS::PrintErr("closure fix typeargs1: %s, function:%s, pc:%p",
                     typeArguments.ToCString(),
                     func.ToFullyQualifiedCString(), pc);
#endif
        memmove(call_base+1, call_base, argc * kWordSize);
        call_base[0] = typeArguments.ptr();
        SP = call_top;
        ++call_top;
        call_top[0] = receiver->untag()->function_;
        Exit(thread, FP, call_top + 1, pc);
        intptr_t namedCount =  arguments_descriptor.NamedCount();
        if (namedCount > 0) {
          Array& namesArr = Array::Handle(Array::New(namedCount));
          for (int j = 0; j < namedCount; j++) {
            namesArr.SetAt(j, String::Handle(arguments_descriptor.NameAt(j)));
          }
          argdesc_ = ArgumentsDescriptor::NewBoxed(typeArguments.Length(),
                                                   arguments_descriptor.Count(),
                                                   namesArr);
        } else {
          argdesc_ = ArgumentsDescriptor::NewBoxed(typeArguments.Length(),
                                               arguments_descriptor.Count());
        }
        Unexit(thread);
        fielddispatcher_call_pc_to_argc[pc] = argc+1;
      }
    }

    Function& callFunctionHandle =
      Function::Handle(receiver->untag()->function_);
    if (callFunctionHandle.kind() ==
          UntaggedFunction::kImplicitClosureFunction) {
      const intptr_t type_args_len =
              InterpreterHelpers::ArgDescTypeArgsLen(argdesc_);
      const intptr_t receiver_idx = type_args_len > 0 ? 1 : 0;
      // implicit closure generated by bytecode
      if (!callFunctionHandle.HasCode()) {
        FunctionPtr tmp = receiver->untag()->function_;
        // The wrapped code is machine code
        FunctionPtr parentFunc = callFunctionHandle.parent_function();
        if (Function::HasCode(parentFunc)) {
          tmp = parentFunc;
        }
        if (!callFunctionHandle.is_static()) {
            // update receiver for non static function
            const Closure& closure = Closure::Handle(receiver);
            ObjectPtr instanceObj = Context::Handle(closure.context()).At(0);
            if (instanceObj != receiver) {
                call_base[receiver_idx] = instanceObj;
#if defined(ENABLE_DEBUG_INTERPRETER)
                OS::PrintErr("ImplicitClosureFunction fix5 instance");
#endif
            }
        } else {
          // remove closure argument for static function
          if (receiver_idx == 1) {
            ObjectPtr obj = call_base[0];
            call_base[0] = call_base[1];
            call_base[1] = obj;
          }
          call_base++;
          Exit(thread, FP, call_top + 1, pc);
          ArgumentsDescriptor ads =
              ArgumentsDescriptor(Array::Handle(argdesc_));
          intptr_t namedCount =  ads.NamedCount();
          if (namedCount > 0) {
            Array& namesArr = Array::Handle(Array::New(namedCount));
            for (int j = 0; j < namedCount; j++) {
                namesArr.SetAt(j, String::Handle(ads.NameAt(j)));
            }
            argdesc_ = ArgumentsDescriptor::NewBoxed(type_args_len,
                     InterpreterHelpers::ArgDescArgCount(argdesc_) - 1,
                     namesArr);
          } else {
            argdesc_ = ArgumentsDescriptor::NewBoxed(type_args_len,
                     InterpreterHelpers::ArgDescArgCount(argdesc_) - 1);
          }
          Unexit(thread);
#if defined(ENABLE_DEBUG_INTERPRETER)
          OS::PrintErr("ImplicitClosureFunction fix5 static argcount");
#endif
        }
            call_top[0] = tmp;
         }
      }
#endif
      if (!Invoke(thread, call_base, call_top, &pc, &FP, &SP)) {
        HANDLE_EXCEPTION;
      }
    }

    DISPATCH();
  }

  {
    BYTECODE(UncheckedInterfaceCall, D_F);
    DEBUG_CHECK;
    {
      const uint32_t argc = rF;
      const uint32_t kidx = rD;

      ObjectPtr* call_base = SP - argc + 1;
      ObjectPtr* call_top = SP + 1;
#if !defined(DART_DYNAMIC_RUNTIME)
      InterpreterHelpers::IncrementUsageCounter(FrameFunction(FP));
#endif
      StringPtr target_name =
          static_cast<FunctionPtr>(LOAD_CONSTANT(kidx))->untag()->name_;
      argdesc_ = static_cast<ArrayPtr>(LOAD_CONSTANT(kidx + 1));
      if (!InstanceCall(thread, target_name, call_base, call_top, &pc, &FP,
                        &SP)) {
        HANDLE_EXCEPTION;
      }
    }

    DISPATCH();
  }

  {
    BYTECODE(DynamicCall, D_F);
    DEBUG_CHECK;
    {
      const uint32_t argc = rF;
      const uint32_t kidx = rD;

      ObjectPtr* call_base = SP - argc + 1;
      ObjectPtr* call_top = SP + 1;
#if !defined(DART_DYNAMIC_RUNTIME)
      InterpreterHelpers::IncrementUsageCounter(FrameFunction(FP));
#endif
      StringPtr target_name = String::RawCast(LOAD_CONSTANT(kidx));
      argdesc_ = Array::RawCast(LOAD_CONSTANT(kidx + 1));

#if defined(DART_DYNAMIC_RUNTIME)
      String& function_name = String::Handle(target_name);
      if (function_name.ptr() == Symbols::Call().ptr()) {
        const Instance& receiver = Instance::Cast(Object::Handle(call_base[0]));
        if (receiver.IsClosure()) {
          const Closure& closure = Closure::Cast(receiver);
          Function& closureFunction = Function::Handle(closure.function());
          if (!closureFunction.HasCode()) {
            ArgumentsDescriptor arguments_descriptor(
                    Array::Handle(argdesc_));
            if (arguments_descriptor.TypeArgsLen() == 0) {
              const TypeArguments& typeArguments =
                  TypeArguments::Handle(
                      Closure::Cast(receiver).delayed_type_arguments());
              if (!typeArguments.IsNull() && typeArguments.Length() > 0) {
#if defined(ENABLE_DEBUG_INTERPRETER)
                const Function& func = Function::Handle(FrameFunction(FP));
                OS::PrintErr("closure fix typeargs2: %s, arguments_descriptor:"
                    "%s, function:%s", receiver.ToCString(),
                    typeArguments.ToCString(), func.ToFullyQualifiedCString());
#endif
                memmove(call_base+1, call_base, argc * kWordSize);
                call_base[0] = typeArguments.ptr();
                SP = call_top;
                ++call_top;
                Exit(thread, FP, call_top + 1, pc);
                intptr_t namedCount =  arguments_descriptor.NamedCount();
                if (namedCount > 0) {
                  Array& namesArr = Array::Handle(Array::New(namedCount));
                  for (int j = 0; j < namedCount; j++) {
                    namesArr.SetAt(j,
                               String::Handle(arguments_descriptor.NameAt(j)));
                  }
                  argdesc_ = ArgumentsDescriptor::NewBoxed(
                      typeArguments.Length(), arguments_descriptor.Count(),
                      namesArr);
                } else {
                  argdesc_ = ArgumentsDescriptor::NewBoxed(
                      typeArguments.Length(), arguments_descriptor.Count());
                }
                Unexit(thread);
                fielddispatcher_call_pc_to_argc[pc] = argc+1;
              }
            }
          }
        }
      }
#endif

      if (!InstanceCall(thread, target_name, call_base, call_top, &pc, &FP,
                        &SP)) {
        HANDLE_EXCEPTION;
      }
    }

    DISPATCH();
  }

  {
    BYTECODE(NativeCall, D);
    TypedDataPtr data = static_cast<TypedDataPtr>(LOAD_CONSTANT(rD));
    MethodRecognizer::Kind kind = NativeEntryData::GetKind(data);
    switch (kind) {
      case MethodRecognizer::kObjectEquals: {
        SP[-1] = SP[-1] == SP[0] ? Bool::True().ptr() : Bool::False().ptr();
        SP--;
      } break;
      case MethodRecognizer::kStringBaseLength:
      case MethodRecognizer::kStringBaseIsEmpty: {
        InstancePtr instance = static_cast<InstancePtr>(SP[0]);
        SP[0] = reinterpret_cast<ObjectPtr*>(
            instance->untag())[String::length_offset() / kWordSize];
        if (kind == MethodRecognizer::kStringBaseIsEmpty) {
          SP[0] =
              SP[0] == Smi::New(0) ? Bool::True().ptr() : Bool::False().ptr();
        }
      } break;
      case MethodRecognizer::kGrowableArrayLength: {
        GrowableObjectArrayPtr instance =
            static_cast<GrowableObjectArrayPtr>(SP[0]);
        SP[0] = instance->untag()->length_;
      } break;
      case MethodRecognizer::kObjectArrayLength:
      case MethodRecognizer::kImmutableArrayLength: {
        ArrayPtr instance = static_cast<ArrayPtr>(SP[0]);
        SP[0] = instance->untag()->length_;
      } break;
      case MethodRecognizer::kTypedListBaseLength:
      case MethodRecognizer::kByteDataViewLength: {
        TypedDataBasePtr instance = static_cast<TypedDataBasePtr>(SP[0]);
        SP[0] = instance->untag()->length_;
      } break;
      case MethodRecognizer::kByteDataViewOffsetInBytes:
      case MethodRecognizer::kTypedDataViewOffsetInBytes: {
        TypedDataViewPtr instance = static_cast<TypedDataViewPtr>(SP[0]);
        SP[0] = instance->untag()->offset_in_bytes_;
      } break;
      case MethodRecognizer::kByteDataViewTypedData:
      case MethodRecognizer::kTypedDataViewTypedData: {
        TypedDataViewPtr instance = static_cast<TypedDataViewPtr>(SP[0]);
        SP[0] = instance->untag()->typed_data_;
      } break;
      case MethodRecognizer::kClassIDgetID: {
        SP[0] = InterpreterHelpers::GetClassIdAsSmi(SP[0]);
      } break;
      case MethodRecognizer::kGrowableArrayCapacity: {
        GrowableObjectArrayPtr instance =
            static_cast<GrowableObjectArrayPtr>(SP[0]);
        SP[0] = instance->untag()->data_->untag()->length_;
      } break;
      case MethodRecognizer::kListFactory: {
        if (InterpreterHelpers::ArgDescPosCount(argdesc_) == 2) {
          TypeArgumentsPtr type_args = TypeArguments::RawCast(SP[-1]);
          ObjectPtr length = SP[0];
          SP--;
          if (!AllocateArray(thread, type_args, length, pc, FP, SP)) {
            HANDLE_EXCEPTION;
          }
        } else {
          ASSERT(InterpreterHelpers::ArgDescPosCount(argdesc_) == 1);
          // SP[-1] is type.
          // The native wrapper pushed null as the optional length argument.
          ASSERT(SP[0] == null_value);
          SP[0] = Smi::New(0);  // Patch null length with zero length.
          SP[1] = thread->isolate()->group()->object_store()->
                  growable_list_factory();
          // Change the ArgumentsDescriptor of the call with a new cached one.
          argdesc_ = ArgumentsDescriptor::NewBoxed(
              0, KernelBytecode::kNativeCallToGrowableListArgc);
          // Replace PC to the return trampoline so ReturnTOS would see
          // a call bytecode at return address and will be able to get argc
          // via DecodeArgc.
          pc = KernelBytecode::GetNativeCallToGrowableListReturnTrampoline();
          if (!Invoke(thread, SP - 1, SP + 1, &pc, &FP, &SP)) {
            HANDLE_EXCEPTION;
          }
        }
      } break;
      case MethodRecognizer::kObjectArrayAllocate: {
        TypeArgumentsPtr type_args = TypeArguments::RawCast(SP[-1]);
        ObjectPtr length = SP[0];
        SP--;
        if (!AllocateArray(thread, type_args, length, pc, FP, SP)) {
          HANDLE_EXCEPTION;
        }
      } break;
      case MethodRecognizer::kLinkedHashBase_getIndex: {
        InstancePtr instance = static_cast<InstancePtr>(SP[0]);
        SP[0] = reinterpret_cast<ObjectPtr*>(
            instance->untag())[LinkedHashMap::index_offset() / kWordSize];
      } break;
      case MethodRecognizer::kLinkedHashBase_setIndex: {
        InstancePtr instance = static_cast<InstancePtr>(SP[-1]);
        instance->untag()->StorePointer(
            reinterpret_cast<ObjectPtr*>(instance->untag()) +
                LinkedHashMap::index_offset() / kWordSize,
            SP[0]);
        *--SP = null_value;
      } break;
      case MethodRecognizer::kLinkedHashBase_getData: {
        InstancePtr instance = static_cast<InstancePtr>(SP[0]);
        SP[0] = reinterpret_cast<ObjectPtr*>(
            instance->untag())[LinkedHashMap::data_offset() / kWordSize];
      } break;
      case MethodRecognizer::kLinkedHashBase_setData: {
        InstancePtr instance = static_cast<InstancePtr>(SP[-1]);
        instance->untag()->StorePointer(
            reinterpret_cast<ObjectPtr*>(instance->untag()) +
                LinkedHashMap::data_offset() / kWordSize,
            SP[0]);
        *--SP = null_value;
      } break;
      case MethodRecognizer::kLinkedHashBase_getHashMask: {
        InstancePtr instance = static_cast<InstancePtr>(SP[0]);
        SP[0] = reinterpret_cast<ObjectPtr*>(
            instance->untag())[LinkedHashMap::hash_mask_offset() / kWordSize];
      } break;
      case MethodRecognizer::kLinkedHashBase_setHashMask: {
        InstancePtr instance = static_cast<InstancePtr>(SP[-1]);
        ASSERT(!SP[0]->IsHeapObject());
        reinterpret_cast<ObjectPtr*>(
            instance->untag())[LinkedHashMap::hash_mask_offset() / kWordSize] =
            SP[0];
        *--SP = null_value;
      } break;
      case MethodRecognizer::kLinkedHashBase_getUsedData: {
        InstancePtr instance = static_cast<InstancePtr>(SP[0]);
        SP[0] = reinterpret_cast<ObjectPtr*>(
            instance->untag())[LinkedHashMap::used_data_offset() / kWordSize];
      } break;
      case MethodRecognizer::kLinkedHashBase_setUsedData: {
        InstancePtr instance = static_cast<InstancePtr>(SP[-1]);
        ASSERT(!SP[0]->IsHeapObject());
        reinterpret_cast<ObjectPtr*>(
            instance->untag())[LinkedHashMap::used_data_offset() / kWordSize] =
            SP[0];
        *--SP = null_value;
      } break;
      case MethodRecognizer::kLinkedHashBase_getDeletedKeys: {
        InstancePtr instance = static_cast<InstancePtr>(SP[0]);
        SP[0] = reinterpret_cast<ObjectPtr*>(
           instance->untag())[LinkedHashMap::deleted_keys_offset() / kWordSize];
      } break;
      case MethodRecognizer::kLinkedHashBase_setDeletedKeys: {
        InstancePtr instance = static_cast<InstancePtr>(SP[-1]);
        ASSERT(!SP[0]->IsHeapObject());
        reinterpret_cast<ObjectPtr*>(
            instance->untag())[
            LinkedHashMap::deleted_keys_offset() / kWordSize] = SP[0];
        *--SP = null_value;
      } break;
      case MethodRecognizer::kFfiAbi: {
        *++SP = Smi::New(static_cast<int64_t>(compiler::ffi::TargetAbi()));
      } break;
#define TYPED_DATA_FACTORY(clazz)                                              \
  case MethodRecognizer::kTypedData_##clazz##_factory: {                       \
    ObjectPtr length = SP[0];                                                  \
    SP[1] = Smi::New(kTypedData##clazz##Cid);                                  \
    SP[2] = length;                                                            \
    Exit(thread, FP, SP + 3, pc);                                              \
    INVOKE_RUNTIME(DRT_AllocateTypedData,                                      \
                   NativeArguments(thread, 2, SP + 1, SP));                    \
  } break;
        CLASS_LIST_TYPED_DATA(TYPED_DATA_FACTORY)
#undef TYPED_DATA_FACTORY
      default: {
        NativeEntryData::Payload* payload =
            NativeEntryData::FromTypedArray(data);
        intptr_t argc_tag = NativeEntryData::GetArgcTag(data);
        const intptr_t num_arguments =
            NativeArguments::ArgcBits::decode(argc_tag);

        if (payload->trampoline == NULL) {
          ASSERT(payload->native_function == NULL);
          payload->trampoline = &NativeEntry::BootstrapNativeCallWrapper;
          payload->native_function =
              reinterpret_cast<NativeFunction>(&NativeEntry::LinkNativeCall);
        }

        *++SP = null_value;  // Result slot.

        ObjectPtr* incoming_args = SP - num_arguments;
        ObjectPtr* return_slot = SP;
        Exit(thread, FP, SP + 1, pc);
        NativeArguments native_args(thread, argc_tag, incoming_args,
                                    return_slot);
        INVOKE_NATIVE(
            payload->trampoline,
            reinterpret_cast<Dart_NativeFunction>(payload->native_function),
            reinterpret_cast<Dart_NativeArguments>(&native_args));

        *(SP - num_arguments) = *return_slot;
        SP -= num_arguments;
      }
    }
    DISPATCH();
  }

  {
    BYTECODE(ReturnTOS, 0);
    DEBUG_CHECK;
    ObjectPtr result;  // result to return to the caller.
    result = *SP;
    // Restore caller PC.
    pc = SavedCallerPC(FP);
#if defined(ENABLE_DEBUG_INTERPRETER)
    OS::PrintErr("%dEnd Call %s", logCount,
                 Function::Handle(FrameFunction(FP)).ToFullyQualifiedCString());
    logCount--;
#endif
    // Check if it is a fake PC marking the entry frame.
    if (IsEntryFrameMarker(pc)) {
      // Pop entry frame.
      ObjectPtr* entry_fp = SavedCallerFP(FP);
      // Restore exit frame info saved in entry frame.
      pp_ = static_cast<ObjectPoolPtr>(entry_fp[kKBCSavedPpSlotFromEntryFp]);
      argdesc_ =
          static_cast<ArrayPtr>(entry_fp[kKBCSavedArgDescSlotFromEntryFp]);
      uword exit_fp = static_cast<uword>(entry_fp[kKBCExitLinkSlotFromEntryFp]);
      thread->set_top_exit_frame_info(exit_fp);
      thread->set_top_resource(top_resource);
      thread->set_vm_tag(vm_tag);
      fp_ = entry_fp;
#if defined(DART_DYNAMIC_RUNTIME) || !defined (PRODUCT)
        pc_ = pc;
#endif
      return result;
    }
#if defined(DART_DYNAMIC_RUNTIME)
    uint8_t argc = KernelBytecode::DecodeArgc(pc);
    if (fielddispatcher_call_pc_to_argc.count(pc) > 0) {
      argc = fielddispatcher_call_pc_to_argc[pc];
      fielddispatcher_call_pc_to_argc.erase(pc);
    }
#else
    // Look at the caller to determine how many arguments to pop.
    const uint8_t argc = KernelBytecode::DecodeArgc(pc);
#endif

    // Restore SP, FP and PP. Push result and dispatch.
    SP = FrameArguments(FP, argc);
    FP = SavedCallerFP(FP);
#if defined(DART_DYNAMIC_RUNTIME) || !defined (PRODUCT)
        fp_ = FP;
        pc_ = pc;
#endif
    pp_ = InterpreterHelpers::FrameBytecode(FP)->untag()->object_pool_;
    *SP = result;
    DISPATCH();
  }

  {
    BYTECODE(InitLateField, D);
    FieldPtr field = RAW_CAST(Field, LOAD_CONSTANT(rD + 1));
    InstancePtr instance = static_cast<InstancePtr>(SP[0]);
    intptr_t offset_in_words =
        Smi::Value(field->untag()->host_offset_or_field_id_);

    instance->untag()->StorePointer(
        reinterpret_cast<ObjectPtr*>(instance->untag()) + offset_in_words,
        Object::RawCast(Object::sentinel().ptr()), thread);

    SP -= 1;  // Drop instance.
    DISPATCH();
  }

  {
    BYTECODE(PushUninitializedSentinel, 0);
    *++SP = Object::sentinel().ptr();
    DISPATCH();
  }

  {
    BYTECODE(JumpIfInitialized, T);
    SP -= 1;
    if (SP[1] != Object::sentinel().ptr()) {
      LOAD_JUMP_TARGET();
    }
    DISPATCH();
  }

  {
    BYTECODE(StoreStaticTOS, D);
    FieldPtr field = static_cast<FieldPtr>(LOAD_CONSTANT(rD));
    InstancePtr value = static_cast<InstancePtr>(*SP--);
    intptr_t field_id = Smi::Value(field->untag()->host_offset_or_field_id_);
    thread->field_table_values()[field_id] = value;
    DISPATCH();
  }

  {
    BYTECODE(LoadStatic, D);
    FieldPtr field = static_cast<FieldPtr>(LOAD_CONSTANT(rD));
    intptr_t field_id = Smi::Value(field->untag()->host_offset_or_field_id_);
    ObjectPtr value = thread->field_table_values()[field_id];
    ASSERT((value != Object::sentinel().ptr()) &&
           (value != Object::transition_sentinel().ptr()));
    *++SP = value;
    DISPATCH();
  }

  {
    BYTECODE(StoreFieldTOS, D);
    FieldPtr field = RAW_CAST(Field, LOAD_CONSTANT(rD + 1));
    InstancePtr instance = static_cast<InstancePtr>(SP[-1]);
    ObjectPtr value = static_cast<ObjectPtr>(SP[0]);
    intptr_t offset_in_words =
        Smi::Value(field->untag()->host_offset_or_field_id_);

    if (InterpreterHelpers::FieldNeedsGuardUpdate(field, value)) {
      SP[1] = 0;  // Unused result of runtime call.
      SP[2] = field;
      SP[3] = value;
      Exit(thread, FP, SP + 4, pc);
      if (!InvokeRuntime(thread, this, DRT_UpdateFieldCid,
                         NativeArguments(thread, 2, /* argv */ SP + 2,
                                         /* retval */ SP + 1))) {
        HANDLE_EXCEPTION;
      }

      // Reload objects after the call which may trigger GC.
      field = RAW_CAST(Field, LOAD_CONSTANT(rD + 1));
      instance = static_cast<InstancePtr>(SP[-1]);
      value = SP[0];
    }

    const bool unboxing =
        (field->untag()->is_nullable_ != kNullCid) &&
        Field::UnboxingCandidateBit::decode(field->untag()->kind_bits_);
    classid_t guarded_cid = field->untag()->guarded_cid_;
    if (unboxing && (guarded_cid == kDoubleCid) && supports_unboxed_doubles_) {
      double raw_value = Double::RawCast(value)->untag()->value_;
      ASSERT(*(reinterpret_cast<DoublePtr*>(instance->untag()) +
               offset_in_words) == null_value);  // Initializing store.
      if (!AllocateDouble(thread, raw_value, pc, FP, SP)) {
        HANDLE_EXCEPTION;
      }
      DoublePtr box = Double::RawCast(SP[0]);
      instance = static_cast<InstancePtr>(SP[-1]);
      instance->untag()->StorePointer(
          reinterpret_cast<DoublePtr*>(instance->untag()) + offset_in_words,
          box, thread);
    } else if (unboxing && (guarded_cid == kFloat32x4Cid) &&
               supports_unboxed_simd128_) {
      simd128_value_t raw_value;
      raw_value.readFrom(Float32x4::RawCast(value)->untag()->value_);
      ASSERT(*(reinterpret_cast<Float32x4Ptr*>(instance->untag()) +
               offset_in_words) == null_value);  // Initializing store.
      if (!AllocateFloat32x4(thread, raw_value, pc, FP, SP)) {
        HANDLE_EXCEPTION;
      }
      Float32x4Ptr box = Float32x4::RawCast(SP[0]);
      instance = static_cast<InstancePtr>(SP[-1]);
      instance->untag()->StorePointer(
          reinterpret_cast<Float32x4Ptr*>(instance->untag()) + offset_in_words,
          box, thread);
    } else if (unboxing && (guarded_cid == kFloat64x2Cid) &&
               supports_unboxed_simd128_) {
      simd128_value_t raw_value;
      raw_value.readFrom(Float64x2::RawCast(value)->untag()->value_);
      ASSERT(*(reinterpret_cast<Float64x2Ptr*>(instance->untag()) +
               offset_in_words) == null_value);  // Initializing store.
      if (!AllocateFloat64x2(thread, raw_value, pc, FP, SP)) {
        HANDLE_EXCEPTION;
      }
      Float64x2Ptr box = Float64x2::RawCast(SP[0]);
      instance = static_cast<InstancePtr>(SP[-1]);
      instance->untag()->StorePointer(
          reinterpret_cast<Float64x2Ptr*>(instance->untag()) + offset_in_words,
          box, thread);
    } else {
      instance->untag()->StorePointer(
          reinterpret_cast<ObjectPtr*>(instance->untag()) + offset_in_words,
          value, thread);
    }

    SP -= 2;  // Drop instance and value.
    DISPATCH();
  }

  {
    BYTECODE(StoreContextParent, 0);
    const uword offset_in_words =
        static_cast<uword>(Context::parent_offset() / kWordSize);
    ContextPtr instance = static_cast<ContextPtr>(SP[-1]);
    ContextPtr value = static_cast<ContextPtr>(SP[0]);
    SP -= 2;  // Drop instance and value.

    instance->untag()->StorePointer(
        reinterpret_cast<ContextPtr*>(instance->untag()) + offset_in_words,
        value, thread);

    DISPATCH();
  }

  {
    BYTECODE(StoreContextVar, A_E);
    const uword offset_in_words =
        static_cast<uword>(Context::variable_offset(rE) / kWordSize);
    ContextPtr instance = static_cast<ContextPtr>(SP[-1]);
    ObjectPtr value = static_cast<ContextPtr>(SP[0]);
    SP -= 2;  // Drop instance and value.
    ASSERT(rE < static_cast<uint32_t>(instance->untag()->num_variables_));
    instance->untag()->StorePointer(
        reinterpret_cast<ObjectPtr*>(instance->untag()) + offset_in_words,
        value, thread);

    DISPATCH();
  }

  {
    BYTECODE(LoadFieldTOS, D);
#if defined(DEBUG)
    // Currently only used to load closure fields, which are not unboxed.
    // If used for general field, code for copying the mutable box must be
    // added.
    FieldPtr field = RAW_CAST(Field, LOAD_CONSTANT(rD + 1));
    const bool unboxing =
        (field->ptr()->is_nullable_ != kNullCid) &&
        Field::UnboxingCandidateBit::decode(field->ptr()->kind_bits_);
    ASSERT(!unboxing);
#endif
    const uword offset_in_words =
        static_cast<uword>(Smi::Value(RAW_CAST(Smi, LOAD_CONSTANT(rD))));
    InstancePtr instance = static_cast<InstancePtr>(SP[0]);
    SP[0] = reinterpret_cast<ObjectPtr*>(instance->untag())[offset_in_words];
    DISPATCH();
  }

  {
    BYTECODE(LoadTypeArgumentsField, D);
    const uword offset_in_words =
        static_cast<uword>(Smi::Value(RAW_CAST(Smi, LOAD_CONSTANT(rD))));
    InstancePtr instance = static_cast<InstancePtr>(SP[0]);
    SP[0] = reinterpret_cast<ObjectPtr*>(instance->untag())[offset_in_words];
    DISPATCH();
  }

  {
    BYTECODE(LoadContextParent, 0);
    const uword offset_in_words =
        static_cast<uword>(Context::parent_offset() / kWordSize);
    ContextPtr instance = static_cast<ContextPtr>(SP[0]);
    SP[0] = reinterpret_cast<ObjectPtr*>(instance->untag())[offset_in_words];
    DISPATCH();
  }

  {
    BYTECODE(LoadContextVar, A_E);
    const uword offset_in_words =
        static_cast<uword>(Context::variable_offset(rE) / kWordSize);
    ContextPtr instance = static_cast<ContextPtr>(SP[0]);
    ASSERT(rE < static_cast<uint32_t>(instance->untag()->num_variables_));
    SP[0] = reinterpret_cast<ObjectPtr*>(instance->untag())[offset_in_words];
    DISPATCH();
  }

  {
    BYTECODE(AllocateContext, A_E);
    ++SP;
    const uint32_t num_context_variables = rE;
    if (!AllocateContext(thread, num_context_variables, pc, FP, SP)) {
      HANDLE_EXCEPTION;
    }
    DISPATCH();
  }

  {
    BYTECODE(CloneContext, A_E);
    {
      SP[1] = SP[0];  // Context to clone.
      Exit(thread, FP, SP + 2, pc);
      INVOKE_RUNTIME(DRT_CloneContext, NativeArguments(thread, 1, SP + 1, SP));
    }
    DISPATCH();
  }

  {
    BYTECODE(Allocate, D);
    ClassPtr cls = Class::RawCast(LOAD_CONSTANT(rD));
    if (LIKELY(InterpreterHelpers::IsAllocateFinalized(cls))) {
      const intptr_t class_id = cls->untag()->id_;
      const intptr_t instance_size = cls->untag()->host_instance_size_in_words_
                                     << kWordSizeLog2;
      ObjectPtr result;
      if (TryAllocate(thread, class_id, instance_size, &result)) {
        uword start = UntaggedObject::ToAddr(result);
        for (intptr_t offset = sizeof(UntaggedInstance); offset < instance_size;
             offset += kWordSize) {
          *reinterpret_cast<ObjectPtr*>(start + offset) = null_value;
        }
        *++SP = result;
        DISPATCH();
      }
    }

    SP[1] = 0;           // Space for the result.
    SP[2] = cls;         // Class object.
    SP[3] = null_value;  // Type arguments.
    Exit(thread, FP, SP + 4, pc);
    INVOKE_RUNTIME(DRT_AllocateObject,
                   NativeArguments(thread, 2, SP + 2, SP + 1));
    SP++;  // Result is in SP[1].
    DISPATCH();
  }

  {
    BYTECODE(AllocateT, 0);
    ClassPtr cls = Class::RawCast(SP[0]);
    TypeArgumentsPtr type_args = TypeArguments::RawCast(SP[-1]);
    if (LIKELY(InterpreterHelpers::IsAllocateFinalized(cls))) {
      const intptr_t class_id = cls->untag()->id_;
      const intptr_t instance_size = cls->untag()->host_instance_size_in_words_
                                     << kWordSizeLog2;
      ObjectPtr result;
      if (TryAllocate(thread, class_id, instance_size, &result)) {
        uword start = UntaggedObject::ToAddr(result);
        for (intptr_t offset = sizeof(UntaggedInstance); offset < instance_size;
             offset += kWordSize) {
          *reinterpret_cast<ObjectPtr*>(start + offset) = null_value;
        }
        const intptr_t type_args_offset =
            cls->untag()->host_type_arguments_field_offset_in_words_
            << kWordSizeLog2;
        *reinterpret_cast<ObjectPtr*>(start + type_args_offset) = type_args;
        *--SP = result;
        DISPATCH();
      }
    }

    SP[1] = cls;
    SP[2] = type_args;
    Exit(thread, FP, SP + 3, pc);
    INVOKE_RUNTIME(DRT_AllocateObject,
                   NativeArguments(thread, 2, SP + 1, SP - 1));
    SP -= 1;  // Result is in SP - 1.
    DISPATCH();
  }

  {
    BYTECODE(CreateArrayTOS, 0);
    TypeArgumentsPtr type_args = TypeArguments::RawCast(SP[-1]);
    ObjectPtr length = SP[0];
    SP--;
    if (!AllocateArray(thread, type_args, length, pc, FP, SP)) {
      HANDLE_EXCEPTION;
    }
    DISPATCH();
  }

  {
    BYTECODE(AssertAssignable, A_E);
    // Stack: instance, type, instantiator type args, function type args, name
    ObjectPtr* args = SP - 4;
    const bool may_be_smi = (rA == 1);
    const bool is_smi =
        ((static_cast<intptr_t>(args[0]) & kSmiTagMask) == kSmiTag);
    const bool smi_ok = is_smi && may_be_smi;
    if (!smi_ok && (args[0] != null_value)) {
      SubtypeTestCachePtr cache =
          static_cast<SubtypeTestCachePtr>(LOAD_CONSTANT(rE));

      if (!AssertAssignable(thread, pc, FP, SP, args, cache)) {
        HANDLE_EXCEPTION;
      }
    }

    SP -= 4;  // Instance remains on stack.
    DISPATCH();
  }

  {
    BYTECODE(AssertSubtype, 0);
    ObjectPtr* args = SP - 4;

    // TODO(kustermann): Implement fast case for common arguments.

    // The arguments on the stack look like:
    //     args[0]  instantiator type args
    //     args[1]  function type args
    //     args[2]  sub_type
    //     args[3]  super_type
    //     args[4]  name

    // This is unused, since the negative case throws an exception.
    SP++;
    ObjectPtr* result_slot = SP;

    Exit(thread, FP, SP + 1, pc);
    INVOKE_RUNTIME(DRT_SubtypeCheck,
                   NativeArguments(thread, 5, args, result_slot));

    // Drop result slot and all arguments.
    SP -= 6;

    DISPATCH();
  }

  {
    BYTECODE(AssertBoolean, A);
    ObjectPtr value = SP[0];
    if (rA != 0u) {  // Should we perform type check?
      if ((value == true_value) || (value == false_value)) {
        goto AssertBooleanOk;
      }
    } else if (value != null_value) {
      goto AssertBooleanOk;
    } else if (value == null_value) {
        SP[0] = true_value;
        goto AssertBooleanOk;
    }

    // Assertion failed.
    {
      SP[1] = SP[0];  // instance
      Exit(thread, FP, SP + 2, pc);
      INVOKE_RUNTIME(DRT_NonBoolTypeError,
                     NativeArguments(thread, 1, SP + 1, SP));
    }

  AssertBooleanOk:
    DISPATCH();
  }

  {
    BYTECODE(Jump, T);
    LOAD_JUMP_TARGET();
    DISPATCH();
  }

  {
    BYTECODE(JumpIfNoAsserts, T);
    if (!thread->isolate()->group()->asserts()) {
      LOAD_JUMP_TARGET();
    }
    DISPATCH();
  }

  {
    BYTECODE(JumpIfNotZeroTypeArgs, T);
    if (InterpreterHelpers::ArgDescTypeArgsLen(argdesc_) != 0) {
      LOAD_JUMP_TARGET();
    }
    DISPATCH();
  }

  {
    BYTECODE(JumpIfEqStrict, T);
    SP -= 2;
    if (SP[1] == SP[2]) {
      LOAD_JUMP_TARGET();
    }
    DISPATCH();
  }

  {
    BYTECODE(JumpIfNeStrict, T);
    SP -= 2;
    if (SP[1] != SP[2]) {
      LOAD_JUMP_TARGET();
    }
    DISPATCH();
  }

  {
    BYTECODE(JumpIfTrue, T);
    SP -= 1;
    if (SP[1] != false_value) {
      LOAD_JUMP_TARGET();
    }
    DISPATCH();
  }

  {
    BYTECODE(JumpIfFalse, T);
    SP -= 1;
    if (SP[1] != true_value) {
      LOAD_JUMP_TARGET();
    }
    DISPATCH();
  }

  {
    BYTECODE(JumpIfNull, T);
    SP -= 1;
    if (SP[1] == null_value) {
      LOAD_JUMP_TARGET();
    }
    DISPATCH();
  }

  {
    BYTECODE(JumpIfNotNull, T);
    SP -= 1;
    if (SP[1] != null_value) {
      LOAD_JUMP_TARGET();
    }
    DISPATCH();
  }

  {
    BYTECODE(JumpIfUnchecked, T);
    // Interpreter is not tracking unchecked calls, so fall through to
    // parameter type checks.
    DISPATCH();
  }

  {
    BYTECODE(StoreIndexedTOS, 0);
    SP -= 3;
    ArrayPtr array = RAW_CAST(Array, SP[1]);
    SmiPtr index = RAW_CAST(Smi, SP[2]);
    ObjectPtr value = SP[3];
    ASSERT(InterpreterHelpers::CheckIndex(index, array->untag()->length_));
    array->untag()->StorePointer(array->untag()->data() + Smi::Value(index),
                                 value, thread);
    DISPATCH();
  }

  {
    BYTECODE(EqualsNull, 0);
    DEBUG_CHECK;
    SP[0] = (SP[0] == null_value) ? true_value : false_value;
    DISPATCH();
  }

  {
    BYTECODE(NullCheck, D);
    if (UNLIKELY(SP[0] == null_value)) {
#if defined(DART_DYNAMIC_RUNTIME)
        OS::PrintErr("null check");
#endif
      // Load selector.
      SP[0] = LOAD_CONSTANT(rD);
      goto ThrowNullError;
    }
    SP -= 1;

    DISPATCH();
  }

  {
    BYTECODE(NegateInt, 0);
    DEBUG_CHECK;
    UNBOX_INT64(value, SP[0], Symbols::UnaryMinus());
    int64_t result = Utils::SubWithWrapAround(static_cast<int64_t>(0), value);
    BOX_INT64_RESULT(result);
    DISPATCH();
  }

  {
    BYTECODE(AddInt, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_INT64(a, SP[0], Symbols::Plus());
    UNBOX_INT64(b, SP[1], Symbols::Plus());
    int64_t result = Utils::AddWithWrapAround(a, b);
    BOX_INT64_RESULT(result);
    DISPATCH();
  }

  {
    BYTECODE(SubInt, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_INT64(a, SP[0], Symbols::Minus());
    UNBOX_INT64(b, SP[1], Symbols::Minus());
    int64_t result = Utils::SubWithWrapAround(a, b);
    BOX_INT64_RESULT(result);
    DISPATCH();
  }

  {
    BYTECODE(MulInt, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_INT64(a, SP[0], Symbols::Star());
    UNBOX_INT64(b, SP[1], Symbols::Star());
    int64_t result = Utils::MulWithWrapAround(a, b);
    BOX_INT64_RESULT(result);
    DISPATCH();
  }

  {
    BYTECODE(TruncDivInt, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_INT64(a, SP[0], Symbols::TruncDivOperator());
    UNBOX_INT64(b, SP[1], Symbols::TruncDivOperator());
    if (UNLIKELY(b == 0)) {
      goto ThrowIntegerDivisionByZeroException;
    }
    int64_t result;
    if (UNLIKELY((a == Mint::kMinValue) && (b == -1))) {
      result = Mint::kMinValue;
    } else {
      result = a / b;
    }
    BOX_INT64_RESULT(result);
    DISPATCH();
  }

  {
    BYTECODE(ModInt, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_INT64(a, SP[0], Symbols::Percent());
    UNBOX_INT64(b, SP[1], Symbols::Percent());
    if (UNLIKELY(b == 0)) {
      goto ThrowIntegerDivisionByZeroException;
    }
    int64_t result;
    if (UNLIKELY((a == Mint::kMinValue) && (b == -1))) {
      result = 0;
    } else {
      result = a % b;
      if (result < 0) {
        if (b < 0) {
          result -= b;
        } else {
          result += b;
        }
      }
    }
    BOX_INT64_RESULT(result);
    DISPATCH();
  }

  {
    BYTECODE(BitAndInt, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_INT64(a, SP[0], Symbols::Ampersand());
    UNBOX_INT64(b, SP[1], Symbols::Ampersand());
    int64_t result = a & b;
    BOX_INT64_RESULT(result);
    DISPATCH();
  }

  {
    BYTECODE(BitOrInt, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_INT64(a, SP[0], Symbols::BitOr());
    UNBOX_INT64(b, SP[1], Symbols::BitOr());
    int64_t result = a | b;
    BOX_INT64_RESULT(result);
    DISPATCH();
  }

  {
    BYTECODE(BitXorInt, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_INT64(a, SP[0], Symbols::Caret());
    UNBOX_INT64(b, SP[1], Symbols::Caret());
    int64_t result = a ^ b;
    BOX_INT64_RESULT(result);
    DISPATCH();
  }

  {
    BYTECODE(ShlInt, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_INT64(a, SP[0], Symbols::LeftShiftOperator());
    UNBOX_INT64(b, SP[1], Symbols::LeftShiftOperator());
    if (b < 0) {
      SP[0] = SP[1];
      goto ThrowArgumentError;
    }
    int64_t result = Utils::ShiftLeftWithTruncation(a, b);
    BOX_INT64_RESULT(result);
    DISPATCH();
  }

  {
    BYTECODE(ShrInt, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_INT64(a, SP[0], Symbols::RightShiftOperator());
    UNBOX_INT64(b, SP[1], Symbols::RightShiftOperator());
    if (b < 0) {
      SP[0] = SP[1];
      goto ThrowArgumentError;
    }
    int64_t result = a >> Utils::Minimum<int64_t>(b, Mint::kBits);
    BOX_INT64_RESULT(result);
    DISPATCH();
  }

  {
    BYTECODE(CompareIntEq, 0);
    DEBUG_CHECK;
    SP -= 1;
    if (SP[0] == SP[1]) {
      SP[0] = true_value;
    } else if (!SP[0]->IsHeapObject() || !SP[1]->IsHeapObject() ||
               (SP[0] == null_value) || (SP[1] == null_value)) {
      SP[0] = false_value;
    } else {
      int64_t a = Integer::GetInt64Value(RAW_CAST(Integer, SP[0]));
      int64_t b = Integer::GetInt64Value(RAW_CAST(Integer, SP[1]));
      SP[0] = (a == b) ? true_value : false_value;
    }
    DISPATCH();
  }

  {
    BYTECODE(CompareIntGt, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_INT64(a, SP[0], Symbols::RAngleBracket());
    UNBOX_INT64(b, SP[1], Symbols::RAngleBracket());
    SP[0] = (a > b) ? true_value : false_value;
    DISPATCH();
  }

  {
    BYTECODE(CompareIntLt, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_INT64(a, SP[0], Symbols::LAngleBracket());
    UNBOX_INT64(b, SP[1], Symbols::LAngleBracket());
    SP[0] = (a < b) ? true_value : false_value;
    DISPATCH();
  }

  {
    BYTECODE(CompareIntGe, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_INT64(a, SP[0], Symbols::GreaterEqualOperator());
    UNBOX_INT64(b, SP[1], Symbols::GreaterEqualOperator());
    SP[0] = (a >= b) ? true_value : false_value;
    DISPATCH();
  }

  {
    BYTECODE(CompareIntLe, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_INT64(a, SP[0], Symbols::LessEqualOperator());
    UNBOX_INT64(b, SP[1], Symbols::LessEqualOperator());
    SP[0] = (a <= b) ? true_value : false_value;
    DISPATCH();
  }

  {
    BYTECODE(NegateDouble, 0);
    DEBUG_CHECK;
    UNBOX_DOUBLE(value, SP[0], Symbols::UnaryMinus());
    double result = -value;
    BOX_DOUBLE_RESULT(result);
    DISPATCH();
  }

  {
    BYTECODE(AddDouble, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_DOUBLE(a, SP[0], Symbols::Plus());
    UNBOX_DOUBLE(b, SP[1], Symbols::Plus());
    double result = a + b;
    BOX_DOUBLE_RESULT(result);
    DISPATCH();
  }

  {
    BYTECODE(SubDouble, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_DOUBLE(a, SP[0], Symbols::Minus());
    UNBOX_DOUBLE(b, SP[1], Symbols::Minus());
    double result = a - b;
    BOX_DOUBLE_RESULT(result);
    DISPATCH();
  }

  {
    BYTECODE(MulDouble, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_DOUBLE(a, SP[0], Symbols::Star());
    UNBOX_DOUBLE(b, SP[1], Symbols::Star());
    double result = a * b;
    BOX_DOUBLE_RESULT(result);
    DISPATCH();
  }

  {
    BYTECODE(DivDouble, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_DOUBLE(a, SP[0], Symbols::Slash());
    UNBOX_DOUBLE(b, SP[1], Symbols::Slash());
    double result = a / b;
    BOX_DOUBLE_RESULT(result);
    DISPATCH();
  }

  {
    BYTECODE(CompareDoubleEq, 0);
    DEBUG_CHECK;
    SP -= 1;
    if ((SP[0] == null_value) || (SP[1] == null_value)) {
      SP[0] = (SP[0] == SP[1]) ? true_value : false_value;
    } else {
      double a = Double::RawCast(SP[0])->untag()->value_;
      double b = Double::RawCast(SP[1])->untag()->value_;
      SP[0] = (a == b) ? true_value : false_value;
    }
    DISPATCH();
  }

  {
    BYTECODE(CompareDoubleGt, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_DOUBLE(a, SP[0], Symbols::RAngleBracket());
    UNBOX_DOUBLE(b, SP[1], Symbols::RAngleBracket());
    SP[0] = (a > b) ? true_value : false_value;
    DISPATCH();
  }

  {
    BYTECODE(CompareDoubleLt, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_DOUBLE(a, SP[0], Symbols::LAngleBracket());
    UNBOX_DOUBLE(b, SP[1], Symbols::LAngleBracket());
    SP[0] = (a < b) ? true_value : false_value;
    DISPATCH();
  }

  {
    BYTECODE(CompareDoubleGe, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_DOUBLE(a, SP[0], Symbols::GreaterEqualOperator());
    UNBOX_DOUBLE(b, SP[1], Symbols::GreaterEqualOperator());
    SP[0] = (a >= b) ? true_value : false_value;
    DISPATCH();
  }

  {
    BYTECODE(CompareDoubleLe, 0);
    DEBUG_CHECK;
    SP -= 1;
    UNBOX_DOUBLE(a, SP[0], Symbols::LessEqualOperator());
    UNBOX_DOUBLE(b, SP[1], Symbols::LessEqualOperator());
    SP[0] = (a <= b) ? true_value : false_value;
    DISPATCH();
  }

  {
    BYTECODE(AllocateClosure, D);
    ++SP;
    if (!AllocateClosure(thread, pc, FP, SP)) {
      HANDLE_EXCEPTION;
    }
    DISPATCH();
  }

  {
    BYTECODE_ENTRY_LABEL(Trap);

#define UNIMPLEMENTED_LABEL_ORDN(Name)
#define UNIMPLEMENTED_LABEL_WIDE(Name)
#define UNIMPLEMENTED_LABEL_RESV(Name) BYTECODE_ENTRY_LABEL(Name)
#define UNIMPLEMENTED_LABEL(name, encoding, kind, op1, op2, op3)               \
  UNIMPLEMENTED_LABEL_##kind(name)

    KERNEL_BYTECODES_LIST(UNIMPLEMENTED_LABEL)

#undef UNIMPLEMENTED_LABEL_ORDN
#undef UNIMPLEMENTED_LABEL_WIDE
#undef UNIMPLEMENTED_LABEL_RESV
#undef UNIMPLEMENTED_LABEL

    UNIMPLEMENTED();
    DISPATCH();
  }

  {
    BYTECODE(VMInternal_ImplicitGetter, 0);

    FunctionPtr function = FrameFunction(FP);
    ASSERT(Function::Handle(function).kind() ==
           UntaggedFunction::kImplicitGetter);

    // Field object is cached in function's data_.
    FieldPtr field = static_cast<FieldPtr>(function->untag()->data_);
    intptr_t offset_in_words =
        Smi::Value(field->untag()->host_offset_or_field_id_);

    const intptr_t kArgc = 1;
    ObjectPtr instance =
        static_cast<ObjectPtr>(FrameArguments(FP, kArgc)[0]);
    ObjectPtr value =
        reinterpret_cast<ObjectPtr*>(instance->untag())[offset_in_words];

    if (UNLIKELY(value == Object::sentinel().ptr())) {
      SP[1] = 0;  // Result slot.
      SP[2] = instance;
      SP[3] = field;
      Exit(thread, FP, SP + 4, pc);
      INVOKE_RUNTIME(
          DRT_InitInstanceField,
          NativeArguments(thread, 2, /* argv */ SP + 2, /* ret val */ SP + 1));

      function = FrameFunction(FP);
      instance = static_cast<InstancePtr>(SP[2]);
      field = static_cast<FieldPtr>(SP[3]);
      offset_in_words = Smi::Value(field->untag()->host_offset_or_field_id_);
      value =
          reinterpret_cast<InstancePtr*>(instance->untag())[offset_in_words];
    }

    *++SP = value;

#if !defined(PRODUCT)
    if (UNLIKELY(Field::NeedsLoadGuardBit::decode(
            field->untag()->kind_bits_))) {
      if (!AssertAssignableField<true>(thread, pc, FP, SP, instance, field,
                                       value)) {
        HANDLE_EXCEPTION;
      }
      // Reload objects after the call which may trigger GC.
      field = static_cast<FieldPtr>(FrameFunction(FP)->untag()->data_);
      instance = static_cast<ObjectPtr>(FrameArguments(FP, kArgc)[0]);
      value = reinterpret_cast<ObjectPtr*>(instance->untag())[offset_in_words];
    }
#endif

    const bool unboxing =
        (field->untag()->is_nullable_ != kNullCid) &&
        Field::UnboxingCandidateBit::decode(field->untag()->kind_bits_);
    classid_t guarded_cid = field->untag()->guarded_cid_;
    if (unboxing && (guarded_cid == kDoubleCid) && supports_unboxed_doubles_) {
      ASSERT(FlowGraphCompiler::SupportsUnboxedDoubles());
      double raw_value = Double::RawCast(value)->untag()->value_;
      // AllocateDouble places result at SP[0]
      if (!AllocateDouble(thread, raw_value, pc, FP, SP)) {
        HANDLE_EXCEPTION;
      }
    } else if (unboxing && (guarded_cid == kFloat32x4Cid) &&
               supports_unboxed_simd128_) {
      simd128_value_t raw_value;
      raw_value.readFrom(Float32x4::RawCast(value)->untag()->value_);
      // AllocateFloat32x4 places result at SP[0]
      if (!AllocateFloat32x4(thread, raw_value, pc, FP, SP)) {
        HANDLE_EXCEPTION;
      }
    } else if (unboxing && (guarded_cid == kFloat64x2Cid) &&
               supports_unboxed_simd128_) {
      simd128_value_t raw_value;
      raw_value.readFrom(Float64x2::RawCast(value)->untag()->value_);
      // AllocateFloat64x2 places result at SP[0]
      if (!AllocateFloat64x2(thread, raw_value, pc, FP, SP)) {
        HANDLE_EXCEPTION;
      }
    }

    DISPATCH();
  }

  {
    BYTECODE(VMInternal_ImplicitSetter, 0);

    FunctionPtr function = FrameFunction(FP);
    ASSERT(Function::Handle(function).kind() ==
           UntaggedFunction::kImplicitSetter);

    // Field object is cached in function's data_.
    FieldPtr field = static_cast<FieldPtr>(function->untag()->data_);
    intptr_t offset_in_words =
        Smi::Value(field->untag()->host_offset_or_field_id_);
    const intptr_t kArgc = 2;
    ObjectPtr instance =
        static_cast<ObjectPtr>(FrameArguments(FP, kArgc)[0]);
    ObjectPtr value = static_cast<ObjectPtr>(FrameArguments(FP, kArgc)[1]);

    if (!AssertAssignableField<false>(thread, pc, FP, SP, instance, field,
                                      value)) {
      HANDLE_EXCEPTION;
    }
    // Reload objects after the call which may trigger GC.
    field = static_cast<FieldPtr>(FrameFunction(FP)->untag()->data_);
    instance = static_cast<ObjectPtr>(FrameArguments(FP, kArgc)[0]);
    value = static_cast<ObjectPtr>(FrameArguments(FP, kArgc)[1]);

    if (InterpreterHelpers::FieldNeedsGuardUpdate(field, value)) {
      SP[1] = 0;  // Unused result of runtime call.
      SP[2] = field;
      SP[3] = value;
      Exit(thread, FP, SP + 4, pc);
      if (!InvokeRuntime(thread, this, DRT_UpdateFieldCid,
                         NativeArguments(thread, 2, /* argv */ SP + 2,
                                         /* retval */ SP + 1))) {
        HANDLE_EXCEPTION;
      }

      // Reload objects after the call which may trigger GC.
      field = static_cast<FieldPtr>(FrameFunction(FP)->untag()->data_);
      instance = static_cast<ObjectPtr>(FrameArguments(FP, kArgc)[0]);
      value = static_cast<ObjectPtr>(FrameArguments(FP, kArgc)[1]);
    }

    const bool unboxing =
        (field->untag()->is_nullable_ != kNullCid) &&
        Field::UnboxingCandidateBit::decode(field->untag()->kind_bits_);
    classid_t guarded_cid = field->untag()->guarded_cid_;
    if (unboxing && (guarded_cid == kDoubleCid) && supports_unboxed_doubles_) {
      double raw_value = Double::RawCast(value)->untag()->value_;
      DoublePtr box =
          *(reinterpret_cast<DoublePtr*>(instance->untag()) + offset_in_words);
      ASSERT(box != null_value);  // Non-initializing store.
      box->untag()->value_ = raw_value;
    } else if (unboxing && (guarded_cid == kFloat32x4Cid) &&
               supports_unboxed_simd128_) {
      simd128_value_t raw_value;
      raw_value.readFrom(Float32x4::RawCast(value)->untag()->value_);
      Float32x4Ptr box =
          *(reinterpret_cast<Float32x4Ptr*>(instance->untag()) +
            offset_in_words);
      ASSERT(box != null_value);  // Non-initializing store.
      raw_value.writeTo(box->untag()->value_);
    } else if (unboxing && (guarded_cid == kFloat64x2Cid) &&
               supports_unboxed_simd128_) {
      simd128_value_t raw_value;
      raw_value.readFrom(Float64x2::RawCast(value)->untag()->value_);
      Float64x2Ptr box =
          *(reinterpret_cast<Float64x2Ptr*>(instance->untag()) +
            offset_in_words);
      ASSERT(box != null_value);  // Non-initializing store.
      raw_value.writeTo(box->untag()->value_);
    } else {
      instance->untag()->StorePointer(
          reinterpret_cast<ObjectPtr*>(instance->untag()) + offset_in_words,
          value, thread);
    }

    *++SP = null_value;

    DISPATCH();
  }

  {
    BYTECODE(VMInternal_ImplicitStaticGetter, 0);

    FunctionPtr function = FrameFunction(FP);
    ASSERT(Function::Handle(function).kind() ==
           UntaggedFunction::kImplicitStaticGetter);

    // Field object is cached in function's data_.
    FieldPtr field = static_cast<FieldPtr>(function->untag()->data_);
    intptr_t field_id = Smi::Value(field->untag()->host_offset_or_field_id_);
    ObjectPtr value = thread->field_table_values()[field_id];
    if (value == Object::sentinel().ptr() ||
        value == Object::transition_sentinel().ptr()) {
      SP[1] = 0;  // Unused result of invoking the initializer.
      SP[2] = field;
      Exit(thread, FP, SP + 3, pc);
      INVOKE_RUNTIME(DRT_InitStaticField,
                     NativeArguments(thread, 1, SP + 2, SP + 1));

      // Reload objects after the call which may trigger GC.
      function = FrameFunction(FP);
      field = static_cast<FieldPtr>(function->untag()->data_);
      // The field is initialized by the runtime call, but not returned.
      intptr_t field_id = Smi::Value(field->untag()->host_offset_or_field_id_);
      value = thread->field_table_values()[field_id];
    }

    // Field was initialized. Return its value.
    *++SP = value;

#if !defined(PRODUCT)
    if (UNLIKELY(Field::NeedsLoadGuardBit::decode(
            field->untag()->kind_bits_))) {
      if (!AssertAssignableField<true>(thread, pc, FP, SP,
                                       static_cast<ObjectPtr>(null_value),
                                       field, value)) {
        HANDLE_EXCEPTION;
      }
    }
#endif

    DISPATCH();
  }

  {
    BYTECODE(VMInternal_MethodExtractor, 0);

    FunctionPtr function = FrameFunction(FP);
    ASSERT(Function::Handle(function).kind() ==
           UntaggedFunction::kMethodExtractor);

    ASSERT(InterpreterHelpers::ArgDescTypeArgsLen(argdesc_) == 0);

    ++SP;
    if (!AllocateClosure(thread, pc, FP, SP)) {
      HANDLE_EXCEPTION;
    }

    ++SP;
    if (!AllocateContext(thread, 1, pc, FP, SP)) {
      HANDLE_EXCEPTION;
    }

    ContextPtr context = Context::RawCast(*SP--);
    InstancePtr instance = Instance::RawCast(FrameArguments(FP, 1)[0]);
    context->untag()->StorePointer(
        reinterpret_cast<InstancePtr*>(&context->untag()->data()[0]), instance);

    ClosurePtr closure = Closure::RawCast(*SP);
    closure->untag()->StorePointer(
        &closure->untag()->instantiator_type_arguments_,
        InterpreterHelpers::GetTypeArguments(thread, instance));
    // function_type_arguments_ is already null
    closure->untag()->delayed_type_arguments_ =
        Object::empty_type_arguments().ptr();
    closure->untag()->StorePointer(
        &closure->untag()->function_,
        Function::RawCast(FrameFunction(FP)->untag()->data_));
    closure->untag()->StorePointer(&closure->untag()->context_, context);
    // hash_ is already null

    DISPATCH();
  }

  {
    BYTECODE(VMInternal_InvokeClosure, 0);

    FunctionPtr function = FrameFunction(FP);
    ASSERT(Function::Handle(function).kind() ==
           UntaggedFunction::kInvokeFieldDispatcher);
    const bool is_dynamic_call =
        Function::IsDynamicInvocationForwarderName(function->untag()->name_);

    const intptr_t type_args_len =
        InterpreterHelpers::ArgDescTypeArgsLen(argdesc_);
    const intptr_t receiver_idx = type_args_len > 0 ? 1 : 0;
    const intptr_t argc =
        InterpreterHelpers::ArgDescArgCount(argdesc_) + receiver_idx;

    ClosurePtr receiver =
        Closure::RawCast(FrameArguments(FP, argc)[receiver_idx]);
    SP[1] = receiver->untag()->function_;

    if (is_dynamic_call) {
      {
        SP[2] = null_value;
        SP[3] = receiver;
        SP[4] = argdesc_;
        Exit(thread, FP, SP + 5, pc);
        if (!InvokeRuntime(thread, this, DRT_ClosureArgumentsValid,
                           NativeArguments(thread, 2, SP + 3, SP + 2))) {
          HANDLE_EXCEPTION;
        }
        receiver = Closure::RawCast(SP[3]);
        argdesc_ = Array::RawCast(SP[4]);
      }

      if (SP[2] != Bool::True().ptr()) {
        goto NoSuchMethodFromPrologue;
      }

      // TODO(dartbug.com/40813): Move other checks that are currently
      // compiled in the closure body to here as they are also moved to
      // FlowGraphBuilder::BuildGraphOfInvokeFieldDispatcher.
    }

    goto TailCallSP1;
  }

  {
    BYTECODE(VMInternal_InvokeField, 0);

    FunctionPtr function = FrameFunction(FP);
    ASSERT(Function::Handle(function).kind() ==
           UntaggedFunction::kInvokeFieldDispatcher);

    const intptr_t type_args_len =
        InterpreterHelpers::ArgDescTypeArgsLen(argdesc_);
    const intptr_t receiver_idx = type_args_len > 0 ? 1 : 0;
    const intptr_t argc =
        InterpreterHelpers::ArgDescArgCount(argdesc_) + receiver_idx;
    ObjectPtr receiver = FrameArguments(FP, argc)[receiver_idx];

    // Possibly demangle field name and invoke field getter on receiver.
    {
      SP[1] = argdesc_;                // Save argdesc_.
      SP[2] = 0;                       // Result of runtime call.
      SP[3] = receiver;                // Receiver.
      SP[4] = function->untag()->name_;  // Field name (may change during call).
      Exit(thread, FP, SP + 5, pc);
      if (!InvokeRuntime(thread, this, DRT_GetFieldForDispatch,
                         NativeArguments(thread, 2, SP + 3, SP + 2))) {
        HANDLE_EXCEPTION;
      }
      function = FrameFunction(FP);
      argdesc_ = Array::RawCast(SP[1]);
    }

    // If the field name in the arguments is different after the call, then
    // this was a dynamic call.
    StringPtr field_name = String::RawCast(SP[4]);
    const bool is_dynamic_call = function->untag()->name_ != field_name;

    // Replace receiver with field value, keep all other arguments, and
    // invoke 'call' function, or if not found, invoke noSuchMethod.
    FrameArguments(FP, argc)[receiver_idx] = receiver = SP[2];

    // If the field value is a closure, no need to resolve 'call' function.
    if (InterpreterHelpers::GetClassId(receiver) == kClosureCid) {
      SP[1] = Closure::RawCast(receiver)->untag()->function_;

      if (is_dynamic_call) {
        {
          SP[2] = null_value;
          SP[3] = receiver;
          SP[4] = argdesc_;
          Exit(thread, FP, SP + 5, pc);
          if (!InvokeRuntime(thread, this, DRT_ClosureArgumentsValid,
                             NativeArguments(thread, 2, SP + 3, SP + 2))) {
            HANDLE_EXCEPTION;
          }
          receiver = SP[3];
          argdesc_ = Array::RawCast(SP[4]);
        }

        if (SP[2] != Bool::True().ptr()) {
          goto NoSuchMethodFromPrologue;
        }

        // TODO(dartbug.com/40813): Move other checks that are currently
        // compiled in the closure body to here as they are also moved to
        // FlowGraphBuilder::BuildGraphOfInvokeFieldDispatcher.
      }

      goto TailCallSP1;
    }

    // Otherwise, call runtime to resolve 'call' function.
    {
      SP[1] = 0;  // Result slot.
      SP[2] = receiver;
      SP[3] = argdesc_;
      Exit(thread, FP, SP + 4, pc);
      if (!InvokeRuntime(thread, this, DRT_ResolveCallFunction,
                         NativeArguments(thread, 2, SP + 2, SP + 1))) {
        HANDLE_EXCEPTION;
      }
      argdesc_ = Array::RawCast(SP[3]);
      function = Function::RawCast(SP[1]);
      receiver = SP[2];
    }

    if (function != Function::null()) {
      SP[1] = function;
      goto TailCallSP1;
    }

    // Function 'call' could not be resolved for argdesc_.
    // Invoke noSuchMethod.
    SP[1] = null_value;
    SP[2] = receiver;
    SP[3] = Symbols::Call().ptr();  // We failed to resolve the 'call' function.
    SP[4] = argdesc_;
    SP[5] = null_value;  // Array of arguments (will be filled).

    // Allocate array of arguments.
    {
      SP[6] = Smi::New(argc);  // length
      SP[7] = null_value;      // type
      Exit(thread, FP, SP + 8, pc);
      if (!InvokeRuntime(thread, this, DRT_AllocateArray,
                         NativeArguments(thread, 2, SP + 6, SP + 5))) {
        HANDLE_EXCEPTION;
      }
    }

    // Copy arguments into the newly allocated array.
    ObjectPtr* argv = FrameArguments(FP, argc);
    ArrayPtr array = static_cast<ArrayPtr>(SP[5]);
    ASSERT(array->GetClassId() == kArrayCid);
    for (intptr_t i = 0; i < argc; i++) {
      array->untag()->data()[i] = argv[i];
    }

    // Invoke noSuchMethod passing down receiver, target name, argument
    // descriptor, and array of arguments.
    {
      Exit(thread, FP, SP + 6, pc);
      if (!InvokeRuntime(thread, this, DRT_InvokeNoSuchMethod,
                         NativeArguments(thread, 4, SP + 2, SP + 1))) {
        HANDLE_EXCEPTION;
      }

      ++SP;  // Result at SP[0]
    }
    DISPATCH();
  }

  {
    BYTECODE(VMInternal_ForwardDynamicInvocation, 0);
    FunctionPtr function = FrameFunction(FP);
    ASSERT(Function::Handle(function).kind() ==
           UntaggedFunction::kDynamicInvocationForwarder);

    FunctionPtr target = Function::RawCast(function->untag()->data_);
    ASSERT(Function::Handle(function).kind() !=
           UntaggedFunction::kDynamicInvocationForwarder);
    BytecodePtr target_bytecode = target->untag()->bytecode_;
    ASSERT(target_bytecode != Bytecode::null());
    ASSERT(target_bytecode->IsBytecode());

    const KBCInstr* pc2 = reinterpret_cast<const KBCInstr*>(
        target_bytecode->untag()->instructions_);
    if (KernelBytecode::IsEntryOptionalOpcode(pc2)) {
      pp_ = target_bytecode->untag()->object_pool_;
      uint32_t rA, rB, rC;
      rA = KernelBytecode::DecodeA(pc2);
      rB = KernelBytecode::DecodeB(pc2);
      rC = KernelBytecode::DecodeC(pc2);
      pc2 = KernelBytecode::Next(pc2);
      if (!CopyParameters(thread, &pc2, &FP, &SP, rA, rB, rC)) {
        SP[1] = function;
        goto NoSuchMethodFromPrologue;
      }
    }

    SP[2] = argdesc_;

    const intptr_t type_args_len =
        InterpreterHelpers::ArgDescTypeArgsLen(argdesc_);
    const intptr_t receiver_idx = type_args_len > 0 ? 1 : 0;
    const intptr_t argc =
        InterpreterHelpers::ArgDescArgCount(argdesc_) + receiver_idx;

    InstancePtr receiver =
        Instance::RawCast(FrameArguments(FP, argc)[receiver_idx]);
    SP[5] = InterpreterHelpers::GetTypeArguments(thread, receiver);

    argdesc_ = Array::RawCast(SP[2]);

    SP = FP - 1;  // Unmarshall optional parameters.

    SP[1] = target;
    goto TailCallSP1;
  }

  {
    BYTECODE(VMInternal_NoSuchMethodDispatcher, 0);
    FunctionPtr function = FrameFunction(FP);
    ASSERT(Function::Handle(function).kind() ==
           UntaggedFunction::kNoSuchMethodDispatcher);
    SP[1] = function;
    goto NoSuchMethodFromPrologue;
  }

  {
    BYTECODE(VMInternal_ImplicitStaticClosure, 0);
    FunctionPtr function = FrameFunction(FP);
    ASSERT(Function::Handle(function).kind() ==
           UntaggedFunction::kImplicitClosureFunction);
    UNIMPLEMENTED();
    DISPATCH();
  }

  {
    BYTECODE(VMInternal_ImplicitInstanceClosure, 0);
    FunctionPtr function = FrameFunction(FP);
    ASSERT(Function::Handle(function).kind() ==
                   UntaggedFunction::kImplicitClosureFunction);
    UNIMPLEMENTED();
    DISPATCH();
  }

  {
  TailCallSP1:
    FunctionPtr function = Function::RawCast(SP[1]);
#if defined(DART_DYNAMIC_RUNTIME)
    intptr_t type_args_len =
            InterpreterHelpers::ArgDescTypeArgsLen(argdesc_);
    intptr_t receiver_idx = type_args_len > 0 ? 1 : 0;
    intptr_t argc =
            InterpreterHelpers::ArgDescArgCount(argdesc_) + receiver_idx;
    if (Function::Handle(function).kind() ==
        UntaggedFunction::kImplicitClosureFunction) {
      ClosurePtr receiver =
          Closure::RawCast(FrameArguments(FP, argc)[receiver_idx]);
      // implicit closure generated by bytecode
      if (!Function::HasCode(function)) {
        Function& callFunctionHandle = Function::Handle(function);
        FunctionPtr tmp = function;
        // machine code
        FunctionPtr parentFunc = callFunctionHandle.parent_function();
        if (Function::HasCode(parentFunc)) {
          tmp = parentFunc;
        }
        if (!callFunctionHandle.is_static()) {
          // update receiver for non static function
          Object& obj = Object::Handle(receiver);
          if (obj.IsClosure()) {
            const Closure& closure = Closure::Cast(obj);
            ObjectPtr instanceObj =
                Context::Handle(closure.context()).At(0);
            if (closure.function() == function && instanceObj != receiver) {
              FrameArguments(FP, argc)[receiver_idx] = instanceObj;
#if defined(ENABLE_DEBUG_INTERPRETER)
              OS::PrintErr("ImplicitClosureFunction fix4 instance");
#endif
            }
          }
        } else {
          // remove closure argument for static
          if (receiver_idx == 1) {
            ObjectPtr obj = FrameArguments(FP, argc)[0];
            FrameArguments(FP, argc)[0] = FrameArguments(FP, argc)[1];
            FrameArguments(FP, argc)[1] = obj;
          }
          Exit(thread, FP, SP + 1, pc);
          ArgumentsDescriptor ads =
              ArgumentsDescriptor(Array::Handle(argdesc_));
          intptr_t namedCount =  ads.NamedCount();
          if (namedCount > 0) {
            Array& namesArr = Array::Handle(Array::New(namedCount));
            for (int j = 0; j < namedCount; j++) {
                namesArr.SetAt(j, String::Handle(ads.NameAt(j)));
            }
            argdesc_ = ArgumentsDescriptor::NewBoxed(
                type_args_len, argc-receiver_idx-1, namesArr);
          } else {
            argdesc_ = ArgumentsDescriptor::NewBoxed(type_args_len,
                                                   argc-receiver_idx-1);
          }
          Unexit(thread);
          argc -= 1;
#if defined(ENABLE_DEBUG_INTERPRETER)
          OS::PrintErr("ImplicitClosureFunction fix3 static argcount");
#endif
        }
        function = tmp;
        SP[1] = function;
      }
    }

    if (Function::HasCode(function)) {
      ObjectPtr* argv = FrameArguments(FP, argc);
      for (intptr_t i = 0; i < argc; i++) {
        *++SP = argv[i];
      }

      ObjectPtr* call_base = SP - argc + 1;
      ObjectPtr* call_top = SP + 1;
      call_top[0] = function;
      if (!InvokeCompiled(thread, function, call_base, call_top, &pc, &FP,
                          &SP)) {
        HANDLE_EXCEPTION;
      } else {
        HANDLE_RETURN;
      }
      DISPATCH();
    }

    if (!Function::HasBytecode(function)) {
      SP[1] = argdesc_;
      SP[2] = 0;  // Code result.
      SP[3] = function;
      Exit(thread, FP, SP + 4, pc);
      if (!InvokeRuntime(thread, this, DRT_CompileFunction,
                     NativeArguments(thread, 1, /* argv */ SP + 3,
                                        /* retval */ SP + 2))) {
        HANDLE_EXCEPTION;
      }
      function = Function::RawCast(SP[3]);
      argdesc_ = Array::RawCast(SP[1]);
    }

#if defined(ENABLE_DEBUG_INTERPRETER)
    logCount++;
    OS::PrintErr("%dBegin CallBC3 %s ", logCount,
                Function::Handle(function).ToFullyQualifiedCString());
#endif
    if (Function::HasBytecode(function)) {
      ASSERT(function->IsFunction());
      BytecodePtr bytecode = function->untag()->bytecode_;
      ASSERT(bytecode->IsBytecode());
      FP[kKBCFunctionSlotFromFp] = function;
      FP[kKBCPcMarkerSlotFromFp] = bytecode;
      pp_ = bytecode->untag()->object_pool_;
      pc = reinterpret_cast<const KBCInstr*>(bytecode->untag()->instructions_);
#if defined(DART_DYNAMIC_RUNTIME) || !defined (PRODUCT)
      pc_ = pc;
#endif
      DISPATCH();
    } else {
        OS::PrintErr("%s has no code and no bytecode",
                   Function::Handle(function).ToFullyQualifiedCString());
    }
#else
    for (;;) {
      if (Function::HasBytecode(function)) {
        ASSERT(function->IsFunction());
        BytecodePtr bytecode = function->untag()->bytecode_;
        ASSERT(bytecode->IsBytecode());
        FP[kKBCFunctionSlotFromFp] = function;
        FP[kKBCPcMarkerSlotFromFp] = bytecode;
        pp_ = bytecode->untag()->object_pool_;
        pc = reinterpret_cast<const KBCInstr*>(
            bytecode->untag()->instructions_);
#if defined(DART_DYNAMIC_RUNTIME) || !defined (PRODUCT)
        pc_ = pc;
#endif
        DISPATCH();
      }

      if (Function::HasCode(function)) {
        const intptr_t type_args_len =
            InterpreterHelpers::ArgDescTypeArgsLen(argdesc_);
        const intptr_t receiver_idx = type_args_len > 0 ? 1 : 0;
        const intptr_t argc =
            InterpreterHelpers::ArgDescArgCount(argdesc_) + receiver_idx;
        ObjectPtr* argv = FrameArguments(FP, argc);
        for (intptr_t i = 0; i < argc; i++) {
          *++SP = argv[i];
        }

        ObjectPtr* call_base = SP - argc + 1;
        ObjectPtr* call_top = SP + 1;
        call_top[0] = function;
        if (!InvokeCompiled(thread, function, call_base, call_top, &pc, &FP,
                            &SP)) {
          HANDLE_EXCEPTION;
        } else {
          HANDLE_RETURN;
        }
        DISPATCH();
      }

      // Compile the function to either generate code or load bytecode.
      SP[1] = argdesc_;
      SP[2] = 0;  // Code result.
      SP[3] = function;
      Exit(thread, FP, SP + 4, pc);
      if (!InvokeRuntime(thread, this, DRT_CompileFunction,
                         NativeArguments(thread, 1, /* argv */ SP + 3,
                                         /* retval */ SP + 2))) {
        HANDLE_EXCEPTION;
      }
      function = Function::RawCast(SP[3]);
      argdesc_ = Array::RawCast(SP[1]);

      ASSERT(Function::HasCode(function) || Function::HasBytecode(function));
    }
#endif
  }

  // Helper used to handle noSuchMethod on closures. The function should be
  // placed into SP[1] before jumping here, similar to TailCallSP1.
  {
  NoSuchMethodFromPrologue:
    FunctionPtr function = Function::RawCast(SP[1]);

    const intptr_t type_args_len =
        InterpreterHelpers::ArgDescTypeArgsLen(argdesc_);
    const intptr_t receiver_idx = type_args_len > 0 ? 1 : 0;
    const intptr_t argc =
        InterpreterHelpers::ArgDescArgCount(argdesc_) + receiver_idx;
    ObjectPtr* args = FrameArguments(FP, argc);

    SP[1] = null_value;
    SP[2] = args[receiver_idx];
    SP[3] = function;
    SP[4] = argdesc_;
    SP[5] = null_value;  // Array of arguments (will be filled).

    // Allocate array of arguments.
    {
      SP[6] = Smi::New(argc);  // length
      SP[7] = null_value;      // type
      Exit(thread, FP, SP + 8, pc);
      if (!InvokeRuntime(thread, this, DRT_AllocateArray,
                         NativeArguments(thread, 2, SP + 6, SP + 5))) {
        HANDLE_EXCEPTION;
      }

      // Copy arguments into the newly allocated array.
      ArrayPtr array = static_cast<ArrayPtr>(SP[5]);
      ASSERT(array->GetClassId() == kArrayCid);
      for (intptr_t i = 0; i < argc; i++) {
        array->untag()->data()[i] = args[i];
      }
    }

    // Invoke noSuchMethod passing down receiver, function, argument descriptor
    // and array of arguments.
    {
      Exit(thread, FP, SP + 6, pc);
      INVOKE_RUNTIME(DRT_NoSuchMethodFromPrologue,
                     NativeArguments(thread, 4, SP + 2, SP + 1));
      ++SP;  // Result at SP[0]
    }

    DISPATCH();
  }

  {
  ThrowNullError:
    // SP[0] contains selector.
    SP[1] = 0;  // Unused space for result.
    Exit(thread, FP, SP + 2, pc);
    INVOKE_RUNTIME(DRT_NullErrorWithSelector,
                   NativeArguments(thread, 1, SP, SP + 1));
    UNREACHABLE();
  }

  {
  ThrowIntegerDivisionByZeroException:
    SP[0] = 0;  // Unused space for result.
    Exit(thread, FP, SP + 1, pc);
    INVOKE_RUNTIME(DRT_IntegerDivisionByZeroException,
                   NativeArguments(thread, 0, SP, SP));
    UNREACHABLE();
  }

  {
  ThrowArgumentError:
    // SP[0] contains value.
    SP[1] = 0;  // Unused space for result.
    Exit(thread, FP, SP + 2, pc);
    INVOKE_RUNTIME(DRT_ArgumentError, NativeArguments(thread, 1, SP, SP + 1));
    UNREACHABLE();
  }

  // Exception handling helper. Gets handler FP and PC from the Interpreter
  // where they were stored by Interpreter::Longjmp and proceeds to execute the
  // handler. Corner case: handler PC can be a fake marker that marks entry
  // frame, which means exception was not handled in the interpreter. In this
  // case we return the caught exception from Interpreter::Call.
  {
  HandleException:
    FP = fp_;
    pc = pc_;
    if (IsEntryFrameMarker(pc)) {
      pp_ = static_cast<ObjectPoolPtr>(fp_[kKBCSavedPpSlotFromEntryFp]);
      argdesc_ = static_cast<ArrayPtr>(fp_[kKBCSavedArgDescSlotFromEntryFp]);
      uword exit_fp = static_cast<uword>(fp_[kKBCExitLinkSlotFromEntryFp]);
      thread->set_top_exit_frame_info(exit_fp);
      thread->set_top_resource(top_resource);
      thread->set_vm_tag(vm_tag);
#if defined(DEBUG)
      if (IsTracingExecution()) {
        THR_Print("%" Pu64 " ", icount_);
        THR_Print("Returning exception from interpreter 0x%" Px " at fp_ 0x%" Px
                  " exit 0x%" Px "\n",
                  reinterpret_cast<uword>(this), reinterpret_cast<uword>(fp_),
                  exit_fp);
      }
#endif
      ASSERT(HasFrame(reinterpret_cast<uword>(fp_)));
      return special_[KernelBytecode::kExceptionSpecialIndex];
    }

    pp_ = InterpreterHelpers::FrameBytecode(FP)->untag()->object_pool_;
    DISPATCH();
  }

  UNREACHABLE();
  return 0;
}

void Interpreter::JumpToFrame(uword pc, uword sp, uword fp, Thread* thread) {
  // Walk over all setjmp buffers (simulated --> C++ transitions)
  // and try to find the setjmp associated with the simulated frame pointer.
  InterpreterSetjmpBuffer* buf = last_setjmp_buffer();
  while ((buf->link() != NULL) && (buf->link()->fp() > fp)) {
    buf = buf->link();
  }
  ASSERT(buf != NULL);
  ASSERT(last_setjmp_buffer() == buf);

  // The C++ caller has not cleaned up the stack memory of C++ frames.
  // Prepare for unwinding frames by destroying all the stack resources
  // in the previous C++ frames.
  StackResource::Unwind(thread);

  fp_ = reinterpret_cast<ObjectPtr*>(fp);

  if (pc == StubCode::RunExceptionHandler().EntryPoint()) {
    // The RunExceptionHandler stub is a placeholder.  We implement
    // its behavior here.
    ObjectPtr raw_exception = thread->active_exception();
    ObjectPtr raw_stacktrace = thread->active_stacktrace();
    ASSERT(raw_exception != Object::null());
    thread->set_active_exception(Object::null_object());
    thread->set_active_stacktrace(Object::null_object());
    special_[KernelBytecode::kExceptionSpecialIndex] = raw_exception;
    special_[KernelBytecode::kStackTraceSpecialIndex] = raw_stacktrace;
    pc_ = reinterpret_cast<const KBCInstr*>(thread->resume_pc());
  } else {
    pc_ = reinterpret_cast<const KBCInstr*>(pc);
  }

  // Set the tag.
  thread->set_vm_tag(VMTag::kDartInterpretedTagId);
  // Clear top exit frame.
  thread->set_top_exit_frame_info(0);

  buf->Longjmp();
  UNREACHABLE();
}

void Interpreter::VisitObjectPointers(ObjectPointerVisitor* visitor) {
  visitor->VisitPointer(reinterpret_cast<ObjectPtr*>(&pp_));
  visitor->VisitPointer(reinterpret_cast<ObjectPtr*>(&argdesc_));
}

}  // namespace dart

#endif  // !defined(DART_PRECOMPILED_RUNTIME)
