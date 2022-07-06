// Copyright (c) 2018, the Dart project authors.  Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include <string>
#include <map>

#include "vm/compiler/frontend/bytecode_reader.h"

#include "vm/bit_vector.h"
#include "vm/bootstrap.h"
#include "vm/class_finalizer.h"
#include "vm/class_id.h"
#include "vm/code_descriptors.h"
#include "vm/compiler/aot/precompiler.h"  // For Obfuscator
#include "vm/compiler/assembler/disassembler_kbc.h"
#if !defined(DART_DYNAMIC_RUNTIME)
#include "vm/compiler/frontend/bytecode_scope_builder.h"
#else
#include "vm/parser.h"
#endif
#include "vm/constants_kbc.h"
#include "vm/dart_api_impl.h"  // For Api::IsFfiEnabled().
#include "vm/dart_entry.h"
#include "vm/debugger.h"
#include "vm/flags.h"
#include "vm/hash.h"
#include "vm/longjump.h"
#include "vm/object_store.h"
#include "vm/resolver.h"
#include "vm/reusable_handles.h"
#include "vm/scopes.h"
#include "vm/stack_frame_kbc.h"
#include "vm/timeline.h"
#include "vm/closure_functions_cache.h"

#if !defined(DART_PRECOMPILED_RUNTIME) || defined(DART_DYNAMIC_RUNTIME)

#define Z (zone_)
#define H (translation_helper_)
#define I (translation_helper_.isolate())
#define IG (translation_helper_.isolate_group())

namespace dart {

DEFINE_FLAG(bool, dump_kernel_bytecode, false, "Dump kernel bytecode");

namespace kernel {

BytecodeMetadataHelper::BytecodeMetadataHelper(KernelReaderHelper* helper,
                                               ActiveClass* active_class)
    : MetadataHelper(helper, tag(), /* precompiler_only = */ false),
      active_class_(active_class) {}

#if !defined(DART_DYNAMIC_RUNTIME)
void BytecodeMetadataHelper::ParseBytecodeFunction(
    ParsedFunction* parsed_function) {
  TIMELINE_DURATION(Thread::Current(), CompilerVerbose,
                    "BytecodeMetadataHelper::ParseBytecodeFunction");

  const Function& function = parsed_function->function();
  ASSERT(function.is_declared_in_bytecode());

  BytecodeComponentData bytecode_component(
      &Array::Handle(helper_->zone_, GetBytecodeComponent()));
  BytecodeReaderHelper bytecode_reader(&H, active_class_, &bytecode_component);

  bytecode_reader.ParseBytecodeFunction(parsed_function, function);
}
#endif

bool BytecodeMetadataHelper::ReadLibraries() {
  TIMELINE_DURATION(Thread::Current(), Compiler,
                    "BytecodeMetadataHelper::ReadLibraries");
  ASSERT(Thread::Current()->IsMutatorThread());

  if (translation_helper_.GetBytecodeComponent() == Array::null()) {
    return false;
  }

  BytecodeComponentData bytecode_component(
      &Array::Handle(helper_->zone_, GetBytecodeComponent()));

  BytecodeReaderHelper bytecode_reader(&H, active_class_, &bytecode_component);
  AlternativeReadingScope alt(&bytecode_reader.reader(),
                              bytecode_component.GetLibraryIndexOffset());
  bytecode_reader.ReadLibraryDeclarations(bytecode_component.GetNumLibraries());
  return true;
}

void BytecodeMetadataHelper::ReadLibrary(const Library& library) {
  TIMELINE_DURATION(Thread::Current(), Compiler,
                    "BytecodeMetadataHelper::ReadLibrary");
  ASSERT(Thread::Current()->IsMutatorThread());
  ASSERT(!library.Loaded());

  if (translation_helper_.GetBytecodeComponent() == Array::null()) {
    return;
  }

  BytecodeComponentData bytecode_component(
      &Array::Handle(helper_->zone_, GetBytecodeComponent()));
  BytecodeReaderHelper bytecode_reader(&H, active_class_, &bytecode_component);
  AlternativeReadingScope alt(&bytecode_reader.reader(),
                              bytecode_component.GetLibraryIndexOffset());
  bytecode_reader.FindAndReadSpecificLibrary(
      library, bytecode_component.GetNumLibraries());
}

bool BytecodeMetadataHelper::FindModifiedLibrariesForHotReload(
    BitVector* modified_libs,
    bool* is_empty_program,
    intptr_t* p_num_classes,
    intptr_t* p_num_procedures) {
  ASSERT(Thread::Current()->IsMutatorThread());

  if (translation_helper_.GetBytecodeComponent() == Array::null()) {
    return false;
  }

  BytecodeComponentData bytecode_component(
      &Array::Handle(helper_->zone_, GetBytecodeComponent()));
  BytecodeReaderHelper bytecode_reader(&H, active_class_, &bytecode_component);
  AlternativeReadingScope alt(&bytecode_reader.reader(),
                              bytecode_component.GetLibraryIndexOffset());
  bytecode_reader.FindModifiedLibrariesForHotReload(
      modified_libs, bytecode_component.GetNumLibraries());

  if (is_empty_program != nullptr) {
    *is_empty_program = (bytecode_component.GetNumLibraries() == 0);
  }
  if (p_num_classes != nullptr) {
    *p_num_classes = bytecode_component.GetNumClasses();
  }
  if (p_num_procedures != nullptr) {
    *p_num_procedures = bytecode_component.GetNumCodes();
  }
  return true;
}

LibraryPtr BytecodeMetadataHelper::GetMainLibrary() {
  const intptr_t md_offset = GetComponentMetadataPayloadOffset();
  if (md_offset < 0) {
    return Library::null();
  }

  BytecodeComponentData bytecode_component(
      &Array::Handle(helper_->zone_, GetBytecodeComponent()));
  const intptr_t main_offset = bytecode_component.GetMainOffset();
  if (main_offset == 0) {
    return Library::null();
  }

  BytecodeReaderHelper bytecode_reader(&H, active_class_, &bytecode_component);
  AlternativeReadingScope alt(&bytecode_reader.reader(), main_offset);
  return bytecode_reader.ReadMain();
}

ArrayPtr BytecodeMetadataHelper::GetBytecodeComponent() {
  ArrayPtr array = translation_helper_.GetBytecodeComponent();
  if (array == Array::null()) {
    array = ReadBytecodeComponent();
    ASSERT(array != Array::null());
  }
  return array;
}

ArrayPtr BytecodeMetadataHelper::ReadBytecodeComponent() {
  const intptr_t md_offset = GetComponentMetadataPayloadOffset();
  if (md_offset < 0) {
    return Array::null();
  }

  BytecodeReaderHelper component_reader(&H, nullptr, nullptr);
  return component_reader.ReadBytecodeComponent(md_offset);
}

BytecodeReaderHelper::BytecodeReaderHelper(
    TranslationHelper* translation_helper,
    ActiveClass* active_class,
    BytecodeComponentData* bytecode_component)
    : reader_(translation_helper->metadata_payloads()),
      translation_helper_(*translation_helper),
      active_class_(active_class),
      thread_(translation_helper->thread()),
      zone_(translation_helper->zone()),
      bytecode_component_(bytecode_component),
      scoped_function_(Function::Handle(translation_helper->zone())),
      scoped_function_name_(String::Handle(translation_helper->zone())),
      scoped_function_class_(Class::Handle(translation_helper->zone())) {}

void BytecodeReaderHelper::ReadCode(const Function& function,
                                    intptr_t code_offset) {
  ASSERT(Thread::Current()->IsMutatorThread());
  ASSERT(!function.IsImplicitGetterFunction() &&
         !function.IsImplicitSetterFunction());
  if (code_offset == 0) {
    FATAL2("Function %s (kind %s) doesn't have bytecode",
           function.ToFullyQualifiedCString(),
           Function::KindToCString(function.kind()));
  }

  AlternativeReadingScope alt(&reader_, code_offset);
  // This scope is needed to set active_class_->enclosing_ which is used to
  // assign parent function for function types.
  FunctionType& sig = FunctionType::Handle(zone_, function.signature());
  ActiveEnclosingFunctionScope active_enclosing_function(active_class_,
                                                         &sig);

  const intptr_t flags = reader_.ReadUInt();
  const bool has_exceptions_table =
      (flags & Code::kHasExceptionsTableFlag) != 0;
  const bool has_source_positions =
      (flags & Code::kHasSourcePositionsFlag) != 0;
  const bool has_local_variables = (flags & Code::kHasLocalVariablesFlag) != 0;
  const bool has_nullable_fields = (flags & Code::kHasNullableFieldsFlag) != 0;
  const bool has_closures = (flags & Code::kHasClosuresFlag) != 0;
  const bool has_parameter_flags = (flags & Code::kHasParameterFlagsFlag) != 0;
  const bool has_forwarding_stub_target =
      (flags & Code::kHasForwardingStubTargetFlag) != 0;
  const bool has_default_function_type_args =
      (flags & Code::kHasDefaultFunctionTypeArgsFlag) != 0;

  if (has_parameter_flags) {
    intptr_t num_flags = reader_.ReadUInt();
    for (intptr_t i = 0; i < num_flags; ++i) {
      reader_.ReadUInt();
    }
  }
  if (has_forwarding_stub_target) {
    reader_.ReadUInt();
  }
  if (has_default_function_type_args) {
    reader_.ReadUInt();
  }

  intptr_t num_closures = 0;
  if (has_closures) {
    num_closures = reader_.ReadListLength();
    closures_ = &Array::Handle(Z, Array::New(num_closures));
    for (intptr_t i = 0; i < num_closures; i++) {
      ReadClosureDeclaration(function, i);
    }
  }

  // Create object pool and read pool entries.
  const intptr_t obj_count = reader_.ReadListLength();
  const ObjectPool& pool = ObjectPool::Handle(Z, ObjectPool::New(obj_count));
  ReadConstantPool(function, pool, 0);

  // Read bytecode and attach to function.
  const Bytecode& bytecode = Bytecode::Handle(Z, ReadBytecode(pool));
  function.AttachBytecode(bytecode);
  ASSERT(bytecode.GetBinary(Z) == reader_.typed_data()->ptr());

  ReadExceptionsTable(bytecode, has_exceptions_table);

  ReadSourcePositions(bytecode, has_source_positions);

  ReadLocalVariables(bytecode, has_local_variables);

  if (FLAG_dump_kernel_bytecode) {
    KernelBytecodeDisassembler::Disassemble(function);
  }

  // Initialization of fields with null literal is elided from bytecode.
  // Record the corresponding stores if field guards are enabled.
  if (has_nullable_fields) {
    ASSERT(function.IsGenerativeConstructor());
    const intptr_t num_fields = reader_.ReadListLength();
    if (I->group()->use_field_guards()) {
      Field& field = Field::Handle(Z);
      for (intptr_t i = 0; i < num_fields; i++) {
        field ^= ReadObject();
        field.RecordStore(Object::null_object());
      }
    } else {
      for (intptr_t i = 0; i < num_fields; i++) {
        ReadObject();
      }
    }
  }

  // Read closures.
  if (has_closures) {
    Function& closure = Function::Handle(Z);
    Bytecode& closure_bytecode = Bytecode::Handle(Z);
    for (intptr_t i = 0; i < num_closures; i++) {
      closure ^= closures_->At(i);

      const intptr_t flags = reader_.ReadUInt();
      const bool has_exceptions_table =
          (flags & ClosureCode::kHasExceptionsTableFlag) != 0;
      const bool has_source_positions =
          (flags & ClosureCode::kHasSourcePositionsFlag) != 0;
      const bool has_local_variables =
          (flags & ClosureCode::kHasLocalVariablesFlag) != 0;

      // Read closure bytecode and attach to closure function.
      closure_bytecode = ReadBytecode(pool);
      closure.AttachBytecode(closure_bytecode);
      ASSERT(bytecode.GetBinary(Z) == reader_.typed_data()->ptr());

      ReadExceptionsTable(closure_bytecode, has_exceptions_table);

      ReadSourcePositions(closure_bytecode, has_source_positions);

      ReadLocalVariables(closure_bytecode, has_local_variables);

      if (FLAG_dump_kernel_bytecode) {
        KernelBytecodeDisassembler::Disassemble(closure);
      }
    }
  }
}

static intptr_t IndexFor(Zone* zone,
                         const Function& function,
                         const String& name) {
  const Bytecode& bc = Bytecode::Handle(zone, function.bytecode());
  const ObjectPool& pool = ObjectPool::Handle(zone, bc.object_pool());
  const KBCInstr* pc = reinterpret_cast<const KBCInstr*>(bc.PayloadStart());

  ASSERT(KernelBytecode::IsEntryOptionalOpcode(pc));
  ASSERT(KernelBytecode::DecodeB(pc) ==
         function.NumOptionalPositionalParameters());
  ASSERT(KernelBytecode::DecodeC(pc) == function.NumOptionalNamedParameters());
  pc = KernelBytecode::Next(pc);

  const intptr_t num_opt_params = function.NumOptionalParameters();
  const intptr_t num_fixed_params = function.num_fixed_parameters();
  for (intptr_t i = 0; i < num_opt_params; i++) {
    const KBCInstr* load_name = pc;
    const KBCInstr* load_value = KernelBytecode::Next(load_name);
    pc = KernelBytecode::Next(load_value);
    ASSERT(KernelBytecode::IsLoadConstantOpcode(load_name));
    ASSERT(KernelBytecode::IsLoadConstantOpcode(load_value));
    if (pool.ObjectAt(KernelBytecode::DecodeE(load_name)) == name.ptr()) {
      return num_fixed_params + i;
    }
  }

  UNREACHABLE();
  return -1;
}

ArrayPtr BytecodeReaderHelper::CreateForwarderChecks(const Function& function) {
  ASSERT(function.kind() != UntaggedFunction::kDynamicInvocationForwarder);
  ASSERT(function.is_declared_in_bytecode());

  TypeArguments& default_args = TypeArguments::Handle(Z);
  if (function.bytecode_offset() != 0) {
    AlternativeReadingScope alt(&reader_, function.bytecode_offset());

    const intptr_t flags = reader_.ReadUInt();
    const bool has_parameter_flags =
        (flags & Code::kHasParameterFlagsFlag) != 0;
    const bool has_forwarding_stub_target =
        (flags & Code::kHasForwardingStubTargetFlag) != 0;
    const bool has_default_function_type_args =
        (flags & Code::kHasDefaultFunctionTypeArgsFlag) != 0;

    if (has_parameter_flags) {
      intptr_t num_flags = reader_.ReadUInt();
      for (intptr_t i = 0; i < num_flags; ++i) {
        reader_.ReadUInt();
      }
    }
    if (has_forwarding_stub_target) {
      reader_.ReadUInt();
    }

    if (has_default_function_type_args) {
      const intptr_t index = reader_.ReadUInt();
      const Bytecode& code = Bytecode::Handle(Z, function.bytecode());
      const ObjectPool& pool = ObjectPool::Handle(Z, code.object_pool());
      default_args ^= pool.ObjectAt(index);
    }
  }

  auto& name = String::Handle(Z);
  auto& check = ParameterTypeCheck::Handle(Z);
  auto& checks = GrowableObjectArray::Handle(Z, GrowableObjectArray::New());

  checks.Add(function);
  checks.Add(default_args);

  const auto& type_params =
      TypeParameters::Handle(Z, function.type_parameters());
  if (!type_params.IsNull()) {
    auto& type_param = TypeParameter::Handle(Z);
    auto& bound = AbstractType::Handle(Z);
    for (intptr_t i = 0, n = type_params.Length(); i < n; ++i) {
      bound = type_params.BoundAt(i);
      if (!bound.IsTopTypeForSubtyping() &&
          !type_params.IsGenericCovariantImplAt(i)) {
        name = type_params.NameAt(i);
        ASSERT(type_param.IsFinalized());
        check = ParameterTypeCheck::New();
        check.set_type_or_bound(bound);
        check.set_name(name);
        checks.Add(check);
      }
    }
  }

  const intptr_t num_params = function.NumParameters();
  const intptr_t num_pos_params = function.HasOptionalNamedParameters()
                                      ? function.num_fixed_parameters()
                                      : num_params;

  BitVector is_covariant(Z, num_params);
  BitVector is_generic_covariant_impl(Z, num_params);
  ReadParameterCovariance(function, &is_covariant, &is_generic_covariant_impl);

  auto& type = AbstractType::Handle(Z);
  auto& cache = SubtypeTestCache::Handle(Z);
  const bool has_optional_parameters = function.HasOptionalParameters();
  for (intptr_t i = function.NumImplicitParameters(); i < num_params; ++i) {
    type = function.ParameterTypeAt(i);
    if (!type.IsTopTypeForSubtyping() &&
        !is_generic_covariant_impl.Contains(i) && !is_covariant.Contains(i)) {
      name = function.ParameterNameAt(i);
      intptr_t index;
      if (i >= num_pos_params) {
        // Named parameter.
        index = IndexFor(Z, function, name);
      } else if (has_optional_parameters) {
        // Fixed or optional parameter.
        index = i;
      } else {
        // Fixed parameter.
        index = -kKBCParamEndSlotFromFp - num_params + i;
      }
      check = ParameterTypeCheck::New();
      check.set_index(index);
      check.set_type_or_bound(type);
      check.set_name(name);
      cache = SubtypeTestCache::New();
      check.set_cache(cache);
      checks.Add(check);
    }
  }

  return Array::MakeFixedLength(checks);
}

void BytecodeReaderHelper::ReadClosureDeclaration(const Function& function,
                                                  intptr_t closureIndex) {
  // Closure flags, must be in sync with ClosureDeclaration constants in
  // pkg/vm/lib/bytecode/declarations.dart.
  const int kHasOptionalPositionalParamsFlag = 1 << 0;
  const int kHasOptionalNamedParamsFlag = 1 << 1;
  const int kHasTypeParamsFlag = 1 << 2;
  const int kHasSourcePositionsFlag = 1 << 3;
  const int kIsAsyncFlag = 1 << 4;
  const int kIsAsyncStarFlag = 1 << 5;
  const int kIsSyncStarFlag = 1 << 6;
  const int kIsDebuggableFlag = 1 << 7;
  const int kHasAttributesFlag = 1 << 8;
  const int kHasParameterFlagsFlag = 1 << 9;

  const intptr_t flags = reader_.ReadUInt();

  Object& parent = Object::Handle(Z, ReadObject());
  if (!parent.IsFunction()) {
    ASSERT(parent.IsField());
    ASSERT(function.kind() == UntaggedFunction::kFieldInitializer);
    // Closure in a static field initializer, so use current function as parent.
    parent = function.ptr();
  }

  String& name = String::CheckedHandle(Z, ReadObject());
  ASSERT(name.IsSymbol());

  TokenPosition position = TokenPosition::kNoSource;
  TokenPosition end_position = TokenPosition::kNoSource;
  if ((flags & kHasSourcePositionsFlag) != 0) {
    position = reader_.ReadPosition();
    end_position = reader_.ReadPosition();
  }

  const Function& closure = Function::Handle(
      Z, Function::NewClosureFunction(name, Function::Cast(parent), position));

  closure.set_is_declared_in_bytecode(true);
  closure.set_end_token_pos(end_position);

  if ((flags & kIsSyncStarFlag) != 0) {
    closure.set_modifier(UntaggedFunction::kSyncGen);
  } else if ((flags & kIsAsyncFlag) != 0) {
    closure.set_modifier(UntaggedFunction::kAsync);
    closure.set_is_inlinable(!FLAG_lazy_async_stacks);
  } else if ((flags & kIsAsyncStarFlag) != 0) {
    closure.set_modifier(UntaggedFunction::kAsyncGen);
    closure.set_is_inlinable(!FLAG_lazy_async_stacks);
  }
  if (Function::Cast(parent).IsAsyncOrGenerator()) {
    closure.set_is_generated_body(true);
  }
  closure.set_is_debuggable((flags & kIsDebuggableFlag) != 0);

  closures_->SetAt(closureIndex, closure);

  Type& signature_type = Type::Handle(
      Z, ReadFunctionSignature(
             closure, (flags & kHasOptionalPositionalParamsFlag) != 0,
             (flags & kHasOptionalNamedParamsFlag) != 0,
             (flags & kHasTypeParamsFlag) != 0,
             /* has_positional_param_names = */ true,
             (flags & kHasParameterFlagsFlag) != 0, Nullability::kNonNullable));

  closure.set_signature(FunctionType::Cast(signature_type));

  if ((flags & kHasAttributesFlag) != 0) {
    ReadAttributes(closure);
  }

  ClosureFunctionsCache::AddClosureFunctionLocked(closure, true);
}

static bool IsNonCanonical(const AbstractType& type) {
  return type.IsTypeRef() || (type.IsType() && !type.IsCanonical());
}

static bool HasNonCanonicalTypes(Zone* zone, const Function& func) {
  auto& type = AbstractType::Handle(zone);
  for (intptr_t i = 0; i < func.NumParameters(); ++i) {
    type = func.ParameterTypeAt(i);
    if (IsNonCanonical(type)) {
      return true;
    }
  }
  type = func.result_type();
  if (IsNonCanonical(type)) {
    return true;
  }
  const auto& type_params =
      TypeParameters::Handle(zone, func.type_parameters());
  if (!type_params.IsNull()) {
    for (intptr_t i = 0; i < type_params.Length(); ++i) {
      if (IsNonCanonical(AbstractType::Handle(type_params.BoundAt(i)))) {
        return true;
      }
    }
  }
  return false;
}

TypePtr BytecodeReaderHelper::ReadFunctionSignature(
    const Function& func,
    bool has_optional_positional_params,
    bool has_optional_named_params,
    bool has_type_params,
    bool has_positional_param_names,
    bool has_parameter_flags,
    Nullability nullability) {
  FunctionTypeScope function_type_scope(this);

  if (has_type_params) {
    ReadTypeParametersDeclaration(Class::Handle(Z), func);
  }

  const intptr_t kImplicitClosureParam = 1;
  const intptr_t num_params = kImplicitClosureParam + reader_.ReadUInt();

  intptr_t num_required_params = num_params;
  if (has_optional_positional_params || has_optional_named_params) {
    num_required_params = kImplicitClosureParam + reader_.ReadUInt();
  }

  FunctionType& signature = FunctionType::Handle(Z, func.signature());

  signature.set_num_fixed_parameters(num_required_params);
  signature.SetNumOptionalParameters(num_params - num_required_params,
                                !has_optional_named_params);
  signature.set_parameter_types(
          Array::Handle(Z, Array::New(num_params, Heap::kOld)));
  func.CreateNameArray();
  signature.CreateNameArrayIncludingFlags();

  intptr_t i = 0;
  signature.SetParameterTypeAt(i, AbstractType::dynamic_type());
  func.SetParameterNameAt(i, Symbols::ClosureParameter());
  ++i;

  AbstractType& type = AbstractType::Handle(Z);
  String& name = String::Handle(Z);
  intptr_t num_params_all = !has_optional_named_params ? num_params :
                                                       num_required_params;
  for (; i < num_params_all; ++i) {
    if (has_positional_param_names ||
      (has_optional_named_params && (i >= num_required_params))) {
      name ^= ReadObject();
    } else {
      name = Symbols::NotNamed().ptr();
    }
    func.SetParameterNameAt(i, name);
    type ^= ReadObject();
    signature.SetParameterTypeAt(i, type);
  }
  for (; i < num_params; ++i) {
    if (has_positional_param_names ||
        (has_optional_named_params && (i >= num_required_params))) {
      name ^= ReadObject();
    } else {
      name = Symbols::NotNamed().ptr();
    }
    signature.SetParameterNameAt(i, name);
    type ^= ReadObject();
    signature.SetParameterTypeAt(i, type);
  }
  if (has_parameter_flags) {
    intptr_t num_flags = reader_.ReadUInt();
    for (intptr_t i = 0; i < num_flags; ++i) {
      intptr_t flag = reader_.ReadUInt();
      if ((flag & Parameter::kIsRequiredFlag) != 0) {
        RELEASE_ASSERT(kImplicitClosureParam + i >= num_required_params);
        signature.SetIsRequiredAt(kImplicitClosureParam + i);
      }
    }
  }
  signature.FinalizeNameArray();

  type ^= ReadObject();
  signature.set_result_type(type);

  // Finalize function type.
#if defined(DART_DYNAMIC_RUNTIME)
  signature.set_nullability2(nullability);
#endif
  ClassFinalizer::FinalizationKind finalization = ClassFinalizer::kCanonicalize;
  if (pending_recursive_types_ != nullptr && HasNonCanonicalTypes(Z, func)) {
    // This function type is a part of recursive type. Avoid canonicalization
    // as not all TypeRef objects are filled up at this point.
    finalization = ClassFinalizer::kFinalize;
  }
  // type = ClassFinalizer::FinalizeType(type, finalization);
  signature ^= ClassFinalizer::FinalizeType(signature, finalization);
  return Type::Cast(signature).ptr();
}

void BytecodeReaderHelper::ReadTypeParametersDeclaration2(
        const Class& parameterized_class,
        const Function& parameterized_function) {
  ASSERT(parameterized_class.IsNull() != parameterized_function.IsNull());

  const intptr_t num_type_params = reader_.ReadUInt();
  // parameterized_function.SetNumTypeParameters(num_type_params);
  ASSERT(num_type_params > 0);

  intptr_t offset;
  NNBDMode nnbd_mode;
  if (!parameterized_class.IsNull()) {
    offset = parameterized_class.NumTypeArguments() - num_type_params;
    nnbd_mode = parameterized_class.nnbd_mode();
  } else {
    offset = parameterized_function.NumParentTypeArguments();
    nnbd_mode = parameterized_function.nnbd_mode();
  }
  const Nullability nullability = (nnbd_mode == NNBDMode::kOptedInLib)
                                  ? Nullability::kNonNullable
                                  : Nullability::kLegacy;

  // First setup the type parameters, so if any of the following code uses it
  // (in a recursive way) we're fine.
  //
  // Step a) Create array of [TypeParameter] objects (without bound).
  const TypeParameters& type_parameters =
          TypeParameters::Handle(Z, TypeParameters::New(num_type_params));
  String& name = String::Handle(Z);
  TypeParameter& parameter = TypeParameter::Handle(Z);
  AbstractType& type = AbstractType::Handle(Z);
  for (intptr_t i = 0; i < num_type_params; ++i) {
    name ^= ReadObject();
    ASSERT(name.IsSymbol());
    parameter = TypeParameter::New(parameterized_class, offset,
                                   offset + i, /* bound = */ type,
                                   nullability);
    parameter.set_index(offset + i);
    parameter.SetIsFinalized();
    parameter.SetCanonical();
    // For functions, default type arguments aren't available here but with the
    // bytecode, so update any non-dynamic default arguments when reading the
    // bytecode. (For classes, we don't currently use this, so dynamic is fine.)
    // parameter.set_default_argument(Object::dynamic_type());
    type_parameters.SetDefaultAt(i, parameter);
    type_parameters.SetNameAt(i, name);
  }

  if (!parameterized_class.IsNull()) {
    parameterized_class.set_type_parameters(type_parameters);
  } else if (!parameterized_function.IsFactory()) {
    // Do not set type parameters for factories, as VM uses class type
    // parameters instead.
    const FunctionType& signature2 =
            FunctionType::Handle(Z, parameterized_function.signature());
    signature2.SetTypeParameters(type_parameters);
    parameterized_function.set_signature(signature2);
    if (parameterized_function.name() == Symbols::AnonymousSignature().ptr()) {
      function_type_type_parameters_ = &type_parameters;
    } else {
      ASSERT(function_type_type_parameters_ == nullptr);
    }
  }

  // Step b) Fill in the bounds of all [TypeParameter]s.
  for (intptr_t i = 0; i < num_type_params; ++i) {
    parameter ^= type_parameters.DefaultAt(i);
    type ^= ReadObject();
    // Convert dynamic to Object? or Object* in bounds of type parameters so
    // they are equivalent when doing subtype checks for function types.
    // TODO(https://github.com/dart-lang/language/issues/495): revise this
    // when function subtyping is fixed.
    if (type.IsDynamicType()) {
      type = nnbd_mode == NNBDMode::kOptedInLib
             ? I->group()->object_store()->nullable_object_type()
             : I->group()->object_store()->legacy_object_type();
    }
    type_parameters.SetBoundAt(i, type);
    parameter.set_bound(type);
  }

  // Fix bounds in all derived type parameters (with different nullabilities).
  if (active_class_->derived_type_parameters != nullptr) {
    auto& derived = TypeParameter::Handle(Z);
    auto& bound = AbstractType::Handle(Z);
    for (intptr_t i = 0, n = active_class_->derived_type_parameters->Length();
         i < n; ++i) {
      derived ^= active_class_->derived_type_parameters->At(i);
      if (derived.bound() == AbstractType::null() &&
          ((!parameterized_class.IsNull() &&
            derived.parameterized_class_id() == parameterized_class.id()))) {
        ASSERT(derived.IsFinalized());
        bound = type_parameters.BoundAt(derived.index() - offset);
        derived.set_bound(bound);
      }
    }
  }
}

void BytecodeReaderHelper::ReadTypeParametersDeclaration(
    const Class& parameterized_class,
    const Function& parameterized_function) {
  ASSERT(parameterized_class.IsNull() != parameterized_function.IsNull());

  const intptr_t num_type_params = reader_.ReadUInt();
  ASSERT(num_type_params > 0);

  intptr_t offset;
  NNBDMode nnbd_mode;
  if (!parameterized_class.IsNull()) {
    offset = parameterized_class.NumTypeArguments() - num_type_params;
    nnbd_mode = parameterized_class.nnbd_mode();
  } else {
    offset = parameterized_function.NumParentTypeArguments();
    nnbd_mode = parameterized_function.nnbd_mode();
  }
  const Nullability nullability = (nnbd_mode == NNBDMode::kOptedInLib)
                                      ? Nullability::kNonNullable
                                      : Nullability::kLegacy;

  // First setup the type parameters, so if any of the following code uses it
  // (in a recursive way) we're fine.
  //
  // Step a) Create array of [TypeParameter] objects (without bound).
  const TypeParameters& type_parameters =
      TypeParameters::Handle(Z, TypeParameters::New(num_type_params));
  String& name = String::Handle(Z);
  TypeParameter& parameter = TypeParameter::Handle(Z);
  AbstractType& type = AbstractType::Handle(Z);
  for (intptr_t i = 0; i < num_type_params; ++i) {
    name ^= ReadObject();
    ASSERT(name.IsSymbol());
    parameter = TypeParameter::New(parameterized_class, offset,
                                   offset + i, /* bound = */ type,
                                   nullability);
    parameter.set_index(offset + i);
    parameter.SetIsFinalized();
    parameter.SetCanonical();
    type_parameters.SetDefaultAt(i, parameter);
    type_parameters.SetNameAt(i, name);
  }

  if (!parameterized_class.IsNull()) {
    parameterized_class.set_type_parameters(type_parameters);
  } else if (!parameterized_function.IsFactory()) {
    // Do not set type parameters for factories, as VM uses class type
    // parameters instead.
    const FunctionType& signature2 =
                 FunctionType::Handle(Z, parameterized_function.signature());
    signature2.SetTypeParameters(type_parameters);
    parameterized_function.set_signature(signature2);
    if (parameterized_function.name() == Symbols::AnonymousSignature().ptr()) {
      function_type_type_parameters_ = &type_parameters;
    } else {
      ASSERT(function_type_type_parameters_ == nullptr);
    }
  }

  // Step b) Fill in the bounds of all [TypeParameter]s.
  for (intptr_t i = 0; i < num_type_params; ++i) {
    parameter ^= type_parameters.DefaultAt(i);
    type ^= ReadObject();
    // Convert dynamic to Object? or Object* in bounds of type parameters so
    // they are equivalent when doing subtype checks for function types.
    // TODO(https://github.com/dart-lang/language/issues/495): revise this
    // when function subtyping is fixed.
    if (type.IsDynamicType()) {
      type = nnbd_mode == NNBDMode::kOptedInLib
                 ? I->group()->object_store()->nullable_object_type()
                 : I->group()->object_store()->legacy_object_type();
    }
    type_parameters.SetBoundAt(i, type);
    parameter.set_bound(type);
  }

  // Fix bounds in all derived type parameters (with different nullabilities).
  if (active_class_->derived_type_parameters != nullptr) {
    auto& derived = TypeParameter::Handle(Z);
    auto& bound = AbstractType::Handle(Z);
    for (intptr_t i = 0, n = active_class_->derived_type_parameters->Length();
         i < n; ++i) {
      derived ^= active_class_->derived_type_parameters->At(i);
      if (derived.bound() == AbstractType::null() &&
          ((!parameterized_class.IsNull() &&
            derived.parameterized_class_id() == parameterized_class.id()))) {
        ASSERT(derived.IsFinalized());
        bound = type_parameters.BoundAt(derived.index() - offset);
        derived.set_bound(bound);
      }
    }
  }
}

intptr_t BytecodeReaderHelper::ReadConstantPool(const Function& function,
                                                const ObjectPool& pool,
                                                intptr_t start_index) {
  TIMELINE_DURATION(Thread::Current(), CompilerVerbose,
                    "BytecodeReaderHelper::ReadConstantPool");

  // These enums and the code below reading the constant pool from kernel must
  // be kept in sync with pkg/vm/lib/bytecode/constant_pool.dart.
  enum ConstantPoolTag {
    kInvalid,
    kUnused1,
    kUnused2,
    kUnused3,
    kUnused4,
    kUnused5,
    kUnused6,
    kUnused6a,
    kUnused7,
    kStaticField,
    kInstanceField,
    kClass,
    kTypeArgumentsField,
    kUnused8,
    kType,
    kUnused9,
    kUnused10,
    kUnused11,
    kUnused12,
    kClosureFunction,
    kEndClosureFunctionScope,
    kNativeEntry,
    kSubtypeTestCache,
    kUnused13,
    kEmptyTypeArguments,
    kUnused14,
    kUnused15,
    kObjectRef,
    kDirectCall,
    kInterfaceCall,
    kInstantiatedInterfaceCall,
    kDynamicCall,
    kDirectCallViaDynamicForwarder,
  };

  Object& obj = Object::Handle(Z);
  Object& elem = Object::Handle(Z);
  Field& field = Field::Handle(Z);
  Class& cls = Class::Handle(Z);
  String& name = String::Handle(Z);
  const intptr_t obj_count = pool.Length();
  for (intptr_t i = start_index; i < obj_count; ++i) {
    const intptr_t tag = reader_.ReadTag();
    switch (tag) {
      case ConstantPoolTag::kInvalid:
        UNREACHABLE();
      case ConstantPoolTag::kStaticField:
        obj = ReadObject();
        ASSERT(obj.IsField());
        break;
      case ConstantPoolTag::kInstanceField:
        field ^= ReadObject();
        // InstanceField constant occupies 2 entries.
        // The first entry is used for field offset.
        obj = Smi::New(field.HostOffset() / kWordSize);
        pool.SetTypeAt(i, ObjectPool::EntryType::kTaggedObject,
                       ObjectPool::Patchability::kNotPatchable);
        pool.SetObjectAt(i, obj);
        ++i;
        ASSERT(i < obj_count);
        // The second entry is used for field object.
        obj = field.ptr();
        break;
      case ConstantPoolTag::kClass:
        obj = ReadObject();
        ASSERT(obj.IsClass());
        break;
      case ConstantPoolTag::kTypeArgumentsField:
        cls ^= ReadObject();
        obj = Smi::New(cls.host_type_arguments_field_offset() / kWordSize);
        break;
      case ConstantPoolTag::kType:
        obj = ReadObject();
        ASSERT(obj.IsAbstractType());
        break;
      case ConstantPoolTag::kClosureFunction: {
        intptr_t closure_index = reader_.ReadUInt();
        obj = closures_->At(closure_index);
        ASSERT(obj.IsFunction());
        // Set current entry.
        pool.SetTypeAt(i, ObjectPool::EntryType::kTaggedObject,
                       ObjectPool::Patchability::kNotPatchable);
        pool.SetObjectAt(i, obj);

        // This scope is needed to set active_class_->enclosing_ which is used
        // to assign parent function for function types.
        FunctionType& sig = FunctionType::Handle(zone_,
                                               Function::Cast(obj).signature());
        ActiveEnclosingFunctionScope active_enclosing_function(active_class_,
                                                               &sig);

        // Read constant pool until corresponding EndClosureFunctionScope.
        i = ReadConstantPool(function, pool, i + 1);

        // Proceed with the rest of entries.
        continue;
      }
      case ConstantPoolTag::kEndClosureFunctionScope: {
        // EndClosureFunctionScope entry is not used and set to null.
        obj = Object::null();
        pool.SetTypeAt(i, ObjectPool::EntryType::kTaggedObject,
                       ObjectPool::Patchability::kNotPatchable);
        pool.SetObjectAt(i, obj);
        return i;
      }
      case ConstantPoolTag::kNativeEntry: {
        name = ReadString();
        obj = NativeEntry(function, name);
        pool.SetTypeAt(i, ObjectPool::EntryType::kNativeEntryData,
                       ObjectPool::Patchability::kNotPatchable);
        pool.SetObjectAt(i, obj);
        continue;
      }
      case ConstantPoolTag::kSubtypeTestCache: {
        obj = SubtypeTestCache::New();
      } break;
      case ConstantPoolTag::kEmptyTypeArguments:
        obj = Object::empty_type_arguments().ptr();
        break;
      case ConstantPoolTag::kObjectRef:
        obj = ReadObject();
        break;
      case ConstantPoolTag::kDirectCall: {
        // DirectCall constant occupies 2 entries.
        // The first entry is used for target function.
        obj = ReadObject();
        ASSERT(obj.IsFunction());
        pool.SetTypeAt(i, ObjectPool::EntryType::kTaggedObject,
                       ObjectPool::Patchability::kNotPatchable);
        pool.SetObjectAt(i, obj);
        ++i;
        ASSERT(i < obj_count);
        // The second entry is used for arguments descriptor.
        obj = ReadObject();
      } break;
      case ConstantPoolTag::kInterfaceCall: {
        elem = ReadObject();
        ASSERT(elem.IsFunction());
        // InterfaceCall constant occupies 2 entries.
        // The first entry is used for interface target.
        pool.SetTypeAt(i, ObjectPool::EntryType::kTaggedObject,
                       ObjectPool::Patchability::kNotPatchable);
        pool.SetObjectAt(i, elem);
        ++i;
        ASSERT(i < obj_count);
        // The second entry is used for arguments descriptor.
        obj = ReadObject();
      } break;
      case ConstantPoolTag::kInstantiatedInterfaceCall: {
        elem = ReadObject();
        ASSERT(elem.IsFunction());
        // InstantiatedInterfaceCall constant occupies 3 entries:
        // 1) Interface target.
        pool.SetTypeAt(i, ObjectPool::EntryType::kTaggedObject,
                       ObjectPool::Patchability::kNotPatchable);
        pool.SetObjectAt(i, elem);
        ++i;
        ASSERT(i < obj_count);
        // 2) Arguments descriptor.
        obj = ReadObject();
        pool.SetTypeAt(i, ObjectPool::EntryType::kTaggedObject,
                       ObjectPool::Patchability::kNotPatchable);
        pool.SetObjectAt(i, obj);
        ++i;
        ASSERT(i < obj_count);
        // 3) Static receiver type.
        obj = ReadObject();
      } break;
      case ConstantPoolTag::kDynamicCall: {
        name ^= ReadObject();
        ASSERT(name.IsSymbol());
        // Do not mangle ==:
        //   * operator == takes an Object so it is either not checked or
        //     checked at the entry because the parameter is marked covariant,
        //     neither of those cases require a dynamic invocation forwarder
        if (!Field::IsGetterName(name) &&
            (name.ptr() != Symbols::EqualOperator().ptr())) {
          name = Function::CreateDynamicInvocationForwarderName(name);
        }
        // DynamicCall constant occupies 2 entries: selector and arguments
        // descriptor.
        pool.SetTypeAt(i, ObjectPool::EntryType::kTaggedObject,
                       ObjectPool::Patchability::kNotPatchable);
        pool.SetObjectAt(i, name);
        ++i;
        ASSERT(i < obj_count);
        // The second entry is used for arguments descriptor.
        obj = ReadObject();
      } break;
      case ConstantPoolTag::kDirectCallViaDynamicForwarder: {
        // DirectCallViaDynamicForwarder constant occupies 2 entries.
        // The first entry is used for target function.
        obj = ReadObject();
        ASSERT(obj.IsFunction());
        name = Function::Cast(obj).name();
        name = Function::CreateDynamicInvocationForwarderName(name);
        obj = Function::Cast(obj).GetDynamicInvocationForwarder(name);

        pool.SetTypeAt(i, ObjectPool::EntryType::kTaggedObject,
                       ObjectPool::Patchability::kNotPatchable);
        pool.SetObjectAt(i, obj);
        ++i;
        ASSERT(i < obj_count);
        // The second entry is used for arguments descriptor.
        obj = ReadObject();
      } break;
      default:
        UNREACHABLE();
    }
    pool.SetTypeAt(i, ObjectPool::EntryType::kTaggedObject,
                   ObjectPool::Patchability::kNotPatchable);
    pool.SetObjectAt(i, obj);
  }

  return obj_count - 1;
}

BytecodePtr BytecodeReaderHelper::ReadBytecode(const ObjectPool& pool) {
#if defined(SUPPORT_TIMELINE)
  TIMELINE_DURATION(Thread::Current(), CompilerVerbose,
                    "BytecodeReaderHelper::ReadBytecode");
#endif  // defined(SUPPORT_TIMELINE)
  const intptr_t size = reader_.ReadUInt();
  const intptr_t offset = reader_.offset();

  const uint8_t* data = reader_.BufferAt(offset);
  reader_.set_offset(offset + size);

  // Create and return bytecode object.
  return Bytecode::New(reinterpret_cast<uword>(data), size, offset, pool);
}

void BytecodeReaderHelper::ReadExceptionsTable(const Bytecode& bytecode,
                                               bool has_exceptions_table) {
#if defined(SUPPORT_TIMELINE)
  TIMELINE_DURATION(Thread::Current(), CompilerVerbose,
                    "BytecodeReaderHelper::ReadExceptionsTable");
#endif

  const intptr_t try_block_count =
      has_exceptions_table ? reader_.ReadListLength() : 0;
  if (try_block_count > 0) {
    const ObjectPool& pool = ObjectPool::Handle(Z, bytecode.object_pool());
    AbstractType& handler_type = AbstractType::Handle(Z);
    Array& handler_types = Array::Handle(Z);
    DescriptorList* pc_descriptors_list = new (Z) DescriptorList(Z);
    ExceptionHandlerList* exception_handlers_list =
        new (Z) ExceptionHandlerList();

    // Encoding of ExceptionsTable is described in
    // pkg/vm/lib/bytecode/exceptions.dart.
    for (intptr_t try_index = 0; try_index < try_block_count; try_index++) {
      intptr_t outer_try_index_plus1 = reader_.ReadUInt();
      intptr_t outer_try_index = outer_try_index_plus1 - 1;
      // PcDescriptors are expressed in terms of return addresses.
      intptr_t start_pc =
          KernelBytecode::BytecodePcToOffset(reader_.ReadUInt(),
                                             /* is_return_address = */ true);
      intptr_t end_pc =
          KernelBytecode::BytecodePcToOffset(reader_.ReadUInt(),
                                             /* is_return_address = */ true);
      intptr_t handler_pc =
          KernelBytecode::BytecodePcToOffset(reader_.ReadUInt(),
                                             /* is_return_address = */ false);
      uint8_t flags = reader_.ReadByte();
      const uint8_t kFlagNeedsStackTrace = 1 << 0;
      const uint8_t kFlagIsSynthetic = 1 << 1;
      const bool needs_stacktrace = (flags & kFlagNeedsStackTrace) != 0;
      const bool is_generated = (flags & kFlagIsSynthetic) != 0;
      intptr_t type_count = reader_.ReadListLength();
      ASSERT(type_count > 0);
      handler_types = Array::New(type_count, Heap::kOld);
      for (intptr_t i = 0; i < type_count; i++) {
        intptr_t type_index = reader_.ReadUInt();
        ASSERT(type_index < pool.Length());
        handler_type ^= pool.ObjectAt(type_index);
        handler_types.SetAt(i, handler_type);
      }
      pc_descriptors_list->AddDescriptor(
          UntaggedPcDescriptors::kOther, start_pc, DeoptId::kNone,
          TokenPosition::kNoSource, try_index,
          UntaggedPcDescriptors::kInvalidYieldIndex);
      pc_descriptors_list->AddDescriptor(
          UntaggedPcDescriptors::kOther, end_pc, DeoptId::kNone,
          TokenPosition::kNoSource, try_index,
          UntaggedPcDescriptors::kInvalidYieldIndex);

      // The exception handler keeps a zone handle of the types array, rather
      // than a raw pointer. Do not share the handle across iterations to avoid
      // clobbering the array.
      exception_handlers_list->AddHandler(
          try_index, outer_try_index, handler_pc, is_generated,
          Array::ZoneHandle(Z, handler_types.ptr()), needs_stacktrace);
    }
    const PcDescriptors& descriptors = PcDescriptors::Handle(
        Z, pc_descriptors_list->FinalizePcDescriptors(bytecode.PayloadStart()));
    bytecode.set_pc_descriptors(descriptors);
    const ExceptionHandlers& handlers = ExceptionHandlers::Handle(
        Z, exception_handlers_list->FinalizeExceptionHandlers(
               bytecode.PayloadStart()));
    bytecode.set_exception_handlers(handlers);
  } else {
    bytecode.set_pc_descriptors(Object::empty_descriptors());
    bytecode.set_exception_handlers(Object::empty_exception_handlers());
  }
}

void BytecodeReaderHelper::ReadSourcePositions(const Bytecode& bytecode,
                                               bool has_source_positions) {
  if (!has_source_positions) {
    return;
  }

  intptr_t offset = reader_.ReadUInt();
  bytecode.set_source_positions_binary_offset(
      bytecode_component_->GetSourcePositionsOffset() + offset);
}

void BytecodeReaderHelper::ReadLocalVariables(const Bytecode& bytecode,
                                              bool has_local_variables) {
  if (!has_local_variables) {
    return;
  }

  const intptr_t offset = reader_.ReadUInt();
  bytecode.set_local_variables_binary_offset(
      bytecode_component_->GetLocalVariablesOffset() + offset);
}

TypedDataPtr BytecodeReaderHelper::NativeEntry(const Function& function,
                                               const String& external_name) {
  MethodRecognizer::Kind kind = function.recognized_kind();
  // This list of recognized methods must be kept in sync with the list of
  // methods handled specially by the NativeCall bytecode in the interpreter.
  switch (kind) {
    case MethodRecognizer::kObjectEquals:
    case MethodRecognizer::kStringBaseLength:
    case MethodRecognizer::kStringBaseIsEmpty:
    case MethodRecognizer::kGrowableArrayLength:
    case MethodRecognizer::kObjectArrayLength:
    case MethodRecognizer::kImmutableArrayLength:
    case MethodRecognizer::kTypedListBaseLength:
    case MethodRecognizer::kByteDataViewLength:
    case MethodRecognizer::kByteDataViewOffsetInBytes:
    case MethodRecognizer::kTypedDataViewOffsetInBytes:
    case MethodRecognizer::kByteDataViewTypedData:
    case MethodRecognizer::kTypedDataViewTypedData:
    case MethodRecognizer::kClassIDgetID:
    case MethodRecognizer::kGrowableArrayCapacity:
    case MethodRecognizer::kListFactory:
    case MethodRecognizer::kObjectArrayAllocate:
    case MethodRecognizer::kLinkedHashBase_getIndex:
    case MethodRecognizer::kLinkedHashBase_setIndex:
    case MethodRecognizer::kLinkedHashBase_getData:
    case MethodRecognizer::kLinkedHashBase_setData:
    case MethodRecognizer::kLinkedHashBase_getHashMask:
    case MethodRecognizer::kLinkedHashBase_setHashMask:
    case MethodRecognizer::kLinkedHashBase_getUsedData:
    case MethodRecognizer::kLinkedHashBase_setUsedData:
    case MethodRecognizer::kLinkedHashBase_getDeletedKeys:
    case MethodRecognizer::kLinkedHashBase_setDeletedKeys:
    case MethodRecognizer::kFfiAbi:
#define TYPED_DATA_FACTORY(clazz)                                              \
  case MethodRecognizer::kTypedData_##clazz##_factory:
      CLASS_LIST_TYPED_DATA(TYPED_DATA_FACTORY)
#undef TYPED_DATA_FACTORY
      break;
    default:
      kind = MethodRecognizer::kUnknown;
  }
  NativeFunctionWrapper trampoline = NULL;
  NativeFunction native_function = NULL;
  intptr_t argc_tag = 0;
  if (kind == MethodRecognizer::kUnknown) {
    if (!FLAG_link_natives_lazily) {
      const Class& cls = Class::Handle(Z, function.Owner());
      const Library& library = Library::Handle(Z, cls.library());
      Dart_NativeEntryResolver resolver = library.native_entry_resolver();
      const bool is_bootstrap_native = Bootstrap::IsBootstrapResolver(resolver);
      const int num_params =
          NativeArguments::ParameterCountForResolution(function);
      bool is_auto_scope = true;
      native_function = NativeEntry::ResolveNative(library, external_name,
                                                   num_params, &is_auto_scope);
      if (native_function == nullptr) {
        Report::MessageF(Report::kError, Script::Handle(function.script()),
                         function.token_pos(), Report::AtLocation,
                         "native function '%s' (%" Pd
                         " arguments) cannot be found",
                         external_name.ToCString(), function.NumParameters());
      }
      if (is_bootstrap_native) {
        trampoline = &NativeEntry::BootstrapNativeCallWrapper;
      } else if (is_auto_scope) {
        trampoline = &NativeEntry::AutoScopeNativeCallWrapper;
      } else {
        trampoline = &NativeEntry::NoScopeNativeCallWrapper;
      }
    }
    argc_tag = NativeArguments::ComputeArgcTag(function);
  }
  return NativeEntryData::New(kind, trampoline, native_function, argc_tag);
}

ArrayPtr BytecodeReaderHelper::ReadBytecodeComponent(intptr_t md_offset) {
  ASSERT(Thread::Current()->IsMutatorThread());

  AlternativeReadingScope alt(&reader_, md_offset);

  const intptr_t start_offset = reader_.offset();

  intptr_t magic = reader_.ReadUInt32();
  if (magic != KernelBytecode::kMagicValue) {
    FATAL1("Unexpected Dart bytecode magic %" Px, magic);
  }

  const intptr_t version = reader_.ReadUInt32();
  if ((version < KernelBytecode::kMinSupportedBytecodeFormatVersion) ||
      (version > KernelBytecode::kMaxSupportedBytecodeFormatVersion)) {
    FATAL3("Unsupported Dart bytecode format version %" Pd
           ". "
           "This version of Dart VM supports bytecode format versions from %" Pd
           " to %" Pd ".",
           version, KernelBytecode::kMinSupportedBytecodeFormatVersion,
           KernelBytecode::kMaxSupportedBytecodeFormatVersion);
  }

  reader_.ReadUInt32();  // Skip stringTable.numItems
  const intptr_t string_table_offset = start_offset + reader_.ReadUInt32();

  reader_.ReadUInt32();  // Skip objectTable.numItems
  const intptr_t object_table_offset = start_offset + reader_.ReadUInt32();

  reader_.ReadUInt32();  // Skip main.numItems
  const intptr_t main_offset = start_offset + reader_.ReadUInt32();

  const intptr_t num_libraries = reader_.ReadUInt32();
  const intptr_t library_index_offset = start_offset + reader_.ReadUInt32();

  reader_.ReadUInt32();  // Skip libraries.numItems
  const intptr_t libraries_offset = start_offset + reader_.ReadUInt32();

  const intptr_t num_classes = reader_.ReadUInt32();
  const intptr_t classes_offset = start_offset + reader_.ReadUInt32();

  reader_.ReadUInt32();  // Skip members.numItems
  const intptr_t members_offset = start_offset + reader_.ReadUInt32();

  const intptr_t num_codes = reader_.ReadUInt32();
  const intptr_t codes_offset = start_offset + reader_.ReadUInt32();

  reader_.ReadUInt32();  // Skip sourcePositions.numItems
  const intptr_t source_positions_offset = start_offset + reader_.ReadUInt32();

  reader_.ReadUInt32();  // Skip sourceFiles.numItems
  const intptr_t source_files_offset = start_offset + reader_.ReadUInt32();

  reader_.ReadUInt32();  // Skip lineStarts.numItems
  const intptr_t line_starts_offset = start_offset + reader_.ReadUInt32();

  reader_.ReadUInt32();  // Skip localVariables.numItems
  const intptr_t local_variables_offset = start_offset + reader_.ReadUInt32();

  reader_.ReadUInt32();  // Skip annotations.numItems
  const intptr_t annotations_offset = start_offset + reader_.ReadUInt32();

  const intptr_t num_protected_names = reader_.ReadUInt32();
  const intptr_t protected_names_offset = start_offset + reader_.ReadUInt32();

  // Read header of string table.
  reader_.set_offset(string_table_offset);
  const intptr_t num_one_byte_strings = reader_.ReadUInt32();
  const intptr_t num_two_byte_strings = reader_.ReadUInt32();
  const intptr_t strings_contents_offset =
      reader_.offset() + (num_one_byte_strings + num_two_byte_strings) * 4;

  // Read header of object table.
  reader_.set_offset(object_table_offset);
  const intptr_t num_objects = reader_.ReadUInt();
  const intptr_t objects_size = reader_.ReadUInt();

  // Skip over contents of objects.
  const intptr_t objects_contents_offset = reader_.offset();
  const intptr_t object_offsets_offset = objects_contents_offset + objects_size;
  reader_.set_offset(object_offsets_offset);

  auto& bytecode_component_array = Array::Handle(
      Z,
      BytecodeComponentData::New(
          Z, version, num_objects, string_table_offset, strings_contents_offset,
          object_offsets_offset, objects_contents_offset, main_offset,
          num_libraries, library_index_offset, libraries_offset, num_classes,
          classes_offset, members_offset, num_codes, codes_offset,
          source_positions_offset, source_files_offset, line_starts_offset,
          local_variables_offset, annotations_offset, Heap::kOld));

  BytecodeComponentData bytecode_component(&bytecode_component_array);

  // Read object offsets.
  Smi& offs = Smi::Handle(Z);
  for (intptr_t i = 0; i < num_objects; ++i) {
    offs = Smi::New(reader_.ReadUInt());
    bytecode_component.SetObject(i, offs);
  }

  // Read protected names.
  if (I->group()->obfuscate() && (num_protected_names > 0)) {
    bytecode_component_ = &bytecode_component;

    reader_.set_offset(protected_names_offset);
    Obfuscator obfuscator(thread_, Object::null_string());
    auto& name = String::Handle(Z);
    for (intptr_t i = 0; i < num_protected_names; ++i) {
      name = ReadString();
      obfuscator.PreventRenaming(name);
    }

    bytecode_component_ = nullptr;
  }

  H.SetBytecodeComponent(bytecode_component_array);

  return bytecode_component_array.ptr();
}

void BytecodeReaderHelper::ResetObjects() {
  reader_.set_offset(bytecode_component_->GetObjectOffsetsOffset());
  const intptr_t num_objects = bytecode_component_->GetNumObjects();

  // Read object offsets.
  Smi& offs = Smi::Handle(Z);
  for (intptr_t i = 0; i < num_objects; ++i) {
    offs = Smi::New(reader_.ReadUInt());
    bytecode_component_->SetObject(i, offs);
  }
}

ObjectPtr BytecodeReaderHelper::ReadObject() {
  uint32_t header = reader_.ReadUInt();
  if ((header & kReferenceBit) != 0) {
    intptr_t index = header >> kIndexShift;
    if (index == 0) {
      return Object::null();
    }
    ObjectPtr obj = bytecode_component_->GetObject(index);
    if (obj->IsHeapObject()) {
      return obj;
    }
    // Object is not loaded yet.
    intptr_t offset = bytecode_component_->GetObjectsContentsOffset() +
                      Smi::Value(Smi::RawCast(obj));
    AlternativeReadingScope alt(&reader_, offset);
    header = reader_.ReadUInt();

    obj = ReadObjectContents(header);
    ASSERT(obj->IsHeapObject());
    {
      REUSABLE_OBJECT_HANDLESCOPE(thread_);
      Object& obj_handle = thread_->ObjectHandle();
      obj_handle = obj;
      bytecode_component_->SetObject(index, obj_handle);
    }
    return obj;
  }

  return ReadObjectContents(header);
}

StringPtr BytecodeReaderHelper::ConstructorName(const Class& cls,
                                                const String& name) {
  GrowableHandlePtrArray<const String> pieces(Z, 3);
  pieces.Add(String::Handle(Z, cls.Name()));
  pieces.Add(Symbols::Dot());
  pieces.Add(name);
  return Symbols::FromConcatAll(thread_, pieces);
}

ObjectPtr BytecodeReaderHelper::ReadObjectContents(uint32_t header) {
  ASSERT(((header & kReferenceBit) == 0));

  // Must be in sync with enum ObjectKind in
  // pkg/vm/lib/bytecode/object_table.dart.
  enum ObjectKind {
    kInvalid,
    kLibrary,
    kClass,
    kMember,
    kClosure,
    kUnused1,
    kUnused2,
    kUnused3,
    kUnused4,
    kName,
    kTypeArguments,
    kUnused5,
    kConstObject,
    kArgDesc,
    kScript,
    kType,
  };

  // Member flags, must be in sync with _MemberHandle constants in
  // pkg/vm/lib/bytecode/object_table.dart.
  const intptr_t kFlagIsField = kFlagBit0;
  const intptr_t kFlagIsConstructor = kFlagBit1;

  // ArgDesc flags, must be in sync with _ArgDescHandle constants in
  // pkg/vm/lib/bytecode/object_table.dart.
  const int kFlagHasNamedArgs = kFlagBit0;
  const int kFlagHasTypeArgs = kFlagBit1;

  // Script flags, must be in sync with _ScriptHandle constants in
  // pkg/vm/lib/bytecode/object_table.dart.
  const int kFlagHasSourceFile = kFlagBit0;

  // Name flags, must be in sync with _NameHandle constants in
  // pkg/vm/lib/bytecode/object_table.dart.
  const intptr_t kFlagIsPublic = kFlagBit0;

  const intptr_t kind = (header >> kKindShift) & kKindMask;
  const intptr_t flags = header & kFlagsMask;

  switch (kind) {
    case kInvalid:
      UNREACHABLE();
      break;
    case kLibrary: {
      String& uri = String::CheckedHandle(Z, ReadObject());
      LibraryPtr library = Library::LookupLibrary(thread_, uri);
      if (library == Library::null()) {
        // We do not register expression evaluation libraries with the VM:
        // The expression evaluation functions should be GC-able as soon as
        // they are not reachable anymore and we never look them up by name.
        if (uri.ptr() == Symbols::EvalSourceUri().ptr()) {
          ASSERT(expression_evaluation_library_ != nullptr);
          return expression_evaluation_library_->ptr();
        }
#if !defined(PRODUCT)
        ASSERT(IsolateGroup::Current()->HasAttemptedReload());
        const String& msg = String::Handle(
            Z,
            String::NewFormatted("Unable to find library %s", uri.ToCString()));
        Report::LongJump(LanguageError::Handle(Z, LanguageError::New(msg)));
#else
        FATAL1("Unable to find library %s", uri.ToCString());
#endif
      }
      return library;
    }
    case kClass: {
      const Library& library = Library::CheckedHandle(Z, ReadObject());
      const String& class_name = String::CheckedHandle(Z, ReadObject());
      if (class_name.ptr() == Symbols::Empty().ptr()) {
        NoSafepointScope no_safepoint_scope(thread_);
        ClassPtr cls = library.toplevel_class();
        if (cls == Class::null()) {
          FATAL1("Unable to find toplevel class %s", library.ToCString());
        }
        return cls;
      }
      ClassPtr cls = library.LookupLocalClass(class_name);
      if (cls == Class::null()) {
        if (IsExpressionEvaluationLibrary(library)) {
          return H.GetExpressionEvaluationRealClass();
        }
#if !defined(PRODUCT)
        ASSERT(IsolateGroup::Current()->HasAttemptedReload());
        const String& msg = String::Handle(
            Z,
            String::NewFormatted("Unable to find class %s in %s",
                                 class_name.ToCString(), library.ToCString()));
        Report::LongJump(LanguageError::Handle(Z, LanguageError::New(msg)));
#else
        FATAL2("Unable to find class %s in %s", class_name.ToCString(),
               library.ToCString());
#endif
      }
      return cls;
    }
    case kMember: {
      const Class& cls = Class::CheckedHandle(Z, ReadObject());
      String& name = String::CheckedHandle(Z, ReadObject());
      if ((flags & kFlagIsField) != 0) {
        FieldPtr field = cls.LookupField(name);
        if (field == Field::null()) {
#if !defined(PRODUCT)
          ASSERT(IsolateGroup::Current()->HasAttemptedReload());
          const String& msg = String::Handle(
              Z, String::NewFormatted("Unable to find field %s in %s",
                                      name.ToCString(), cls.ToCString()));
          Report::LongJump(LanguageError::Handle(Z, LanguageError::New(msg)));
#else
          FATAL2("Unable to find field %s in %s", name.ToCString(),
                 cls.ToCString());
#endif
        }
        return field;
      } else {
        if ((flags & kFlagIsConstructor) != 0) {
          name = ConstructorName(cls, name);
        }
        ASSERT(!name.IsNull() && name.IsSymbol());
#if defined(DART_DYNAMIC_RUNTIME)
        if (Isolate::Current()->getIsAlignClass()) {
          if (name.ptr() == scoped_function_name_.ptr()) {
            return scoped_function_.ptr();
          }
        } else {
          if (name.ptr() == scoped_function_name_.ptr() &&
            cls.ptr() == scoped_function_class_.ptr()) {
            return scoped_function_.ptr();
          }
        }
#else
        if (name.ptr() == scoped_function_name_.ptr() &&
          cls.ptr() == scoped_function_class_.ptr()) {
          return scoped_function_.ptr();
        }
#endif
        FunctionPtr function = Function::null();
        if (cls.EnsureIsFinalized(thread_) == Error::null()) {
          function = Resolver::ResolveFunction(Z, cls, name);
        }
        if (function == Function::null()) {
          // When requesting a getter, also return method extractors.
          if (Field::IsGetterName(name)) {
            String& method_name =
                String::Handle(Z, Field::NameFromGetter(name));
            function = Resolver::ResolveFunction(Z, cls, method_name);
            if (function != Function::null()) {
              function = Function::Handle(Z, function).GetMethodExtractor(name);
              if (function != Function::null()) {
                return function;
              }
            }
          }
#if defined(DART_DYNAMIC_RUNTIME)
          FunctionType& signature2 =
              FunctionType::Handle(Z, FunctionType::New());
          function = Function::New(signature2, name,
                                   UntaggedFunction::kRegularFunction, false,
                                   false, false, false, false, cls,
                                   TokenPosition::kMinSource);
#else
#if !defined(PRODUCT)
          ASSERT(IsolateGroup::Current()->HasAttemptedReload());
          const String& msg = String::Handle(
              Z, String::NewFormatted("Unable to find function %s in %s",
                                      name.ToCString(), cls.ToCString()));
          Report::LongJump(LanguageError::Handle(Z, LanguageError::New(msg)));
#else
          FATAL2("Unable to find function %s in %s", name.ToCString(),
                 cls.ToCString());
#endif
#endif
        }
        return function;
      }
    }
    case kClosure: {
      ReadObject();  // Skip enclosing member.
      const intptr_t closure_index = reader_.ReadUInt();
      return closures_->At(closure_index);
    }
    case kName: {
      if ((flags & kFlagIsPublic) == 0) {
        const Library& library = Library::CheckedHandle(Z, ReadObject());
        ASSERT(!library.IsNull());
        auto& name = String::Handle(Z, ReadString(/* is_canonical = */ false));
        name = library.PrivateName(name);
        if (I->group()->obfuscate()) {
          const auto& library_key = String::Handle(Z, library.private_key());
          Obfuscator obfuscator(thread_, library_key);
          return obfuscator.Rename(name);
        }
        return name.ptr();
      }
      if (I->group()->obfuscate()) {
        Obfuscator obfuscator(thread_, Object::null_string());
        const auto& name = String::Handle(Z, ReadString());
        return obfuscator.Rename(name);
      } else {
        return ReadString();
      }
    }
    case kTypeArguments: {
      return ReadTypeArguments();
    }
    case kConstObject: {
      const intptr_t tag = flags / kFlagBit0;
      return ReadConstObject(tag);
    }
    case kArgDesc: {
      const intptr_t num_arguments = reader_.ReadUInt();
      const intptr_t num_type_args =
          ((flags & kFlagHasTypeArgs) != 0) ? reader_.ReadUInt() : 0;
      if ((flags & kFlagHasNamedArgs) == 0) {
        return ArgumentsDescriptor::NewBoxed(num_type_args, num_arguments);
      } else {
        const intptr_t num_arg_names = reader_.ReadListLength();
        const Array& array = Array::Handle(Z, Array::New(num_arg_names));
        String& name = String::Handle(Z);
        for (intptr_t i = 0; i < num_arg_names; ++i) {
          name ^= ReadObject();
          array.SetAt(i, name);
        }
        return ArgumentsDescriptor::NewBoxed(num_type_args, num_arguments,
                                             array);
      }
    }
    case kScript: {
      const String& uri = String::CheckedHandle(Z, ReadObject());
      Script& script = Script::Handle(Z);
      if ((flags & kFlagHasSourceFile) != 0) {
        // TODO(alexmarkov): read source and line starts only when needed.
        script =
            ReadSourceFile(uri, bytecode_component_->GetSourceFilesOffset() +
                                    reader_.ReadUInt());
      } else {
        script = Script::New(uri, Object::null_string());
      }
      script.set_kernel_program_info(H.GetKernelProgramInfo());
      return script.ptr();
    }
    case kType: {
      const intptr_t tag = (flags & kTagMask) / kFlagBit0;
      const Nullability nullability =
          Reader::ConvertNullability(static_cast<KernelNullability>(
              (flags & kNullabilityMask) / kFlagBit4));
      return ReadType(tag, nullability);
    }
    default:
      UNREACHABLE();
  }

  return Object::null();
}

ObjectPtr BytecodeReaderHelper::ReadConstObject(intptr_t tag) {
  // Must be in sync with enum ConstTag in
  // pkg/vm/lib/bytecode/object_table.dart.
  enum ConstTag {
    kInvalid,
    kInstance,
    kInt,
    kDouble,
    kList,
    kTearOff,
    kBool,
    kSymbol,
    kTearOffInstantiation,
    kString,
    kMap,
    kSet,
  };

  switch (tag) {
    case kInvalid:
      UNREACHABLE();
      break;
    case kInstance: {
      const Type& type = Type::CheckedHandle(Z, ReadObject());
      const Class& cls = Class::Handle(Z, type.type_class());
      const Instance& obj = Instance::Handle(Z, Instance::New(cls, Heap::kOld));
      if (type.arguments() != TypeArguments::null()) {
        const TypeArguments& type_args =
            TypeArguments::Handle(Z, type.arguments());
        obj.SetTypeArguments(type_args);
      }
      const intptr_t num_fields = reader_.ReadUInt();
      Field& field = Field::Handle(Z);
      Object& value = Object::Handle(Z);
      for (intptr_t i = 0; i < num_fields; ++i) {
        field ^= ReadObject();
        value = ReadObject();
        obj.SetField(field, value);
      }
      return H.Canonicalize(obj);
    }
    case kInt: {
      const int64_t value = reader_.ReadSLEB128AsInt64();
      if (Smi::IsValid(value)) {
        return Smi::New(static_cast<intptr_t>(value));
      }
      const Integer& obj = Integer::Handle(Z, Integer::New(value, Heap::kOld));
      return H.Canonicalize(obj);
    }
    case kDouble: {
      const int64_t bits = reader_.ReadSLEB128AsInt64();
      double value = bit_cast<double, int64_t>(bits);
      const Double& obj = Double::Handle(Z, Double::New(value, Heap::kOld));
      return H.Canonicalize(obj);
    }
    case kList: {
      const AbstractType& elem_type =
          AbstractType::CheckedHandle(Z, ReadObject());
      const intptr_t length = reader_.ReadUInt();
      const Array& array = Array::Handle(Z, Array::New(length, elem_type));
      Object& value = Object::Handle(Z);
      for (intptr_t i = 0; i < length; ++i) {
        value = ReadObject();
        array.SetAt(i, value);
      }
      array.MakeImmutable();
      return H.Canonicalize(array);
    }
    case kTearOff: {
      Object& obj = Object::Handle(Z, ReadObject());
      ASSERT(obj.IsFunction());
      obj = Function::Cast(obj).ImplicitClosureFunction();
      ASSERT(obj.IsFunction());
      obj = Function::Cast(obj).ImplicitStaticClosure();
      ASSERT(obj.IsInstance());
      return H.Canonicalize(Instance::Cast(obj));
    }
    case kBool: {
      bool is_true = reader_.ReadByte() != 0;
      return is_true ? Bool::True().ptr() : Bool::False().ptr();
    }
    case kSymbol: {
      const String& name = String::CheckedHandle(Z, ReadObject());
      ASSERT(name.IsSymbol());
      const Library& library = Library::Handle(Z, Library::InternalLibrary());
      ASSERT(!library.IsNull());
      const Class& cls =
          Class::Handle(Z, library.LookupClass(Symbols::Symbol()));
      ASSERT(!cls.IsNull());
      const Field& field = Field::Handle(
          Z, cls.LookupInstanceFieldAllowPrivate(Symbols::_name()));
      ASSERT(!field.IsNull());
      const Instance& obj = Instance::Handle(Z, Instance::New(cls, Heap::kOld));
      obj.SetField(field, name);
      return H.Canonicalize(obj);
    }
    case kTearOffInstantiation: {
      Closure& closure = Closure::CheckedHandle(Z, ReadObject());
      const TypeArguments& type_args =
          TypeArguments::CheckedHandle(Z, ReadObject());
      closure = Closure::New(
          TypeArguments::Handle(Z, closure.instantiator_type_arguments()),
          TypeArguments::Handle(Z, closure.function_type_arguments()),
          type_args, Function::Handle(Z, closure.function()),
          Context::Handle(Z, closure.context()), Heap::kOld);
      return H.Canonicalize(closure);
    }
    case kString:
      return ReadString();
    case kMap: {
        const Type& type = Type::CheckedHandle(Z, ReadObject());
        const auto& map = LinkedHashMap::Handle(
                Z, ImmutableLinkedHashMap::NewUninitialized(Heap::kOld));
        if (type.arguments() != TypeArguments::null()) {
            const TypeArguments& type_args =
                    TypeArguments::Handle(Z, type.arguments());
            map.SetTypeArguments(type_args);
        }
        const intptr_t length = reader_.ReadUInt();
        const intptr_t used_data = (length << 1);
        map.set_used_data(used_data);

        const intptr_t data_size = Utils::RoundUpToPowerOfTwo(used_data);
        const auto& data = Array::Handle(Z, Array::New(data_size));
        map.set_data(data);

        map.set_deleted_keys(0);
        map.ComputeAndSetHashMask();

        for (intptr_t i = 0; i < used_data; ++i) {
            Object& obj = Object::Handle(Z);
            obj = ReadObject();
            data.SetAt(i, obj);
        }
        return H.Canonicalize(map);
    }
    case kSet: {
        const Type& type = Type::CheckedHandle(Z, ReadObject());
        const auto& set = LinkedHashSet::Handle(
                Z, ImmutableLinkedHashSet::NewUninitialized(Heap::kOld));
        if (type.arguments() != TypeArguments::null()) {
            const TypeArguments& type_args =
                    TypeArguments::Handle(Z, type.arguments());
            set.SetTypeArguments(type_args);
        }
        const intptr_t length = reader_.ReadUInt();
        const intptr_t used_data = length;
        set.set_used_data(used_data);

        const intptr_t data_size = Utils::RoundUpToPowerOfTwo(used_data);
        const auto& data = Array::Handle(Z, Array::New(data_size));
        set.set_data(data);

        set.set_deleted_keys(0);
        set.ComputeAndSetHashMask();

        for (intptr_t i = 0; i < used_data; ++i) {
            Object& obj = Object::Handle(Z);
            obj = ReadObject();
            data.SetAt(i, obj);
        }
        return H.Canonicalize(set);
    }
    default:
      UNREACHABLE();
  }
  return Object::null();
}

ObjectPtr BytecodeReaderHelper::ReadType(intptr_t tag,
                                         Nullability nullability) {
  // Must be in sync with enum TypeTag in
  // pkg/vm/lib/bytecode/object_table.dart.
  enum TypeTag {
    kInvalid,
    kDynamic,
    kVoid,
    kSimpleType,
    kTypeParameter,
    kGenericType,
    kRecursiveGenericType,
    kRecursiveTypeRef,
    kFunctionType,
    kNever,
    kNull,
  };

  // FunctionType flags, must be in sync with _FunctionTypeHandle constants in
  // pkg/vm/lib/bytecode/object_table.dart.
  const int kFlagHasOptionalPositionalParams = 1 << 0;
  const int kFlagHasOptionalNamedParams = 1 << 1;
  const int kFlagHasTypeParams = 1 << 2;

  switch (tag) {
    case kInvalid:
      UNREACHABLE();
      break;
    case kDynamic:
      return AbstractType::dynamic_type().ptr();
    case kVoid:
      return AbstractType::void_type().ptr();
    case kNever:
      return Type::Handle(Z, Type::NeverType())
          .ToNullability(nullability, Heap::kOld);
    case kSimpleType: {
      const Class& cls = Class::CheckedHandle(Z, ReadObject());
      if (!cls.is_declaration_loaded()) {
        LoadReferencedClass(cls);
      }
      const Type& type = Type::Handle(Z, cls.DeclarationType());
      return type.ToNullability(nullability, Heap::kOld);
    }
    case kTypeParameter: {
      Object& parent = Object::Handle(Z, ReadObject());
      const intptr_t index_in_parent = reader_.ReadUInt();
      TypeParameters& type_parameters = TypeParameters::Handle(Z);
      if (parent.IsClass()) {
        type_parameters = Class::Cast(parent).type_parameters();
      } else if (parent.IsFunction()) {
        if (Function::Cast(parent).IsFactory()) {
          // For factory constructors VM uses type parameters of a class
          // instead of constructor's type parameters.
          parent = Function::Cast(parent).Owner();
          type_parameters = Class::Cast(parent).type_parameters();
        } else {
          type_parameters = Function::Cast(parent).type_parameters();
        }
      } else if (parent.IsNull()) {
        ASSERT(function_type_type_parameters_ != nullptr);
        type_parameters = function_type_type_parameters_->ptr();
      } else {
        UNREACHABLE();
      }
      TypeParameter& type_parameter = TypeParameter::Handle(Z);
      type_parameter ^= type_parameters.DefaultAt(index_in_parent);
      type_parameter.set_bound(
          AbstractType::Handle(type_parameters.BoundAt(index_in_parent)));
      if (type_parameter.bound() == AbstractType::null()) {
        AbstractType& derived = AbstractType::Handle(
            Z, type_parameter.ToNullability(nullability, Heap::kOld));
        active_class_->RecordDerivedTypeParameter(Z,
                                                  TypeParameter::Cast(derived));
        return derived.ptr();
      }
      return type_parameter.ToNullability(nullability, Heap::kOld);
    }
    case kGenericType: {
      const Class& cls = Class::CheckedHandle(Z, ReadObject());
      if (!cls.is_declaration_loaded()) {
        LoadReferencedClass(cls);
      }
      const TypeArguments& type_arguments =
          TypeArguments::CheckedHandle(Z, ReadObject());
      const Type& type =
          Type::Handle(Z, Type::New(cls, type_arguments, nullability));
      type.SetIsFinalized();
      return type.Canonicalize(thread_, nullptr);
    }
    case kRecursiveGenericType: {
      const intptr_t id = reader_.ReadUInt();
      const Class& cls = Class::CheckedHandle(Z, ReadObject());
      if (!cls.is_declaration_loaded()) {
        LoadReferencedClass(cls);
      }
      const auto saved_pending_recursive_types = pending_recursive_types_;
      if (id == 0) {
        pending_recursive_types_ = &GrowableObjectArray::Handle(
            Z, GrowableObjectArray::New(Heap::kOld));
      }
      ASSERT(id == pending_recursive_types_->Length());
      const auto& type_ref =
          TypeRef::Handle(Z, TypeRef::New(AbstractType::null_abstract_type()));
      pending_recursive_types_->Add(type_ref);

      reading_type_arguments_of_recursive_type_ = true;
      const TypeArguments& type_arguments =
          TypeArguments::CheckedHandle(Z, ReadObject());
      reading_type_arguments_of_recursive_type_ = false;

      ASSERT(id == pending_recursive_types_->Length() - 1);
      ASSERT(pending_recursive_types_->At(id) == type_ref.ptr());
      pending_recursive_types_->SetLength(id);
      pending_recursive_types_ = saved_pending_recursive_types;

      Type& type =
          Type::Handle(Z, Type::New(cls, type_arguments, nullability));
      type_ref.set_type(type);
      type.SetIsFinalized();
      if (id != 0) {
        // Do not canonicalize non-root recursive types
        // as not all TypeRef objects are filled up at this point.
        return type.ptr();
      }
      return type.Canonicalize(thread_, nullptr);
    }
    case kRecursiveTypeRef: {
      const intptr_t id = reader_.ReadUInt();
      ASSERT(pending_recursive_types_ != nullptr);
      ASSERT(pending_recursive_types_->Length() >= id);
      return pending_recursive_types_->At(id);
    }
    case kFunctionType: {
      const intptr_t flags = reader_.ReadUInt();

      const intptr_t num_enclosing_type_arguments =
              active_class_->enclosing !=
                  NULL ? active_class_->enclosing->NumTypeArguments() : 0;
      const FunctionType& signature = FunctionType::ZoneHandle(
          FunctionType::New(num_enclosing_type_arguments, nullability));
      Function& signature_function2 = Function::ZoneHandle(
          Z,
          Function::New(signature, Symbols::AnonymousSignature(),
                        UntaggedFunction::kRegularFunction,
                        false,
                        false,  // is_const
                        false,  // is_abstract
                        false,  // is_external
                        false,  // is_native
                        *active_class_->klass, TokenPosition::kNoSource));

      // This scope is needed to set active_class_->enclosing_ which is used to
      // assign parent function for function types.
      ActiveEnclosingFunctionScope active_enclosing_function(
          active_class_, &signature);

      return ReadFunctionSignature(
          signature_function2, (flags & kFlagHasOptionalPositionalParams) != 0,
          (flags & kFlagHasOptionalNamedParams) != 0,
          (flags & kFlagHasTypeParams) != 0,
          /* has_positional_param_names = */ false,
          /* has_parameter_flags */ false, nullability);
    }
    case kNull: {
      return Type::NullType();
    }
    default:
      UNREACHABLE();
  }
  return Object::null();
}

StringPtr BytecodeReaderHelper::ReadString(bool is_canonical) {
  const int kFlagTwoByteString = 1;
  const int kHeaderFields = 2;
  const int kUInt32Size = 4;

  uint32_t ref = reader_.ReadUInt();
  const bool isOneByteString = (ref & kFlagTwoByteString) == 0;
  intptr_t index = ref >> 1;

  if (!isOneByteString) {
    const uint32_t num_one_byte_strings =
        reader_.ReadUInt32At(bytecode_component_->GetStringsHeaderOffset());
    index += num_one_byte_strings;
  }

  AlternativeReadingScope alt(&reader_,
                              bytecode_component_->GetStringsHeaderOffset() +
                                  (kHeaderFields + index - 1) * kUInt32Size);
  intptr_t start_offs = reader_.ReadUInt32();
  intptr_t end_offs = reader_.ReadUInt32();
  if (index == 0) {
    // For the 0-th string we read a header field instead of end offset of
    // the previous string.
    start_offs = 0;
  }

  // Bytecode strings reside in ExternalTypedData which is not movable by GC,
  // so it is OK to take a direct pointer to string characters even if
  // symbol allocation triggers GC.
  const uint8_t* data = reader_.BufferAt(
      bytecode_component_->GetStringsContentsOffset() + start_offs);

  if (is_canonical) {
    if (isOneByteString) {
      return Symbols::FromLatin1(thread_, data, end_offs - start_offs);
    } else {
      return Symbols::FromUTF16(thread_,
                                reinterpret_cast<const uint16_t*>(data),
                                (end_offs - start_offs) >> 1);
    }
  } else {
    if (isOneByteString) {
      return String::FromLatin1(data, end_offs - start_offs, Heap::kOld);
    } else {
      return String::FromUTF16(reinterpret_cast<const uint16_t*>(data),
                               (end_offs - start_offs) >> 1, Heap::kOld);
    }
  }
}

ScriptPtr BytecodeReaderHelper::ReadSourceFile(const String& uri,
                                               intptr_t offset) {
  // SourceFile flags, must be in sync with SourceFile constants in
  // pkg/vm/lib/bytecode/declarations.dart.
  const int kHasLineStartsFlag = 1 << 0;
  const int kHasSourceFlag = 1 << 1;

  AlternativeReadingScope alt(&reader_, offset);

  const intptr_t flags = reader_.ReadUInt();
  const String& import_uri = String::CheckedHandle(Z, ReadObject());

  TypedData& line_starts = TypedData::Handle(Z);
  if ((flags & kHasLineStartsFlag) != 0) {
    const intptr_t line_starts_offset =
        bytecode_component_->GetLineStartsOffset() + reader_.ReadUInt();

    AlternativeReadingScope alt(&reader_, line_starts_offset);

    const intptr_t num_line_starts = reader_.ReadUInt();
    line_starts = reader_.ReadLineStartsData(num_line_starts);
  }

  String& source = String::Handle(Z);
  if ((flags & kHasSourceFlag) != 0) {
    source = ReadString(/* is_canonical = */ false);
  }

  const Script& script =
      Script::Handle(Z, Script::New(import_uri, uri, source));
  script.set_line_starts(line_starts);

  if (source.IsNull() && line_starts.IsNull()) {
    // This script provides a uri only, but no source or line_starts array.
    // This could be a reference to a Script in another kernel binary.
    // Make an attempt to find source and line starts when needed.
    script.SetLazyLookupSourceAndLineStarts(true);
  }

  return script.ptr();
}

TypeArgumentsPtr BytecodeReaderHelper::ReadTypeArguments() {
  const bool is_recursive = reading_type_arguments_of_recursive_type_;
  reading_type_arguments_of_recursive_type_ = false;
  const intptr_t length = reader_.ReadUInt();
  TypeArguments& type_arguments =
      TypeArguments::ZoneHandle(Z, TypeArguments::New(length));
  AbstractType& type = AbstractType::Handle(Z);
  for (intptr_t i = 0; i < length; ++i) {
    type ^= ReadObject();
    type_arguments.SetTypeAt(i, type);
  }
  if (is_recursive) {
    // Avoid canonicalization of type arguments of recursive type
    // as not all TypeRef objects are filled up at this point.
    // Type arguments will be canoncialized when the root recursive
    // type is canonicalized.
    ASSERT(pending_recursive_types_ != nullptr);
    return type_arguments.ptr();
  }
  return type_arguments.Canonicalize(thread_, nullptr);
}

void BytecodeReaderHelper::ReadAttributes(const Object& key) {
  ASSERT(key.IsFunction() || key.IsField());
  const auto& value = Object::Handle(Z, ReadObject());

  Array& attributes =
      Array::Handle(Z, I->group()->object_store()->bytecode_attributes());
  if (attributes.IsNull()) {
    attributes = HashTables::New<BytecodeAttributesMap>(16, Heap::kOld);
  }
  BytecodeAttributesMap map(attributes.ptr());
  bool present = map.UpdateOrInsert(key, value);
  ASSERT(!present);
  I->group()->object_store()->set_bytecode_attributes(map.Release());

  if (key.IsField()) {
    const Field& field = Field::Cast(key);
    const auto& inferred_type_attr =
        Array::CheckedHandle(Z, BytecodeReader::GetBytecodeAttribute(
                                    key, Symbols::vm_inferred_type_metadata()));

    if (!inferred_type_attr.IsNull() &&
        (InferredTypeBytecodeAttribute::GetPCAt(inferred_type_attr, 0) ==
         InferredTypeBytecodeAttribute::kFieldTypePC)) {
      const InferredTypeMetadata type =
          InferredTypeBytecodeAttribute::GetInferredTypeAt(
              Z, inferred_type_attr, 0);
      if (!type.IsTrivial()) {
        field.set_guarded_cid(type.cid);
        field.set_is_nullable(type.IsNullable());
        field.set_guarded_list_length(Field::kNoFixedLength);
      }
    }
  }
}

void BytecodeReaderHelper::ReadMembers(const Class& cls, bool discard_fields) {
  ASSERT(Thread::Current()->IsMutatorThread());
  ASSERT(cls.is_type_finalized());
  ASSERT(!cls.is_loaded());

  const intptr_t num_functions = reader_.ReadUInt();
  functions_ = &Array::Handle(Z, Array::New(num_functions, Heap::kOld));
  function_index_ = 0;

  ReadFieldDeclarations(cls, discard_fields);
  ReadFunctionDeclarations(cls);

  cls.set_is_loaded(true);
}

void BytecodeReaderHelper::ReadFieldDeclarations(const Class& cls,
                                                 bool discard_fields) {
  // Field flags, must be in sync with FieldDeclaration constants in
  // pkg/vm/lib/bytecode/declarations.dart.
  const int kHasNontrivialInitializerFlag = 1 << 0;
  const int kHasGetterFlag = 1 << 1;
  const int kHasSetterFlag = 1 << 2;
  const int kIsReflectableFlag = 1 << 3;
  const int kIsStaticFlag = 1 << 4;
  const int kIsConstFlag = 1 << 5;
  const int kIsFinalFlag = 1 << 6;
  const int kIsCovariantFlag = 1 << 7;
  const int kIsGenericCovariantImplFlag = 1 << 8;
  const int kHasSourcePositionsFlag = 1 << 9;
  const int kHasAnnotationsFlag = 1 << 10;
  const int kHasPragmaFlag = 1 << 11;
  const int kHasCustomScriptFlag = 1 << 12;
  const int kHasInitializerCodeFlag = 1 << 13;
  const int kHasAttributesFlag = 1 << 14;
  const int kIsLateFlag = 1 << 15;
  const int kIsExtensionMemberFlag = 1 << 16;
  const int kHasInitializerFlag = 1 << 17;

  const int num_fields = reader_.ReadListLength();
  if ((num_fields == 0) && !cls.is_enum_class()) {
    return;
  }
  const Array& fields = Array::Handle(
      Z, Array::New(num_fields + (cls.is_enum_class() ? 1 : 0), Heap::kOld));
  String& name = String::Handle(Z);
  Object& script_class = Object::Handle(Z);
  AbstractType& type = AbstractType::Handle(Z);
  Field& field = Field::Handle(Z);
  Instance& value = Instance::Handle(Z);
  Function& function = Function::Handle(Z);

  for (intptr_t i = 0; i < num_fields; ++i) {
    intptr_t flags = reader_.ReadUInt();

    const bool is_static = (flags & kIsStaticFlag) != 0;
    const bool is_final = (flags & kIsFinalFlag) != 0;
    const bool is_const = (flags & kIsConstFlag) != 0;
    const bool is_late = (flags & kIsLateFlag) != 0;
    const bool has_nontrivial_initializer =
        (flags & kHasNontrivialInitializerFlag) != 0;
    const bool has_pragma = (flags & kHasPragmaFlag) != 0;
    const bool is_extension_member = (flags & kIsExtensionMemberFlag) != 0;
    const bool has_initializer = (flags & kHasInitializerFlag) != 0;

    name ^= ReadObject();
    type ^= ReadObject();

    if ((flags & kHasCustomScriptFlag) != 0) {
      Script& script = Script::CheckedHandle(Z, ReadObject());
      script_class = GetPatchClass(cls, script);
    } else {
      script_class = cls.ptr();
    }

    TokenPosition position = TokenPosition::kNoSource;
    TokenPosition end_position = TokenPosition::kNoSource;
    if ((flags & kHasSourcePositionsFlag) != 0) {
      position = reader_.ReadPosition();
      end_position = reader_.ReadPosition();
    }

    field = Field::New(name, is_static, is_final, is_const,
                       (flags & kIsReflectableFlag) != 0, is_late, script_class,
                       type, position, end_position);

    if (is_static) {
      thread_->isolate_group()->RegisterStaticField(field, value);
    }

    field.set_is_declared_in_bytecode(true);
    field.set_has_pragma(has_pragma);
    field.set_is_covariant((flags & kIsCovariantFlag) != 0);
    field.set_is_generic_covariant_impl((flags & kIsGenericCovariantImplFlag) !=
                                        0);
    field.set_has_nontrivial_initializer(has_nontrivial_initializer);
    field.set_is_extension_member(is_extension_member);
    field.set_has_initializer(has_initializer);

    if (!has_nontrivial_initializer) {
      value ^= ReadObject();
      if (is_static) {
        if (field.is_late() && !has_initializer) {
          field.SetStaticValue(Object::sentinel());
          field.SetStaticConstFieldValue(Sentinel::null_instance(), false);
        } else {
          field.SetStaticValue(value);
          field.SetStaticConstFieldValue(value, false);
        }
      } else {
        // Null-initialized instance fields are tracked separately for each
        // constructor (see handling of kHasNullableFieldsFlag).
        if (!value.IsNull()) {
          // Note: optimizer relies on DoubleInitialized bit in its
          // field-unboxing heuristics.
          // See JitCallSpecializer::VisitStoreInstanceField for more details.
          field.RecordStore(value);
          if (value.IsDouble()) {
            field.set_is_double_initialized(true);
          }
        }
      }
    }

    if ((flags & kHasInitializerCodeFlag) != 0) {
      const intptr_t code_offset = reader_.ReadUInt();
      field.set_bytecode_offset(code_offset +
                                bytecode_component_->GetCodesOffset());
      if (is_static) {
        field.SetStaticValue(Object::sentinel());
        field.SetStaticConstFieldValue(Sentinel::null_instance(), false);
      }
    }

    if ((flags & kHasGetterFlag) != 0) {
      name ^= ReadObject();
      const FunctionType& signature2 =
          FunctionType::ZoneHandle(FunctionType::New());
      function = Function::New(signature2,
                               name,
                               is_static ?
                                         UntaggedFunction::kImplicitStaticGetter
                                         : UntaggedFunction::kImplicitGetter,
                               is_static, is_const,
                               false,  // is_abstract
                               false,  // is_external
                               false,  // is_native
                               script_class, position);
      function.set_end_token_pos(end_position);
      signature2.set_result_type(type);
      function.set_signature(signature2);
      function.set_is_debuggable(false);
      function.set_accessor_field(field);
      function.set_is_declared_in_bytecode(true);
      function.set_is_extension_member(is_extension_member);
      if (is_const && has_nontrivial_initializer) {
        function.set_bytecode_offset(field.bytecode_offset());
      }
      H.SetupFieldAccessorFunction(cls, function, type);
      functions_->SetAt(function_index_++, function);
    }

    if ((flags & kHasSetterFlag) != 0) {
      ASSERT(is_late || ((!is_static) && (!is_final)));
      ASSERT(!is_const);
      name ^= ReadObject();
      const FunctionType& signature2 =
          FunctionType::ZoneHandle(FunctionType::New());
      function = Function::New(signature2,
                               name, UntaggedFunction::kImplicitSetter,
                               is_static,
                               false,  // is_const
                               false,  // is_abstract
                               false,  // is_external
                               false,  // is_native
                               script_class, position);
      function.set_end_token_pos(end_position);
      signature2.set_result_type(Object::void_type());
      function.set_signature(signature2);
      function.set_is_debuggable(false);
      function.set_accessor_field(field);
      function.set_is_declared_in_bytecode(true);
      function.set_is_extension_member(is_extension_member);
      H.SetupFieldAccessorFunction(cls, function, type);
      functions_->SetAt(function_index_++, function);
    }

    if ((flags & kHasAnnotationsFlag) != 0) {
      intptr_t annotations_offset =
          reader_.ReadUInt() + bytecode_component_->GetAnnotationsOffset();
      ASSERT(annotations_offset > 0);

      if (FLAG_enable_mirrors || has_pragma) {
        Library& library = Library::Handle(Z, cls.library());
        library.AddMetadata(field, 0, annotations_offset);
        if (has_pragma) {
          library.GetMetadata(field);
        }
      }
    }

    if ((flags & kHasAttributesFlag) != 0) {
      ReadAttributes(field);
    }

    fields.SetAt(i, field);
  }

  if (cls.is_enum_class()) {
    // Add static field 'const _deleted_enum_sentinel'.
    field = Field::New(Symbols::_DeletedEnumSentinel(),
                       /* is_static = */ true,
                       /* is_final = */ true,
                       /* is_const = */ true,
                       /* is_reflectable = */ false,
                       /* is_late = */ false, cls, Object::dynamic_type(),
                       TokenPosition::kNoSource, TokenPosition::kNoSource);

    // enum value is considered as CONST STATIC
    thread_->isolate_group()->RegisterStaticField(field, value);

    fields.SetAt(num_fields, field);
  }

  if (!discard_fields) {
    cls.SetFields(fields);
  }

  if (cls.IsTopLevel()) {
    const Library& library = Library::Handle(Z, cls.library());
    for (intptr_t i = 0, n = fields.Length(); i < n; ++i) {
      field ^= fields.At(i);
      name = field.name();
      library.AddObject(field, name);
    }
  }
}

PatchClassPtr BytecodeReaderHelper::GetPatchClass(const Class& cls,
                                                  const Script& script) {
  if (patch_class_ != nullptr && patch_class_->patched_class() == cls.ptr() &&
      patch_class_->script() == script.ptr()) {
    return patch_class_->ptr();
  }
  if (patch_class_ == nullptr) {
    patch_class_ = &PatchClass::Handle(Z);
  }
  *patch_class_ = PatchClass::New(cls, script);
  return patch_class_->ptr();
}

void BytecodeReaderHelper::ReadFunctionDeclarations(const Class& cls) {
  // Function flags, must be in sync with FunctionDeclaration constants in
  // pkg/vm/lib/bytecode/declarations.dart.
  const int kIsConstructorFlag = 1 << 0;
  const int kIsGetterFlag = 1 << 1;
  const int kIsSetterFlag = 1 << 2;
  const int kIsFactoryFlag = 1 << 3;
  const int kIsStaticFlag = 1 << 4;
  const int kIsAbstractFlag = 1 << 5;
  const int kIsConstFlag = 1 << 6;
  const int kHasOptionalPositionalParamsFlag = 1 << 7;
  const int kHasOptionalNamedParamsFlag = 1 << 8;
  const int kHasTypeParamsFlag = 1 << 9;
  const int kIsReflectableFlag = 1 << 10;
  const int kIsDebuggableFlag = 1 << 11;
  const int kIsAsyncFlag = 1 << 12;
  const int kIsAsyncStarFlag = 1 << 13;
  const int kIsSyncStarFlag = 1 << 14;
  // const int kIsForwardingStubFlag = 1 << 15;
  const int kIsNoSuchMethodForwarderFlag = 1 << 16;
  const int kIsNativeFlag = 1 << 17;
  const int kIsExternalFlag = 1 << 18;
  const int kHasSourcePositionsFlag = 1 << 19;
  const int kHasAnnotationsFlag = 1 << 20;
  const int kHasPragmaFlag = 1 << 21;
  const int kHasCustomScriptFlag = 1 << 22;
  const int kHasAttributesFlag = 1 << 23;
  const int kIsExtensionMemberFlag = 1 << 24;
  const int kHasParameterFlagsFlag = 1 << 25;

  const intptr_t num_functions = reader_.ReadListLength();
  ASSERT(function_index_ + num_functions == functions_->Length());

  if (function_index_ + num_functions == 0) {
    return;
  }

  String& name = String::Handle(Z);
  Object& script_class = Object::Handle(Z);
  Function& function = Function::Handle(Z);
  Array& parameter_types = Array::Handle(Z);
  AbstractType& type = AbstractType::Handle(Z);

  name = cls.ScrubbedName();

  for (intptr_t i = 0; i < num_functions; ++i) {
    intptr_t flags = reader_.ReadUInt();

    const bool is_static = (flags & kIsStaticFlag) != 0;
    const bool is_factory = (flags & kIsFactoryFlag) != 0;
    const bool is_native = (flags & kIsNativeFlag) != 0;
    const bool has_pragma = (flags & kHasPragmaFlag) != 0;
    const bool is_extension_member = (flags & kIsExtensionMemberFlag) != 0;

    name ^= ReadObject();

    if ((flags & kHasCustomScriptFlag) != 0) {
      Script& script = Script::CheckedHandle(Z, ReadObject());
      script_class = GetPatchClass(cls, script);
    } else {
      script_class = cls.ptr();
    }

    TokenPosition position = TokenPosition::kNoSource;
    TokenPosition end_position = TokenPosition::kNoSource;
    if ((flags & kHasSourcePositionsFlag) != 0) {
      position = reader_.ReadPosition();
      end_position = reader_.ReadPosition();
    }

    UntaggedFunction::Kind kind = UntaggedFunction::kRegularFunction;
    if ((flags & kIsGetterFlag) != 0) {
      kind = UntaggedFunction::kGetterFunction;
    } else if ((flags & kIsSetterFlag) != 0) {
      kind = UntaggedFunction::kSetterFunction;
    } else if ((flags & (kIsConstructorFlag | kIsFactoryFlag)) != 0) {
      kind = UntaggedFunction::kConstructor;
      name = ConstructorName(cls, name);
    }

    const FunctionType& signature2 =
        FunctionType::ZoneHandle(FunctionType::New());
    function = Function::New(signature2, name, kind, is_static,
                             (flags & kIsConstFlag) != 0,
                             (flags & kIsAbstractFlag) != 0,
                             (flags & kIsExternalFlag) != 0, is_native,
                             script_class, position);

    const bool is_expression_evaluation =
        (name.ptr() == Symbols::DebugProcedureName().ptr());

    // Declare function scope as types (type parameters) in function
    // signature may back-reference to the function being declared.
    // At this moment, owner class is not fully loaded yet and it won't be
    // able to serve function lookup requests.
    FunctionScope function_scope(this, function, name, cls);

    function.set_is_declared_in_bytecode(true);
    function.set_has_pragma(has_pragma);
    function.set_end_token_pos(end_position);
    function.set_is_synthetic((flags & kIsNoSuchMethodForwarderFlag) != 0);
    function.set_is_reflectable((flags & kIsReflectableFlag) != 0);
    function.set_is_debuggable((flags & kIsDebuggableFlag) != 0);
    function.set_is_extension_member(is_extension_member);

    // _AsyncAwaitCompleter.start should be made non-visible in stack traces,
    // since it is an implementation detail of our await/async desugaring.
    if (Symbols::_AsyncAwaitStart().Equals(name)) {
      function.set_is_visible(!FLAG_lazy_async_stacks);
    }

    if ((flags & kIsSyncStarFlag) != 0) {
      function.set_modifier(UntaggedFunction::kSyncGen);
      function.set_is_visible(!FLAG_lazy_async_stacks);
    } else if ((flags & kIsAsyncFlag) != 0) {
      function.set_modifier(UntaggedFunction::kAsync);
      function.set_is_inlinable(!FLAG_lazy_async_stacks);
      function.set_is_visible(!FLAG_lazy_async_stacks);
    } else if ((flags & kIsAsyncStarFlag) != 0) {
      function.set_modifier(UntaggedFunction::kAsyncGen);
      function.set_is_inlinable(!FLAG_lazy_async_stacks);
      function.set_is_visible(!FLAG_lazy_async_stacks);
    }

    if ((flags & kHasTypeParamsFlag) != 0) {
      ReadTypeParametersDeclaration2(Class::Handle(Z), function);
    }

    const intptr_t num_implicit_params = (!is_static || is_factory) ? 1 : 0;
    const intptr_t num_params = num_implicit_params + reader_.ReadUInt();

    intptr_t num_required_params = num_params;
    if ((flags & (kHasOptionalPositionalParamsFlag |
                  kHasOptionalNamedParamsFlag)) != 0) {
      num_required_params = num_implicit_params + reader_.ReadUInt();
    }

    FunctionType& signature = FunctionType::Handle(Z, function.signature());
    signature.set_num_fixed_parameters(num_required_params);
    signature.SetNumOptionalParameters(
        num_params - num_required_params,
        (flags & kHasOptionalNamedParamsFlag) == 0);
    intptr_t num_params_all = (flags & kHasOptionalNamedParamsFlag) == 0 ?
                                       num_params : num_required_params;

    parameter_types = Array::New(num_params, Heap::kOld);
    signature.set_parameter_types(parameter_types);
    function.CreateNameArray();
    signature.CreateNameArrayIncludingFlags();

    intptr_t param_index = 0;
    if (!is_static) {
      if (is_expression_evaluation) {
        // Do not reference enclosing class as expression evaluation
        // method logically belongs to another (real) class.
        // Enclosing class is not registered and doesn't have
        // a valid cid, so it can't be used in a type.
        signature.SetParameterTypeAt(param_index, AbstractType::dynamic_type());
      } else {
        signature.SetParameterTypeAt(param_index, H.GetDeclarationType(cls));
      }
      function.SetParameterNameAt(param_index, Symbols::This());
      ++param_index;
    } else if (is_factory) {
      signature.SetParameterTypeAt(param_index, AbstractType::dynamic_type());
      function.SetParameterNameAt(param_index,
                                  Symbols::TypeArgumentsParameter());
      ++param_index;
    }

    for (; param_index < num_params_all; ++param_index) {
      name ^= ReadObject();
      function.SetParameterNameAt(param_index, name);
      type ^= ReadObject();
      signature.SetParameterTypeAt(param_index, type);
    }
      for (; param_index < num_params; ++param_index) {
          name ^= ReadObject();
          type ^= ReadObject();
          signature.SetParameterNameAt(param_index, name);
          signature.SetParameterTypeAt(param_index, type);
      }

    if ((flags & kHasParameterFlagsFlag) != 0) {
      const intptr_t length = reader_.ReadUInt();
      const intptr_t offset = function.NumImplicitParameters();
      for (intptr_t i = 0; i < length; i++) {
        const intptr_t param_flags = reader_.ReadUInt();
        if ((param_flags & Parameter::kIsRequiredFlag) != 0) {
          RELEASE_ASSERT(function.HasOptionalNamedParameters());
          RELEASE_ASSERT(i + offset >= function.num_fixed_parameters());
          signature.SetIsRequiredAt(i + offset);
        }
      }
    }
    signature.FinalizeNameArray();

    type ^= ReadObject();
    signature.set_result_type(type);
    function.SetSignature(signature);

    if (is_native) {
      name ^= ReadObject();
      function.set_native_name(name);
    }

    if ((flags & kIsAbstractFlag) == 0) {
      const intptr_t code_offset = reader_.ReadUInt();
      function.set_bytecode_offset(code_offset +
                                   bytecode_component_->GetCodesOffset());
    }

    if ((flags & kHasAnnotationsFlag) != 0) {
      const intptr_t annotations_offset =
          reader_.ReadUInt() + bytecode_component_->GetAnnotationsOffset();
      ASSERT(annotations_offset > 0);

      if (FLAG_enable_mirrors || has_pragma) {
        Library& library = Library::Handle(Z, cls.library());
        library.AddMetadata(function, 0, annotations_offset);

        if (has_pragma) {
          if (H.constants().IsNull() &&
              library.ptr() == Library::CoreLibrary()) {
            // Bootstrapping, need to postpone evaluation of pragma annotations
            // as classes are not fully loaded/finalized yet.
            const auto& pragma_funcs = GrowableObjectArray::Handle(
                Z, H.EnsurePotentialPragmaFunctions());
            pragma_funcs.Add(function);
          } else {
            library.GetMetadata(function);
          }
        }
      }
    }

    if ((flags & kHasAttributesFlag) != 0) {
      ASSERT(!is_expression_evaluation);
      ReadAttributes(function);
    }

    if (is_expression_evaluation) {
#if !defined(DART_DYNAMIC_RUNTIME)
      H.SetExpressionEvaluationFunction(function);
      // Read bytecode of expression evaluation function eagerly,
      // while expression_evaluation_library_ and FunctionScope
      // are still set, as its constant pool may reference back to a library
      // or a function which are not registered and cannot be looked up.
      ASSERT(!function.is_abstract());
      ASSERT(function.bytecode_offset() != 0);
      // Replace class of the function in scope as we're going to look for
      // expression evaluation function in a real class.
      if (!cls.IsTopLevel()) {
        scoped_function_class_ = H.GetExpressionEvaluationRealClass();
      }
      CompilerState compiler_state(thread_, FLAG_precompiled_mode, false);
      ReadCode(function, function.bytecode_offset());
#endif
    }

    functions_->SetAt(function_index_++, function);
  }

  {
    Thread* thread = Thread::Current();
    SafepointWriteRwLocker ml(thread, thread->isolate_group()->program_lock());
    cls.SetFunctions(*functions_);
  }

  if (cls.IsTopLevel()) {
    const Library& library = Library::Handle(Z, cls.library());
    for (intptr_t i = 0, n = functions_->Length(); i < n; ++i) {
      function ^= functions_->At(i);
      name = function.name();
      library.AddObject(function, name);
    }
  }

  functions_ = nullptr;
}

void BytecodeReaderHelper::LoadReferencedClass(const Class& cls) {
  ASSERT(!cls.is_declaration_loaded());

  if (!cls.is_declared_in_bytecode()) {
    cls.EnsureDeclarationLoaded();
    return;
  }

  const auto& script = Script::Handle(Z, cls.script());
  if (H.GetKernelProgramInfo().ptr() != script.kernel_program_info()) {
    // Class comes from a different binary.
    cls.EnsureDeclarationLoaded();
    return;
  }

  // We can reuse current BytecodeReaderHelper.
  ActiveClassScope active_class_scope(active_class_, &cls);
  AlternativeReadingScope alt(&reader_, cls.bytecode_offset());
  ReadClassDeclaration(cls);
}

void BytecodeReaderHelper::ReadClassDeclaration(const Class& cls) {
  // Class flags, must be in sync with ClassDeclaration constants in
  // pkg/vm/lib/bytecode/declarations.dart.
  const int kIsAbstractFlag = 1 << 0;
  const int kIsEnumFlag = 1 << 1;
  const int kHasTypeParamsFlag = 1 << 2;
  const int kHasTypeArgumentsFlag = 1 << 3;
  const int kIsTransformedMixinApplicationFlag = 1 << 4;
  const int kHasSourcePositionsFlag = 1 << 5;
  const int kHasAnnotationsFlag = 1 << 6;
  const int kHasPragmaFlag = 1 << 7;

  // Class is allocated when reading library declaration in
  // BytecodeReaderHelper::ReadLibraryDeclaration.
  // Its cid is set in Class::New / Isolate::RegisterClass /
  // ClassTable::Register, unless it was loaded for expression evaluation.
  ASSERT(cls.is_declared_in_bytecode());
  ASSERT(!cls.is_declaration_loaded() || loading_native_wrappers_library_);

  const intptr_t flags = reader_.ReadUInt();
  const bool has_pragma = (flags & kHasPragmaFlag) != 0;

  // Set early to enable access to type_parameters().
  // TODO(alexmarkov): revise early stamping of native wrapper classes
  //  as loaded.
  if (!cls.is_declaration_loaded()) {
    cls.set_is_declaration_loaded();
  }

  const auto& script = Script::CheckedHandle(Z, ReadObject());
  cls.set_script(script);

  TokenPosition position = TokenPosition::kNoSource;
  TokenPosition end_position = TokenPosition::kNoSource;
  if ((flags & kHasSourcePositionsFlag) != 0) {
    position = reader_.ReadPosition();
    end_position = reader_.ReadPosition();
    cls.set_token_pos(position);
    cls.set_end_token_pos(end_position);
  }

  cls.set_has_pragma(has_pragma);

  if ((flags & kIsAbstractFlag) != 0) {
    cls.set_is_abstract();
  }
  if ((flags & kIsEnumFlag) != 0) {
    cls.set_is_enum_class();
  }
  if ((flags & kIsTransformedMixinApplicationFlag) != 0) {
    cls.set_is_transformed_mixin_application();
  }

  intptr_t num_type_arguments = 0;
  if ((flags & kHasTypeArgumentsFlag) != 0) {
    num_type_arguments = reader_.ReadUInt();
  }
  cls.set_num_type_arguments(num_type_arguments);

  if ((flags & kHasTypeParamsFlag) != 0) {
    ReadTypeParametersDeclaration(cls, Function::null_function());
  }

  auto& type = AbstractType::CheckedHandle(Z, ReadObject());
  cls.set_super_type(type);

  const intptr_t num_interfaces = reader_.ReadUInt();
  if (num_interfaces > 0) {
    const auto& interfaces =
        Array::Handle(Z, Array::New(num_interfaces, Heap::kOld));
    for (intptr_t i = 0; i < num_interfaces; ++i) {
      type ^= ReadObject();
      interfaces.SetAt(i, type);
    }
    cls.set_interfaces(interfaces);
  }

  if ((flags & kHasAnnotationsFlag) != 0) {
    intptr_t annotations_offset =
        reader_.ReadUInt() + bytecode_component_->GetAnnotationsOffset();
    ASSERT(annotations_offset > 0);

    if (FLAG_enable_mirrors || has_pragma) {
      const auto& library = Library::Handle(Z, cls.library());
      if (cls.IsTopLevel()) {
        ASSERT(!has_pragma);
        library.AddMetadata(cls, 0, annotations_offset);
      } else {
        library.AddMetadata(cls, 0, annotations_offset);
      }
    }
  }

  const intptr_t members_offset = reader_.ReadUInt();
  cls.set_bytecode_offset(members_offset +
                          bytecode_component_->GetMembersOffset());

  // All types are finalized if loading from bytecode.
  // TODO(alexmarkov): revise early stamping of native wrapper classes
  //  as type-finalized.
  if (!cls.is_type_finalized()) {
    cls.set_is_type_finalized();
  }

  // Avoid registering expression evaluation class in a hierarchy, as
  // it doesn't have cid and shouldn't be found when enumerating subclasses.
  if (expression_evaluation_library_ == nullptr) {
    // TODO(alexmarkov): move this to class finalization.
    ClassFinalizer::RegisterClassInHierarchy(Z, cls);
  }
}

void BytecodeReaderHelper::ReadLibraryDeclaration(const Library& library,
                                                  bool lookup_classes) {
  // Library flags, must be in sync with LibraryDeclaration constants in
  // pkg/vm/lib/bytecode/declarations.dart.
  const int kUsesDartMirrorsFlag = 1 << 0;
  const int kUsesDartFfiFlag = 1 << 1;
  const int kHasExtensionsFlag = 1 << 2;
  const int kIsNonNullableByDefaultFlag = 1 << 3;

  ASSERT(library.is_declared_in_bytecode());
  ASSERT(!library.Loaded());
  ASSERT(library.toplevel_class() == Object::null());

  // TODO(alexmarkov): fill in library.used_scripts.

  const intptr_t flags = reader_.ReadUInt();
  if (((flags & kUsesDartMirrorsFlag) != 0) && !FLAG_enable_mirrors) {
    H.ReportError(
        "import of dart:mirrors is not supported in the current Dart runtime");
  }
  if (((flags & kUsesDartFfiFlag) != 0) && !Api::IsFfiEnabled()) {
    H.ReportError(
        "import of dart:ffi is not supported in the current Dart runtime");
  }

  auto& name = String::CheckedHandle(Z, ReadObject());
  library.SetName(name);

  const auto& script = Script::CheckedHandle(Z, ReadObject());

  if ((flags & kHasExtensionsFlag) != 0) {
    const intptr_t num_extensions = reader_.ReadUInt();
    auto& import_namespace = Namespace::Handle(Z);
    auto& native_library = Library::Handle(Z);
    for (intptr_t i = 0; i < num_extensions; ++i) {
      name ^= ReadObject();
      ASSERT(name.StartsWith(Symbols::DartExtensionScheme()));

      // Create a dummy library and add it as an import to the current library.
      // Actual loading occurs in KernelLoader::LoadNativeExtensionLibraries().
      // This also allows later to discover and reload this native extension,
      // e.g. when running from an app-jit snapshot.
      // See Loader::ReloadNativeExtensions(...) which relies on
      // Dart_GetImportsOfScheme('dart-ext').
      native_library = Library::New(name);
      import_namespace = Namespace::New(native_library, Array::null_array(),
                                        Array::null_array(), library);
      library.AddImport(import_namespace);
    }
    H.AddPotentialExtensionLibrary(library);
  }

  if ((flags & kIsNonNullableByDefaultFlag) != 0) {
    library.set_is_nnbd(true);
  }

  // The bootstrapper will take care of creating the native wrapper classes,
  // but we will add the synthetic constructors to them here.
  if (name.ptr() ==
      Symbols::Symbol(Symbols::kDartNativeWrappersLibNameId).ptr()) {
    ASSERT(library.LoadInProgress());
    loading_native_wrappers_library_ = true;
  } else {
    loading_native_wrappers_library_ = false;
    library.SetLoadInProgress();
  }

  const bool register_class = !IsExpressionEvaluationLibrary(library);

  const intptr_t num_classes = reader_.ReadUInt();
  ASSERT(num_classes > 0);
  auto& cls = Class::Handle(Z);

  for (intptr_t i = 0; i < num_classes; ++i) {
    name ^= ReadObject();
    const intptr_t class_offset =
        bytecode_component_->GetClassesOffset() + reader_.ReadUInt();

    if (i == 0) {
      ASSERT(name.ptr() == Symbols::Empty().ptr());
      cls = Class::New(library, Symbols::TopLevel(), script,
                       TokenPosition::kNoSource, register_class);
      library.set_toplevel_class(cls);
    } else {
      if (lookup_classes) {
        cls = library.LookupLocalClass(name);
      }
      if (lookup_classes && !cls.IsNull()) {
        ASSERT(!cls.is_declaration_loaded() ||
               loading_native_wrappers_library_);
        cls.set_script(script);
      } else {
        cls = Class::New(library, name, script, TokenPosition::kNoSource,
                         register_class);
        if (register_class) {
          library.AddClass(cls);
        }
      }
    }

    cls.set_is_declared_in_bytecode(true);
    cls.set_bytecode_offset(class_offset);

    if (loading_native_wrappers_library_ || !register_class) {
      AlternativeReadingScope alt(&reader_, class_offset);
      ReadClassDeclaration(cls);
      ActiveClassScope active_class_scope(active_class_, &cls);
      AlternativeReadingScope alt2(&reader_, cls.bytecode_offset());
      ReadMembers(cls, /* discard_fields = */ false);
    }
  }

  ASSERT(!library.Loaded());
  library.SetLoaded();

  loading_native_wrappers_library_ = false;
}

#if defined(DART_DYNAMIC_RUNTIME)
void BytecodeReaderHelper::AlignClass(const Library& aotLibrary,
                                      const Class& aotClass,
                                      const Library& tmpLibrary,
                                      const Class& tmpClass) {
  Isolate* isolate = Isolate::Current();
  isolate->setIsAlignClass(true);
  std::map<std::string, int>* pageKeys = isolate->getPageKeys();
  OS::PrintErr("begin align cls %s\n", aotClass.ToCString());
  tmpClass.EnsureIsFinalized(Thread::Current());
  if (aotClass.InstanceSize() != tmpClass.InstanceSize()) {
      OS::PrintErr("lib: %s, clz: %s instance size error!, aotsize:%" Pd ","
                 "tmpsize:%" Pd "\n", String::Handle(
                     aotLibrary.url()).ToCString(),
                 String::Handle(aotClass.Name()).ToCString(),
                 aotClass.InstanceSize(),
                 tmpClass.InstanceSize());
      return;
  }
  Array& functions = Array::Handle(tmpClass.functions());
  intptr_t funcsLength = functions.Length();
  auto& func = Function::Handle();
  auto& funcName = String::Handle();
  auto& aotFunc = Function::Handle();
  auto& libName = String::Handle();
  auto& className = String::Handle();
  libName = aotLibrary.url();
  className = aotClass.UserVisibleName();
  bool isAlign = false;
  for (intptr_t i=0; i < funcsLength; i++) {
      func = Function::RawCast(functions.At(i));
      funcName = func.name();
      aotFunc = aotClass.LookupFunctionAllowPrivate(funcName);
      if (aotFunc.IsNull()) {
          if (!func.is_static()) {
            FunctionType::Handle(func.signature()).SetParameterTypeAt(0,
                                        H.GetDeclarationType(aotClass));
          }
          func.set_owner(aotClass);
          aotClass.AddFunction(func);
          isAlign = true;
      } else {
          if (func.is_declared_in_bytecode()) {
              bool isNeedModify = false;
              std::string pageKey = libName.ToCString();
              pageKey.append("#");
              pageKey.append(className.ToCString());
              pageKey.append("#");
              pageKey.append(aotFunc.UserVisibleNameCString());
              if ((*pageKeys)[pageKey] == 1) {
                  isNeedModify = true;
              }
              isNeedModify |= (!aotFunc.HasCode());
              if (isNeedModify) {
                  if (aotFunc.HasCode()) {
                    uword code_start =
                        dart::Code::EntryPointOf(aotFunc.CurrentCode());
                    std::map<uword , FunctionPtr>* patchFunctionsMap =
                        isolate->getPatchFunctionsMap();
                    (*patchFunctionsMap)[code_start] = aotFunc.ptr();
                  }
                  aotFunc.set_is_declared_in_bytecode(true);
                  aotFunc.set_bytecode_offset(func.bytecode_offset());
                  aotFunc.SetInstructions(StubCode::InterpretCall());
                  isAlign = true;
              }
          }
      }
  }
  if (isAlign) {
      aotClass.set_script(Script::Handle(tmpClass.script()));
      aotClass.set_is_declared_in_bytecode(true);
      aotClass.set_bytecode_offset(tmpClass.bytecode_offset());
      aotLibrary.set_is_declared_in_bytecode(true);
      aotLibrary.set_bytecode_offset(tmpLibrary.bytecode_offset());
  }
  isolate->setIsAlignClass(false);
}
#endif

void BytecodeReaderHelper::ReadLibraryDeclarations(intptr_t num_libraries) {
  auto& library = Library::Handle(Z);
  auto& uri = String::Handle(Z);
#if defined(DART_DYNAMIC_RUNTIME)
  GrowableObjectArray& tmpLibs =
          GrowableObjectArray::Handle(Z, GrowableObjectArray::New());
#endif

  for (intptr_t i = 0; i < num_libraries; ++i) {
    uri ^= ReadObject();
    const intptr_t library_offset =
        bytecode_component_->GetLibrariesOffset() + reader_.ReadUInt();

    if (!FLAG_precompiled_mode && !IG->should_load_vmservice()) {
      if (uri.ptr() == Symbols::DartVMServiceIO().ptr()) {
        continue;
      }
    }

    bool lookup_classes = true;
    library = Library::LookupLibrary(thread_, uri);
    if (library.IsNull()) {
      lookup_classes = false;
      library = Library::New(uri);

      if (uri.ptr() == Symbols::EvalSourceUri().ptr()) {
        ASSERT(expression_evaluation_library_ == nullptr);
        expression_evaluation_library_ = &Library::Handle(Z, library.ptr());
      } else {
        library.Register(thread_);
      }
    }

    if (library.Loaded()) {
#if defined(DART_DYNAMIC_RUNTIME)
      if (!library.is_declared_in_bytecode()) {
        auto& tmplibrary = Library::Handle(Z);
        // OS::PrintErr("duplicate lib %s\n", uri.ToCString());
        tmplibrary = Library::New(uri);
        tmplibrary.set_is_declared_in_bytecode(true);
        tmplibrary.set_bytecode_offset(library_offset);
        AlternativeReadingScope alt(&reader_, library_offset);
        ReadLibraryDeclaration(tmplibrary, false);
        tmpLibs.Add(tmplibrary);
        tmpLibs.Add(library);
      }
#endif
        continue;
    }

    library.set_is_declared_in_bytecode(true);
    library.set_bytecode_offset(library_offset);

    AlternativeReadingScope alt(&reader_, library_offset);
    ReadLibraryDeclaration(library, lookup_classes);
  }
#if defined(DART_DYNAMIC_RUNTIME)
  GrowableObjectArray& tmpClzs =
            GrowableObjectArray::Handle(Z, GrowableObjectArray::New());
    intptr_t tmpLibsLen = tmpLibs.Length();
    auto& tmpLibrary = Library::Handle(Z);
    for (intptr_t i = 0; i < tmpLibsLen; i++) {
      tmpLibrary = Library::RawCast(tmpLibs.At(i));
      i++;
      library = Library::RawCast(tmpLibs.At(i));
      if (library.IsNull()) {
        continue;
      }
      auto& tmpCls = Class::Handle(Z);
      auto& aotCls = Class::Handle(Z);
      tmpCls = tmpLibrary.toplevel_class();
      aotCls = library.toplevel_class();
      tmpClzs.Add(tmpCls);
      tmpClzs.Add(aotCls);

      Array& clsDict = Array::Handle(tmpLibrary.dictionary2());
      intptr_t dict_size = clsDict.Length() - 1;
      intptr_t index = 0;

      while (index < dict_size) {
        Object& entry = Object::Handle();
        entry = clsDict.At(index);
        if (!entry.IsNull() && entry.IsClass()) {
          tmpCls = Class::Cast(entry).ptr();
          aotCls = library.LookupLocalClass(String::Handle(tmpCls.Name()));
          if (aotCls.IsNull()) {
            OS::PrintErr("add class %s to lib %s", tmpCls.ToCString(),
                       library.ToCString());
            tmpCls.set_library(library);
            library.AddClass(tmpCls);
            library.set_is_declared_in_bytecode(true);
            library.set_bytecode_offset(library.bytecode_offset());
          } else {
            tmpClzs.Add(tmpCls);
            tmpClzs.Add(aotCls);
          }
        }
        index++;
      }
    }

    intptr_t tmpClzsLen = tmpClzs.Length();
    auto& tmpCls = Class::Handle(Z);
    auto& aotCls = Class::Handle(Z);
    for (intptr_t i = 0; i< t mpClzsLen; i++) {
      tmpCls = Class::RawCast(tmpClzs.At(i));
      i++;
      aotCls = Class::RawCast(tmpClzs.At(i));
      tmpLibrary = tmpCls.library();
      library = aotCls.library();
      AlignClass(library, aotCls, tmpLibrary, tmpCls);
    }
#endif
}

void BytecodeReaderHelper::FindAndReadSpecificLibrary(const Library& library,
                                                      intptr_t num_libraries) {
  auto& uri = String::Handle(Z);
  for (intptr_t i = 0; i < num_libraries; ++i) {
    uri ^= ReadObject();
    const intptr_t library_offset =
        bytecode_component_->GetLibrariesOffset() + reader_.ReadUInt();

    if (uri.ptr() == library.url()) {
      library.set_is_declared_in_bytecode(true);
      library.set_bytecode_offset(library_offset);

      AlternativeReadingScope alt(&reader_, library_offset);
      ReadLibraryDeclaration(library, /* lookup_classes = */ true);
      return;
    }
  }
}

void BytecodeReaderHelper::FindModifiedLibrariesForHotReload(
    BitVector* modified_libs,
    intptr_t num_libraries) {
  auto& uri = String::Handle(Z);
  auto& lib = Library::Handle(Z);
  for (intptr_t i = 0; i < num_libraries; ++i) {
    uri ^= ReadObject();
    reader_.ReadUInt();  // Skip offset.

    lib = Library::LookupLibrary(thread_, uri);
    if (!lib.IsNull() && !lib.is_dart_scheme()) {
      // This is a library that already exists so mark it as being modified.
      modified_libs->Add(lib.index());
    }
  }
}

void BytecodeReaderHelper::ReadParameterCovariance(
    const Function& function,
    BitVector* is_covariant,
    BitVector* is_generic_covariant_impl) {
  ASSERT(function.is_declared_in_bytecode());

  const intptr_t num_params = function.NumParameters();
  ASSERT(is_covariant->length() == num_params);
  ASSERT(is_generic_covariant_impl->length() == num_params);

  AlternativeReadingScope alt(&reader_, function.bytecode_offset());

  const intptr_t code_flags = reader_.ReadUInt();
  if ((code_flags & Code::kHasParameterFlagsFlag) != 0) {
    const intptr_t num_explicit_params = reader_.ReadUInt();
    ASSERT(num_params ==
           function.NumImplicitParameters() + num_explicit_params);

    for (intptr_t i = function.NumImplicitParameters(); i < num_params; ++i) {
      const intptr_t flags = reader_.ReadUInt();

      if ((flags & Parameter::kIsCovariantFlag) != 0) {
        is_covariant->Add(i);
      }
      if ((flags & Parameter::kIsGenericCovariantImplFlag) != 0) {
        is_generic_covariant_impl->Add(i);
      }
    }
  }
}

ObjectPtr BytecodeReaderHelper::BuildParameterDescriptor(
    const Function& function) {
  ASSERT(function.is_declared_in_bytecode());

  Object& result = Object::Handle(Z);
  if (!function.HasBytecode()) {
    result = BytecodeReader::ReadFunctionBytecode(Thread::Current(), function);
    if (result.IsError()) {
      return result.ptr();
    }
  }

  const intptr_t num_params = function.NumParameters();
  const intptr_t num_implicit_params = function.NumImplicitParameters();
  const intptr_t num_explicit_params = num_params - num_implicit_params;
  const Array& descriptor = Array::Handle(
      Z, Array::New(num_explicit_params * Parser::kParameterEntrySize));

  // 1. Find isFinal in the Code declaration.
  bool found_final = false;
  if (!function.is_abstract()) {
    AlternativeReadingScope alt(&reader_, function.bytecode_offset());
    const intptr_t code_flags = reader_.ReadUInt();

    if ((code_flags & Code::kHasParameterFlagsFlag) != 0) {
      const intptr_t num_explicit_params_written = reader_.ReadUInt();
      ASSERT(num_explicit_params == num_explicit_params_written);
      for (intptr_t i = 0; i < num_explicit_params; ++i) {
        const intptr_t flags = reader_.ReadUInt();
        descriptor.SetAt(
            i * Parser::kParameterEntrySize + Parser::kParameterIsFinalOffset,
            Bool::Get((flags & Parameter::kIsFinalFlag) != 0));
      }
      found_final = true;
    }
  }
  if (!found_final) {
    for (intptr_t i = 0; i < num_explicit_params; ++i) {
      descriptor.SetAt(
          i * Parser::kParameterEntrySize + Parser::kParameterIsFinalOffset,
          Bool::Get(false));
    }
  }

  // 2. Find metadata implicitly after the function declaration's metadata.
  const Class& klass = Class::Handle(Z, function.Owner());
  const Library& library = Library::Handle(Z, klass.library());
  const Object& metadata = Object::Handle(
      Z, library.GetExtendedMetadata(function, num_explicit_params));
  if (metadata.IsError()) {
    return metadata.ptr();
  }
  if (Array::Cast(metadata).Length() != 0) {
    for (intptr_t i = 0; i < num_explicit_params; i++) {
      result = Array::Cast(metadata).At(i);
      descriptor.SetAt(
          i * Parser::kParameterEntrySize + Parser::kParameterMetadataOffset,
          result);
    }
  }

  // 3. Find the defaultValues in the EntryOptional sequence.
  if (!function.is_abstract()) {
    const Bytecode& bytecode = Bytecode::Handle(Z, function.bytecode());
    ASSERT(!bytecode.IsNull());
    const ObjectPool& constants = ObjectPool::Handle(Z, bytecode.object_pool());
    ASSERT(!constants.IsNull());
    const KBCInstr* instr =
        reinterpret_cast<const KBCInstr*>(bytecode.PayloadStart());
    if (KernelBytecode::IsEntryOptionalOpcode(instr)) {
      // Note that number of fixed parameters may not match 'A' operand of
      // EntryOptional bytecode as [function] could be an implicit closure
      // function with an extra implicit argument, while bytecode corresponds
      // to a static function without any implicit arguments.
      const intptr_t num_fixed_params = function.num_fixed_parameters();
      const intptr_t num_opt_pos_params = KernelBytecode::DecodeB(instr);
      const intptr_t num_opt_named_params = KernelBytecode::DecodeC(instr);
      instr = KernelBytecode::Next(instr);
      ASSERT(num_opt_pos_params == function.NumOptionalPositionalParameters());
      ASSERT(num_opt_named_params == function.NumOptionalNamedParameters());
      ASSERT((num_opt_pos_params == 0) || (num_opt_named_params == 0));

      for (intptr_t i = 0; i < num_opt_pos_params; i++) {
        const KBCInstr* load_value_instr = instr;
        instr = KernelBytecode::Next(instr);
        ASSERT(KernelBytecode::IsLoadConstantOpcode(load_value_instr));
        result = constants.ObjectAt(KernelBytecode::DecodeE(load_value_instr));
        descriptor.SetAt((num_fixed_params - num_implicit_params + i) *
                                 Parser::kParameterEntrySize +
                             Parser::kParameterDefaultValueOffset,
                         result);
      }
      for (intptr_t i = 0; i < num_opt_named_params; i++) {
        const KBCInstr* load_name_instr = instr;
        const KBCInstr* load_value_instr =
            KernelBytecode::Next(load_name_instr);
        instr = KernelBytecode::Next(load_value_instr);
        ASSERT(KernelBytecode::IsLoadConstantOpcode(load_name_instr));
        result = constants.ObjectAt(KernelBytecode::DecodeE(load_name_instr));
        intptr_t param_index;
        for (param_index = num_fixed_params; param_index < num_params;
             param_index++) {
          if (function.ParameterNameAt(param_index) == result.ptr()) {
            break;
          }
        }
        ASSERT(param_index < num_params);
        ASSERT(KernelBytecode::IsLoadConstantOpcode(load_value_instr));
        result = constants.ObjectAt(KernelBytecode::DecodeE(load_value_instr));
        descriptor.SetAt(
            (param_index - num_implicit_params) * Parser::kParameterEntrySize +
                Parser::kParameterDefaultValueOffset,
            result);
      }
    }
  }

  return descriptor.ptr();
}
#if !defined(DART_DYNAMIC_RUNTIME)
void BytecodeReaderHelper::ParseBytecodeFunction(
    ParsedFunction* parsed_function,
    const Function& function) {
  // Handle function kinds which don't have a user-defined body first.
  switch (function.kind()) {
    case UntaggedFunction::kImplicitClosureFunction:
      ParseForwarderFunction(parsed_function, function,
                             Function::Handle(Z, function.parent_function()));
      return;
    case UntaggedFunction::kDynamicInvocationForwarder:
      ParseForwarderFunction(parsed_function, function,
                             Function::Handle(Z, function.ForwardingTarget()));
      return;
    case UntaggedFunction::kImplicitGetter:
    case UntaggedFunction::kImplicitSetter:
    case UntaggedFunction::kMethodExtractor:
      BytecodeScopeBuilder(parsed_function).BuildScopes();
      return;
    case UntaggedFunction::kImplicitStaticGetter: {
      if (IsStaticFieldGetterGeneratedAsInitializer(function, Z)) {
        break;
      } else {
        BytecodeScopeBuilder(parsed_function).BuildScopes();
        return;
      }
    }
    case UntaggedFunction::kRegularFunction:
    case UntaggedFunction::kGetterFunction:
    case UntaggedFunction::kSetterFunction:
    case UntaggedFunction::kClosureFunction:
    case UntaggedFunction::kConstructor:
    case UntaggedFunction::kFieldInitializer:
      break;
    case UntaggedFunction::kNoSuchMethodDispatcher:
    case UntaggedFunction::kInvokeFieldDispatcher:
    case UntaggedFunction::kIrregexpFunction:
    case UntaggedFunction::kFfiTrampoline:
      UNREACHABLE();
      break;
  }

  // We only reach here if function has a bytecode body. Make sure it is
  // loaded and collect information about covariant parameters.

  if (!function.HasBytecode()) {
    ReadCode(function, function.bytecode_offset());
    ASSERT(function.HasBytecode());
  }

  // TODO(alexmarkov): simplify access to covariant / generic_covariant_impl
  //  flags of parameters so we won't need to read them separately.
  if (!parsed_function->HasCovariantParametersInfo()) {
    const intptr_t num_params = function.NumParameters();
    BitVector* covariant_parameters = new (Z) BitVector(Z, num_params);
    BitVector* generic_covariant_impl_parameters =
        new (Z) BitVector(Z, num_params);
    ReadParameterCovariance(function, covariant_parameters,
                            generic_covariant_impl_parameters);
    parsed_function->SetCovariantParameters(covariant_parameters);
    parsed_function->SetGenericCovariantImplParameters(
        generic_covariant_impl_parameters);
  }
}

void BytecodeReaderHelper::ParseForwarderFunction(
    ParsedFunction* parsed_function,
    const Function& function,
    const Function& target) {
  ASSERT(function.IsImplicitClosureFunction() ||
         function.IsDynamicInvocationForwarder());

  ASSERT(target.is_declared_in_bytecode());

  if (function.IsDynamicInvocationForwarder() &&
      target.IsImplicitSetterFunction()) {
    BytecodeScopeBuilder(parsed_function).BuildScopes();
    return;
  }

  if (!target.HasBytecode()) {
    ReadCode(target, target.bytecode_offset());
  }

  BytecodeScopeBuilder(parsed_function).BuildScopes();

  const auto& target_bytecode = Bytecode::Handle(Z, target.bytecode());
  const auto& obj_pool = ObjectPool::Handle(Z, target_bytecode.object_pool());

  AlternativeReadingScope alt(&reader_, target.bytecode_offset());

  const intptr_t flags = reader_.ReadUInt();
  const bool has_parameter_flags = (flags & Code::kHasParameterFlagsFlag) != 0;
  const bool has_forwarding_stub_target =
      (flags & Code::kHasForwardingStubTargetFlag) != 0;
  const bool has_default_function_type_args =
      (flags & Code::kHasDefaultFunctionTypeArgsFlag) != 0;
  const auto proc_attrs = kernel::ProcedureAttributesOf(target, Z);
  // TODO(alexmarkov): fix building of flow graph for implicit closures so
  // it would include missing checks and remove 'proc_attrs.has_tearoff_uses'
  // from this condition.
  const bool body_has_generic_covariant_impl_type_checks =
      proc_attrs.has_non_this_uses || proc_attrs.has_tearoff_uses;

  if (has_parameter_flags) {
    const intptr_t num_params = reader_.ReadUInt();
    const intptr_t num_implicit_params = function.NumImplicitParameters();
    for (intptr_t i = 0; i < num_params; ++i) {
      const intptr_t flags = reader_.ReadUInt();

      bool is_covariant = (flags & Parameter::kIsCovariantFlag) != 0;
      bool is_generic_covariant_impl =
          (flags & Parameter::kIsGenericCovariantImplFlag) != 0;

      LocalVariable* variable =
          parsed_function->ParameterVariable(num_implicit_params + i);

      if (is_covariant) {
        variable->set_is_explicit_covariant_parameter();
      }

      const bool checked_in_method_body =
          is_covariant || (is_generic_covariant_impl &&
                           body_has_generic_covariant_impl_type_checks);

      if (checked_in_method_body) {
        variable->set_type_check_mode(LocalVariable::kSkipTypeCheck);
      } else {
        ASSERT(variable->type_check_mode() == LocalVariable::kDoTypeCheck);
      }
    }
  }

  if (has_forwarding_stub_target) {
    const intptr_t cp_index = reader_.ReadUInt();
    const auto& forwarding_stub_target =
        Function::CheckedZoneHandle(Z, obj_pool.ObjectAt(cp_index));
    parsed_function->MarkForwardingStub(&forwarding_stub_target);
  }

  if (has_default_function_type_args) {
    ASSERT(function.IsGeneric());
    const intptr_t cp_index = reader_.ReadUInt();
    const auto& type_args =
        TypeArguments::CheckedHandle(Z, obj_pool.ObjectAt(cp_index));
    // In bytecode mode, all type parameters are created with a default
    // argument of dynamic, so only need to update if not the all-dynamic TAV.
    if (!type_args.IsNull()) {
      auto& type_params = TypeParameters::Handle(Z, function.type_parameters());
      ASSERT_EQUAL(type_params.Length(), type_args.Length());
      auto& type = AbstractType::Handle(Z);
      for (intptr_t i = 0; i < type_params.Length(); i++) {
        type = type_args.TypeAt(i);
        type_params.SetDefaultAt(i, type);
      }
    }
  }

  if (function.HasOptionalParameters()) {
    const KBCInstr* raw_bytecode =
        reinterpret_cast<const KBCInstr*>(target_bytecode.PayloadStart());
    const KBCInstr* entry = raw_bytecode;
    raw_bytecode = KernelBytecode::Next(raw_bytecode);
    ASSERT(KernelBytecode::IsEntryOptionalOpcode(entry));
    ASSERT(KernelBytecode::DecodeB(entry) ==
           function.NumOptionalPositionalParameters());
    ASSERT(KernelBytecode::DecodeC(entry) ==
           function.NumOptionalNamedParameters());

    const intptr_t num_opt_params = function.NumOptionalParameters();
    ZoneGrowableArray<const Instance*>* default_values =
        new (Z) ZoneGrowableArray<const Instance*>(Z, num_opt_params);

    if (function.HasOptionalPositionalParameters()) {
      for (intptr_t i = 0, n = function.NumOptionalPositionalParameters();
           i < n; ++i) {
        const KBCInstr* load = raw_bytecode;
        raw_bytecode = KernelBytecode::Next(raw_bytecode);
        ASSERT(KernelBytecode::IsLoadConstantOpcode(load));
        const auto& value = Instance::CheckedZoneHandle(
            Z, obj_pool.ObjectAt(KernelBytecode::DecodeE(load)));
        default_values->Add(&value);
      }
    } else {
      const intptr_t num_fixed_params = function.num_fixed_parameters();
      auto& param_name = String::Handle(Z);
      default_values->EnsureLength(num_opt_params, nullptr);
      for (intptr_t i = 0; i < num_opt_params; ++i) {
        const KBCInstr* load_name = raw_bytecode;
        const KBCInstr* load_value = KernelBytecode::Next(load_name);
        raw_bytecode = KernelBytecode::Next(load_value);
        ASSERT(KernelBytecode::IsLoadConstantOpcode(load_name));
        ASSERT(KernelBytecode::IsLoadConstantOpcode(load_value));
        param_name ^= obj_pool.ObjectAt(KernelBytecode::DecodeE(load_name));
        const auto& value = Instance::CheckedZoneHandle(
            Z, obj_pool.ObjectAt(KernelBytecode::DecodeE(load_value)));

        const intptr_t num_params = function.NumParameters();
        intptr_t param_index = num_fixed_params;
        for (; param_index < num_params; ++param_index) {
          if (function.ParameterNameAt(param_index) == param_name.ptr()) {
            break;
          }
        }
        ASSERT(param_index < num_params);
        ASSERT(default_values->At(param_index - num_fixed_params) == nullptr);
        (*default_values)[param_index - num_fixed_params] = &value;
      }
    }

    parsed_function->set_default_parameter_values(default_values);
  }
}
#endif

LibraryPtr BytecodeReaderHelper::ReadMain() {
  return Library::RawCast(ReadObject());
}

intptr_t BytecodeComponentData::GetVersion() const {
  return Smi::Value(Smi::RawCast(data_.At(kVersion)));
}

intptr_t BytecodeComponentData::GetStringsHeaderOffset() const {
  return Smi::Value(Smi::RawCast(data_.At(kStringsHeaderOffset)));
}

intptr_t BytecodeComponentData::GetStringsContentsOffset() const {
  return Smi::Value(Smi::RawCast(data_.At(kStringsContentsOffset)));
}

intptr_t BytecodeComponentData::GetObjectOffsetsOffset() const {
  return Smi::Value(Smi::RawCast(data_.At(kObjectOffsetsOffset)));
}

intptr_t BytecodeComponentData::GetNumObjects() const {
  return Smi::Value(Smi::RawCast(data_.At(kNumObjects)));
}

intptr_t BytecodeComponentData::GetObjectsContentsOffset() const {
  return Smi::Value(Smi::RawCast(data_.At(kObjectsContentsOffset)));
}

intptr_t BytecodeComponentData::GetMainOffset() const {
  return Smi::Value(Smi::RawCast(data_.At(kMainOffset)));
}

intptr_t BytecodeComponentData::GetNumLibraries() const {
  return Smi::Value(Smi::RawCast(data_.At(kNumLibraries)));
}

intptr_t BytecodeComponentData::GetLibraryIndexOffset() const {
  return Smi::Value(Smi::RawCast(data_.At(kLibraryIndexOffset)));
}

intptr_t BytecodeComponentData::GetLibrariesOffset() const {
  return Smi::Value(Smi::RawCast(data_.At(kLibrariesOffset)));
}

intptr_t BytecodeComponentData::GetNumClasses() const {
  return Smi::Value(Smi::RawCast(data_.At(kNumClasses)));
}

intptr_t BytecodeComponentData::GetClassesOffset() const {
  return Smi::Value(Smi::RawCast(data_.At(kClassesOffset)));
}

intptr_t BytecodeComponentData::GetMembersOffset() const {
  return Smi::Value(Smi::RawCast(data_.At(kMembersOffset)));
}

intptr_t BytecodeComponentData::GetNumCodes() const {
  return Smi::Value(Smi::RawCast(data_.At(kNumCodes)));
}

intptr_t BytecodeComponentData::GetCodesOffset() const {
  return Smi::Value(Smi::RawCast(data_.At(kCodesOffset)));
}

intptr_t BytecodeComponentData::GetSourcePositionsOffset() const {
  return Smi::Value(Smi::RawCast(data_.At(kSourcePositionsOffset)));
}

intptr_t BytecodeComponentData::GetSourceFilesOffset() const {
  return Smi::Value(Smi::RawCast(data_.At(kSourceFilesOffset)));
}

intptr_t BytecodeComponentData::GetLineStartsOffset() const {
  return Smi::Value(Smi::RawCast(data_.At(kLineStartsOffset)));
}

intptr_t BytecodeComponentData::GetLocalVariablesOffset() const {
  return Smi::Value(Smi::RawCast(data_.At(kLocalVariablesOffset)));
}

intptr_t BytecodeComponentData::GetAnnotationsOffset() const {
  return Smi::Value(Smi::RawCast(data_.At(kAnnotationsOffset)));
}

void BytecodeComponentData::SetObject(intptr_t index, const Object& obj) const {
  data_.SetAt(kNumFields + index, obj);
}

ObjectPtr BytecodeComponentData::GetObject(intptr_t index) const {
  return data_.At(kNumFields + index);
}

ArrayPtr BytecodeComponentData::New(Zone* zone,
                                    intptr_t version,
                                    intptr_t num_objects,
                                    intptr_t strings_header_offset,
                                    intptr_t strings_contents_offset,
                                    intptr_t object_offsets_offset,
                                    intptr_t objects_contents_offset,
                                    intptr_t main_offset,
                                    intptr_t num_libraries,
                                    intptr_t library_index_offset,
                                    intptr_t libraries_offset,
                                    intptr_t num_classes,
                                    intptr_t classes_offset,
                                    intptr_t members_offset,
                                    intptr_t num_codes,
                                    intptr_t codes_offset,
                                    intptr_t source_positions_offset,
                                    intptr_t source_files_offset,
                                    intptr_t line_starts_offset,
                                    intptr_t local_variables_offset,
                                    intptr_t annotations_offset,
                                    Heap::Space space) {
  const Array& data =
      Array::Handle(zone, Array::New(kNumFields + num_objects, space));
  Smi& smi_handle = Smi::Handle(zone);

  smi_handle = Smi::New(version);
  data.SetAt(kVersion, smi_handle);

  smi_handle = Smi::New(strings_header_offset);
  data.SetAt(kStringsHeaderOffset, smi_handle);

  smi_handle = Smi::New(strings_contents_offset);
  data.SetAt(kStringsContentsOffset, smi_handle);

  smi_handle = Smi::New(object_offsets_offset);
  data.SetAt(kObjectOffsetsOffset, smi_handle);

  smi_handle = Smi::New(num_objects);
  data.SetAt(kNumObjects, smi_handle);

  smi_handle = Smi::New(objects_contents_offset);
  data.SetAt(kObjectsContentsOffset, smi_handle);

  smi_handle = Smi::New(main_offset);
  data.SetAt(kMainOffset, smi_handle);

  smi_handle = Smi::New(num_libraries);
  data.SetAt(kNumLibraries, smi_handle);

  smi_handle = Smi::New(library_index_offset);
  data.SetAt(kLibraryIndexOffset, smi_handle);

  smi_handle = Smi::New(libraries_offset);
  data.SetAt(kLibrariesOffset, smi_handle);

  smi_handle = Smi::New(num_classes);
  data.SetAt(kNumClasses, smi_handle);

  smi_handle = Smi::New(classes_offset);
  data.SetAt(kClassesOffset, smi_handle);

  smi_handle = Smi::New(members_offset);
  data.SetAt(kMembersOffset, smi_handle);

  smi_handle = Smi::New(num_codes);
  data.SetAt(kNumCodes, smi_handle);

  smi_handle = Smi::New(codes_offset);
  data.SetAt(kCodesOffset, smi_handle);

  smi_handle = Smi::New(source_positions_offset);
  data.SetAt(kSourcePositionsOffset, smi_handle);

  smi_handle = Smi::New(source_files_offset);
  data.SetAt(kSourceFilesOffset, smi_handle);

  smi_handle = Smi::New(line_starts_offset);
  data.SetAt(kLineStartsOffset, smi_handle);

  smi_handle = Smi::New(local_variables_offset);
  data.SetAt(kLocalVariablesOffset, smi_handle);

  smi_handle = Smi::New(annotations_offset);
  data.SetAt(kAnnotationsOffset, smi_handle);

  return data.ptr();
}

ErrorPtr BytecodeReader::ReadFunctionBytecode(Thread* thread,
                                              const Function& function) {
  ASSERT(!FLAG_precompiled_mode);
  ASSERT(!function.HasBytecode());
  ASSERT(thread->sticky_error() == Error::null());
  ASSERT(Thread::Current()->IsMutatorThread());

  VMTagScope tagScope(thread, VMTag::kLoadBytecodeTagId);

#if defined(SUPPORT_TIMELINE)
  TimelineBeginEndScope tbes(thread, Timeline::GetCompilerStream(),
                             "BytecodeReader::ReadFunctionBytecode");
  // This increases bytecode reading time by ~7%, so only keep it around for
  // debugging.
#if defined(DEBUG)
  tbes.SetNumArguments(1);
  tbes.CopyArgument(0, "Function", function.ToQualifiedCString());
#endif  // defined(DEBUG)
#endif  // !defined(SUPPORT_TIMELINE)

  LongJumpScope jump;
  if (setjmp(*jump.Set()) == 0) {
#if defined(DART_DYNAMIC_RUNTIME)
    Thread::Current()->isolate()->setIsReadBytecode(true);
#endif
    StackZone stack_zone(thread);
    Zone* const zone = stack_zone.GetZone();
    HANDLESCOPE(thread);

    auto& bytecode = Bytecode::Handle(zone);

    switch (function.kind()) {
      case UntaggedFunction::kImplicitGetter:
        bytecode = Object::implicit_getter_bytecode().ptr();
        break;
      case UntaggedFunction::kImplicitSetter:
        bytecode = Object::implicit_setter_bytecode().ptr();
        break;
      case UntaggedFunction::kImplicitStaticGetter:
        if (!IsStaticFieldGetterGeneratedAsInitializer(function, zone)) {
          bytecode = Object::implicit_static_getter_bytecode().ptr();
        }
        break;
      case UntaggedFunction::kMethodExtractor:
        bytecode = Object::method_extractor_bytecode().ptr();
        break;
      case UntaggedFunction::kInvokeFieldDispatcher:
        if (Class::Handle(zone, function.Owner()).id() == kClosureCid) {
          bytecode = Object::invoke_closure_bytecode().ptr();
        } else {
          bytecode = Object::invoke_field_bytecode().ptr();
        }
        break;
      case UntaggedFunction::kNoSuchMethodDispatcher:
        bytecode = Object::nsm_dispatcher_bytecode().ptr();
        break;
      case UntaggedFunction::kDynamicInvocationForwarder: {
        const Function& target =
            Function::Handle(zone, function.ForwardingTarget());
        if (!target.HasBytecode()) {
          // The forwarder will use the target's bytecode to handle optional
          // parameters.
          const Error& error =
              Error::Handle(zone, ReadFunctionBytecode(thread, target));
          if (!error.IsNull()) {
            return error.ptr();
          }
        }
        {
          const Script& script = Script::Handle(zone, target.script());
          TranslationHelper translation_helper(thread);
          translation_helper.InitFromScript(script);

          ActiveClass active_class;
          BytecodeComponentData bytecode_component(
              &Array::Handle(zone, translation_helper.GetBytecodeComponent()));
          ASSERT(!bytecode_component.IsNull());
          BytecodeReaderHelper bytecode_reader(
              &translation_helper, &active_class, &bytecode_component);

         function.SetForwardingTarget(target);
        }
        bytecode = Object::dynamic_invocation_forwarder_bytecode().ptr();
      } break;
      default:
        break;
    }

    if (!bytecode.IsNull()) {
      function.AttachBytecode(bytecode);
    } else if (function.is_declared_in_bytecode()) {
      const intptr_t code_offset = function.bytecode_offset();
      if (code_offset != 0) {
#if !defined(DART_DYNAMIC_RUNTIME)
        CompilerState compiler_state(thread, FLAG_precompiled_mode, false);
#endif
        const Script& script = Script::Handle(zone, function.script());
        TranslationHelper translation_helper(thread);
        translation_helper.InitFromScript(script);

        ActiveClass active_class;

        // Setup a [ActiveClassScope] and a [ActiveMemberScope] which will be
        // used e.g. for type translation.
        const Class& klass = Class::Handle(zone, function.Owner());
        Function& outermost_function =
            Function::Handle(zone, function.GetOutermostFunction());

        ActiveClassScope active_class_scope(&active_class, &klass);
        ActiveMemberScope active_member(&active_class, &outermost_function);

        BytecodeComponentData bytecode_component(
            &Array::Handle(zone, translation_helper.GetBytecodeComponent()));
        ASSERT(!bytecode_component.IsNull());
        BytecodeReaderHelper bytecode_reader(&translation_helper, &active_class,
                                             &bytecode_component);

        bytecode_reader.ReadCode(function, code_offset);
      }
    }
#if defined(DART_DYNAMIC_RUNTIME)
    Thread::Current()->isolate()->setIsReadBytecode(false);
#endif
    return Error::null();
  } else {
    return thread->StealStickyError();
  }
}

ObjectPtr BytecodeReader::ReadAnnotation(const Field& annotation_field) {
  ASSERT(annotation_field.is_declared_in_bytecode());

  Thread* thread = Thread::Current();
  Zone* zone = thread->zone();
  ASSERT(thread->IsMutatorThread());

  const Script& script = Script::Handle(zone, annotation_field.Script());
  TranslationHelper translation_helper(thread);
  translation_helper.InitFromScript(script);

  ActiveClass active_class;

  BytecodeComponentData bytecode_component(
      &Array::Handle(zone, translation_helper.GetBytecodeComponent()));
  ASSERT(!bytecode_component.IsNull());
  BytecodeReaderHelper bytecode_reader(&translation_helper, &active_class,
                                       &bytecode_component);

  AlternativeReadingScope alt(&bytecode_reader.reader(),
                              annotation_field.bytecode_offset());

  return bytecode_reader.ReadObject();
}

ObjectPtr BytecodeReader::ReadAnnotation2(const Library& library,
                                          intptr_t bytecode_offset) {
  ASSERT(bytecode_offset > 0);

  Thread* thread = Thread::Current();
  Zone* zone = thread->zone();
  ASSERT(thread->IsMutatorThread());

  TranslationHelper translation_helper(thread);

  Script& script = Script::Handle(
          zone, Class::Handle(zone, library.toplevel_class()).script());
  translation_helper.InitFromScript(script);

  ActiveClass active_class;

  BytecodeComponentData bytecode_component(
          &Array::Handle(zone, translation_helper.GetBytecodeComponent()));
  ASSERT(!bytecode_component.IsNull());
  BytecodeReaderHelper bytecode_reader(&translation_helper, &active_class,
                                       &bytecode_component);

  AlternativeReadingScope alt(&bytecode_reader.reader(),
                              bytecode_offset);

  return bytecode_reader.ReadObject();
}

ArrayPtr BytecodeReader::ReadExtendedAnnotations2(const Library& library,
                                                  intptr_t bytecode_offset,
                                                  intptr_t count) {
  ASSERT(bytecode_offset > 0);

  Thread* thread = Thread::Current();
  Zone* zone = thread->zone();
  ASSERT(thread->IsMutatorThread());

  Script& script = Script::Handle(
        zone, Class::Handle(zone, library.toplevel_class()).script());
  TranslationHelper translation_helper(thread);
  translation_helper.InitFromScript(script);

  ActiveClass active_class;

  BytecodeComponentData bytecode_component(
          &Array::Handle(zone, translation_helper.GetBytecodeComponent()));
  ASSERT(!bytecode_component.IsNull());
  BytecodeReaderHelper bytecode_reader(&translation_helper, &active_class,
                                       &bytecode_component);

  AlternativeReadingScope alt(&bytecode_reader.reader(),
                              bytecode_offset);

  bytecode_reader.ReadObject();  // Discard main annotation.

  Array& result = Array::Handle(zone, Array::New(count));
  Object& element = Object::Handle(zone);
  for (intptr_t i = 0; i < count; i++) {
    element = bytecode_reader.ReadObject();
    result.SetAt(i, element);
  }
  return result.ptr();
}

ArrayPtr BytecodeReader::ReadExtendedAnnotations(const Field& annotation_field,
                                                 intptr_t count) {
  ASSERT(annotation_field.is_declared_in_bytecode());

  Thread* thread = Thread::Current();
  Zone* zone = thread->zone();
  ASSERT(thread->IsMutatorThread());

  const Script& script = Script::Handle(zone, annotation_field.Script());
  TranslationHelper translation_helper(thread);
  translation_helper.InitFromScript(script);

  ActiveClass active_class;

  BytecodeComponentData bytecode_component(
      &Array::Handle(zone, translation_helper.GetBytecodeComponent()));
  ASSERT(!bytecode_component.IsNull());
  BytecodeReaderHelper bytecode_reader(&translation_helper, &active_class,
                                       &bytecode_component);

  AlternativeReadingScope alt(&bytecode_reader.reader(),
                              annotation_field.bytecode_offset());

  bytecode_reader.ReadObject();  // Discard main annotation.

  Array& result = Array::Handle(zone, Array::New(count));
  Object& element = Object::Handle(zone);
  for (intptr_t i = 0; i < count; i++) {
    element = bytecode_reader.ReadObject();
    result.SetAt(i, element);
  }
  return result.ptr();
}

void BytecodeReader::ResetObjectTable(const KernelProgramInfo& info) {
  Thread* thread = Thread::Current();
  TranslationHelper translation_helper(thread);
  translation_helper.InitFromKernelProgramInfo(info);
  ActiveClass active_class;
  BytecodeComponentData bytecode_component(&Array::Handle(
      thread->zone(), translation_helper.GetBytecodeComponent()));
  ASSERT(!bytecode_component.IsNull());
  BytecodeReaderHelper bytecode_reader(&translation_helper, &active_class,
                                       &bytecode_component);
  bytecode_reader.ResetObjects();
}

void BytecodeReader::LoadClassDeclaration(const Class& cls) {
  TIMELINE_DURATION(Thread::Current(), Compiler,
                    "BytecodeReader::LoadClassDeclaration");

  ASSERT(cls.is_declared_in_bytecode());
  ASSERT(!cls.is_declaration_loaded());

  Thread* thread = Thread::Current();
  Zone* zone = thread->zone();
  ASSERT(thread->IsMutatorThread());

  const Script& script = Script::Handle(zone, cls.script());
  TranslationHelper translation_helper(thread);
  translation_helper.InitFromScript(script);

  ActiveClass active_class;
  ActiveClassScope active_class_scope(&active_class, &cls);

  BytecodeComponentData bytecode_component(
      &Array::Handle(zone, translation_helper.GetBytecodeComponent()));
  ASSERT(!bytecode_component.IsNull());
  BytecodeReaderHelper bytecode_reader(&translation_helper, &active_class,
                                       &bytecode_component);

  AlternativeReadingScope alt(&bytecode_reader.reader(), cls.bytecode_offset());

  bytecode_reader.ReadClassDeclaration(cls);
}

void BytecodeReader::FinishClassLoading(const Class& cls) {
  ASSERT(cls.is_declared_in_bytecode());

  Thread* thread = Thread::Current();
  Zone* zone = thread->zone();
  ASSERT(thread->IsMutatorThread());

  const Script& script = Script::Handle(zone, cls.script());
  TranslationHelper translation_helper(thread);
  translation_helper.InitFromScript(script);

  ActiveClass active_class;
  ActiveClassScope active_class_scope(&active_class, &cls);

  BytecodeComponentData bytecode_component(
      &Array::Handle(zone, translation_helper.GetBytecodeComponent()));
  ASSERT(!bytecode_component.IsNull());
  BytecodeReaderHelper bytecode_reader(&translation_helper, &active_class,
                                       &bytecode_component);

  AlternativeReadingScope alt(&bytecode_reader.reader(), cls.bytecode_offset());

  // If this is a dart:internal.ClassID class ignore field declarations
  // contained in the Kernel file and instead inject our own const
  // fields.
  const bool discard_fields = cls.InjectCIDFields();

  bytecode_reader.ReadMembers(cls, discard_fields);
}

ObjectPtr BytecodeReader::GetBytecodeAttribute(const Object& key,
                                               const String& name) {
  Thread* thread = Thread::Current();
  Zone* zone = thread->zone();
  const auto* object_store = thread->isolate()->group()->object_store();
  if (object_store->bytecode_attributes() == Object::null()) {
    return Object::null();
  }
  BytecodeAttributesMap map(object_store->bytecode_attributes());
  const auto& attrs = Array::CheckedHandle(zone, map.GetOrNull(key));
  ASSERT(map.Release().ptr() == object_store->bytecode_attributes());
  if (attrs.IsNull()) {
    return Object::null();
  }
  auto& obj = Object::Handle(zone);
  for (intptr_t i = 0, n = attrs.Length(); i + 1 < n; i += 2) {
    obj = attrs.At(i);
    if (obj.ptr() == name.ptr()) {
      return attrs.At(i + 1);
    }
  }
  return Object::null();
}

InferredTypeMetadata InferredTypeBytecodeAttribute::GetInferredTypeAt(
    Zone* zone,
    const Array& attr,
    intptr_t index) {
  ASSERT(index + kNumElements <= attr.Length());
  const auto& type = AbstractType::CheckedHandle(zone, attr.At(index + 1));
  const intptr_t flags = Smi::Value(Smi::RawCast(attr.At(index + 2)));
  if (!type.IsNull()) {
    intptr_t cid = Type::Cast(type).type_class_id();
    return InferredTypeMetadata(cid, flags);
  } else {
    return InferredTypeMetadata(kDynamicCid, flags);
  }
}

#if !defined(PRODUCT)
LocalVarDescriptorsPtr BytecodeReader::ComputeLocalVarDescriptors(
    Zone* zone,
    const Function& function,
    const Bytecode& bytecode) {
  ASSERT(function.is_declared_in_bytecode());
  ASSERT(function.HasBytecode());
  ASSERT(!bytecode.IsNull());
  ASSERT(function.bytecode() == bytecode.ptr());

  LocalVarDescriptorsBuilder vars;

  if (function.IsLocalFunction()) {
    const auto& parent = Function::Handle(zone, function.parent_function());
    ASSERT(parent.is_declared_in_bytecode() && parent.HasBytecode());
    const auto& parent_bytecode = Bytecode::Handle(zone, parent.bytecode());
    const auto& parent_vars = LocalVarDescriptors::Handle(
        zone, parent_bytecode.GetLocalVarDescriptors());
    for (intptr_t i = 0; i < parent_vars.Length(); ++i) {
      UntaggedLocalVarDescriptors::VarInfo var_info;
      parent_vars.GetInfo(i, &var_info);
      // Include parent's context variable if variable's scope
      // intersects with the local function range.
      // It is not enough to check if local function is declared within the
      // scope of variable, because in case of async functions closure has
      // the same range as original function.
      if (var_info.kind() == UntaggedLocalVarDescriptors::kContextVar &&
          ((var_info.begin_pos <= function.token_pos() &&
            function.token_pos() <= var_info.end_pos) ||
           (function.token_pos() <= var_info.begin_pos &&
            var_info.begin_pos <= function.end_token_pos()))) {
        vars.Add(LocalVarDescriptorsBuilder::VarDesc{
            &String::Handle(zone, parent_vars.GetName(i)), var_info});
      }
    }
  }

  if (bytecode.HasLocalVariablesInfo()) {
    intptr_t scope_id = 0;
    intptr_t context_level = -1;
    BytecodeLocalVariablesIterator local_vars(zone, bytecode);
    while (local_vars.MoveNext()) {
      switch (local_vars.Kind()) {
        case BytecodeLocalVariablesIterator::kScope: {
          ++scope_id;
          context_level = local_vars.ContextLevel();
        } break;
        case BytecodeLocalVariablesIterator::kVariableDeclaration: {
          LocalVarDescriptorsBuilder::VarDesc desc;
          desc.name = &String::Handle(zone, local_vars.Name());
          if (local_vars.IsCaptured()) {
            desc.info.set_kind(UntaggedLocalVarDescriptors::kContextVar);
            desc.info.scope_id = context_level;
            desc.info.set_index(local_vars.Index());
          } else {
            desc.info.set_kind(UntaggedLocalVarDescriptors::kStackVar);
            desc.info.scope_id = scope_id;
            if (local_vars.Index() < 0) {
              // Parameter
              ASSERT(local_vars.Index() < -kKBCParamEndSlotFromFp);
              desc.info.set_index(-local_vars.Index() - kKBCParamEndSlotFromFp);
            } else {
              desc.info.set_index(-local_vars.Index());
            }
          }
          desc.info.declaration_pos = local_vars.DeclarationTokenPos();
          desc.info.begin_pos = local_vars.StartTokenPos();
          desc.info.end_pos = local_vars.EndTokenPos();
          vars.Add(desc);
        } break;
        case BytecodeLocalVariablesIterator::kContextVariable: {
          ASSERT(local_vars.Index() >= 0);
          const intptr_t context_variable_index = -local_vars.Index();
          LocalVarDescriptorsBuilder::VarDesc desc;
          desc.name = &Symbols::CurrentContextVar();
          desc.info.set_kind(UntaggedLocalVarDescriptors::kSavedCurrentContext);
          desc.info.scope_id = 0;
          desc.info.declaration_pos = TokenPosition::kMinSource;
          desc.info.begin_pos = TokenPosition::kMinSource;
          desc.info.end_pos = TokenPosition::kMinSource;
          desc.info.set_index(context_variable_index);
          vars.Add(desc);
        } break;
      }
    }
  }

  return vars.Done();
}
#endif  // !defined(PRODUCT)

bool IsStaticFieldGetterGeneratedAsInitializer(const Function& function,
                                               Zone* zone) {
  ASSERT(function.kind() == UntaggedFunction::kImplicitStaticGetter);

  const auto& field = Field::Handle(zone, function.accessor_field());
  return field.is_declared_in_bytecode() && field.is_const() &&
         field.has_nontrivial_initializer();
}

}  // namespace kernel
}  // namespace dart

#endif  // !defined(DART_PRECOMPILED_RUNTIME)
