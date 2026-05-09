use std::collections::{HashMap, HashSet};
use std::fmt;

use cranelift_codegen::ir::{self, AbiParam, InstBuilder, types};
use cranelift_codegen::settings;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use yulang_core_ir as core_ir;

use crate::abi::{NativeAbiBlock, NativeAbiFunction, NativeAbiModule, NativeAbiStmt};
use crate::abi_subset::{NativeAbiSubsetError, validate_cranelift_prototype_subset};
use crate::abi_validate::{NativeAbiValidateError, validate_abi_module};
use crate::control_ir::{BlockId, NativeLiteral, NativeTerminator, ValueId};

pub type NativeCraneliftResult<T> = Result<T, NativeCraneliftError>;

#[derive(Debug)]
pub enum NativeCraneliftError {
    AbiInvalid(NativeAbiValidateError),
    UnsupportedSubset(NativeAbiSubsetError),
    UnsupportedScalarLiteral {
        function: String,
        literal: NativeLiteral,
    },
    UnsupportedScalarPrimitive {
        function: String,
        op: core_ir::PrimitiveOp,
    },
    UnsupportedStmt {
        function: String,
        kind: &'static str,
    },
    UnsupportedEnvironment {
        function: String,
        slots: usize,
    },
    UnsupportedClosureValue {
        function: String,
        value: ValueId,
    },
    UnsupportedDirectEnvironmentCall {
        function: String,
        target: String,
        slots: usize,
    },
    MissingFunction {
        name: String,
    },
    MissingBlock {
        function: String,
        block: BlockId,
    },
    MissingValue {
        function: String,
        value: ValueId,
    },
    InvalidReturnArity {
        function: String,
        arity: usize,
    },
    Cranelift(String),
}

impl fmt::Display for NativeCraneliftError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeCraneliftError::AbiInvalid(error) => write!(f, "{error}"),
            NativeCraneliftError::UnsupportedSubset(error) => write!(f, "{error}"),
            NativeCraneliftError::UnsupportedScalarLiteral { function, literal } => write!(
                f,
                "native Cranelift scalar prototype does not support literal {literal:?} in `{function}`"
            ),
            NativeCraneliftError::UnsupportedScalarPrimitive { function, op } => write!(
                f,
                "native Cranelift scalar prototype does not support primitive {op:?} in `{function}`"
            ),
            NativeCraneliftError::UnsupportedStmt { function, kind } => write!(
                f,
                "native Cranelift scalar prototype does not support {kind} in `{function}`"
            ),
            NativeCraneliftError::UnsupportedEnvironment { function, slots } => write!(
                f,
                "native Cranelift scalar prototype does not support environment for `{function}` ({slots} slots)"
            ),
            NativeCraneliftError::UnsupportedClosureValue { function, value } => write!(
                f,
                "native Cranelift scalar prototype cannot use closure value {value:?} as a scalar in `{function}`"
            ),
            NativeCraneliftError::UnsupportedDirectEnvironmentCall {
                function,
                target,
                slots,
            } => write!(
                f,
                "native Cranelift scalar prototype cannot directly call `{target}` with {slots} environment slots from `{function}`"
            ),
            NativeCraneliftError::MissingFunction { name } => {
                write!(f, "native Cranelift function `{name}` is missing")
            }
            NativeCraneliftError::MissingBlock { function, block } => {
                write!(
                    f,
                    "native Cranelift block {block:?} is missing in `{function}`"
                )
            }
            NativeCraneliftError::MissingValue { function, value } => {
                write!(
                    f,
                    "native Cranelift value {value:?} is missing in `{function}`"
                )
            }
            NativeCraneliftError::InvalidReturnArity { function, arity } => {
                write!(
                    f,
                    "native Cranelift function `{function}` has {arity} return values"
                )
            }
            NativeCraneliftError::Cranelift(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for NativeCraneliftError {}

impl From<NativeAbiValidateError> for NativeCraneliftError {
    fn from(error: NativeAbiValidateError) -> Self {
        NativeCraneliftError::AbiInvalid(error)
    }
}

impl From<NativeAbiSubsetError> for NativeCraneliftError {
    fn from(error: NativeAbiSubsetError) -> Self {
        NativeCraneliftError::UnsupportedSubset(error)
    }
}

pub struct NativeJitModule {
    module: JITModule,
    roots: Vec<FuncId>,
}

impl NativeJitModule {
    pub fn run_roots_i64(&mut self) -> NativeCraneliftResult<Vec<i64>> {
        self.module
            .finalize_definitions()
            .map_err(cranelift_error)?;
        self.roots
            .iter()
            .map(|root| {
                let ptr = self.module.get_finalized_function(*root);
                let call = unsafe { std::mem::transmute::<_, extern "C" fn() -> i64>(ptr) };
                Ok(call())
            })
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeObjectModule {
    bytes: Vec<u8>,
}

impl NativeObjectModule {
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }
}

pub fn compile_abi_module(module: &NativeAbiModule) -> NativeCraneliftResult<NativeJitModule> {
    validate_abi_module(module)?;
    validate_cranelift_prototype_subset(module)?;
    let reachable = reachable_function_names(module);
    validate_scalar_subset(module, &reachable)?;

    let builder =
        JITBuilder::new(cranelift_module::default_libcall_names()).map_err(cranelift_error)?;
    let mut jit = JITModule::new(builder);

    let signatures =
        FunctionSignatures::new(declare_functions(&mut jit, module, &reachable)?, module);
    define_functions(&mut jit, module, &reachable, &signatures)?;
    let roots = module
        .roots
        .iter()
        .map(|root| {
            signatures.ids.get(&root.name).copied().ok_or_else(|| {
                NativeCraneliftError::MissingFunction {
                    name: root.name.clone(),
                }
            })
        })
        .collect::<NativeCraneliftResult<Vec<_>>>()?;
    Ok(NativeJitModule { module: jit, roots })
}

pub fn compile_abi_module_to_object(
    module: &NativeAbiModule,
) -> NativeCraneliftResult<NativeObjectModule> {
    validate_abi_module(module)?;
    validate_cranelift_prototype_subset(module)?;
    let reachable = reachable_function_names(module);
    validate_scalar_subset(module, &reachable)?;

    let isa_builder = cranelift_native::builder().map_err(cranelift_error)?;
    let flags = settings::Flags::new(settings::builder());
    let isa = isa_builder.finish(flags).map_err(cranelift_error)?;
    let builder = ObjectBuilder::new(
        isa,
        "yulang_native_object".to_string(),
        cranelift_module::default_libcall_names(),
    )
    .map_err(cranelift_error)?;
    let mut object = ObjectModule::new(builder);

    let signatures =
        FunctionSignatures::new(declare_functions(&mut object, module, &reachable)?, module);
    define_functions(&mut object, module, &reachable, &signatures)?;
    let product = object.finish();
    let bytes = product.emit().map_err(cranelift_error)?;
    Ok(NativeObjectModule { bytes })
}

fn declare_functions<M: Module>(
    module_backend: &mut M,
    module: &NativeAbiModule,
    reachable: &HashSet<String>,
) -> NativeCraneliftResult<HashMap<String, FuncId>> {
    let mut declared = HashMap::new();
    for function in reachable_functions(module, reachable) {
        let sig = function_signature(module_backend, function);
        let id = module_backend
            .declare_function(&function.name, Linkage::Export, &sig)
            .map_err(cranelift_error)?;
        declared.insert(function.name.clone(), id);
    }
    Ok(declared)
}

fn define_functions<M: Module>(
    module_backend: &mut M,
    module: &NativeAbiModule,
    reachable: &HashSet<String>,
    signatures: &FunctionSignatures<'_>,
) -> NativeCraneliftResult<()> {
    for function in reachable_functions(module, reachable) {
        let func_id = signatures.ids.get(&function.name).copied().ok_or_else(|| {
            NativeCraneliftError::MissingFunction {
                name: function.name.clone(),
            }
        })?;
        let mut ctx = module_backend.make_context();
        ctx.func.signature = function_signature(module_backend, function);
        lower_function(module_backend, &mut ctx, function, signatures)?;
        module_backend
            .define_function(func_id, &mut ctx)
            .map_err(cranelift_error)?;
        module_backend.clear_context(&mut ctx);
    }
    Ok(())
}

fn function_signature<M: Module>(
    module_backend: &M,
    function: &NativeAbiFunction,
) -> ir::Signature {
    let mut sig = module_backend.make_signature();
    sig.params
        .extend((0..function.environment_slots).map(|_| AbiParam::new(types::I64)));
    sig.params
        .extend(function.params.iter().map(|_| AbiParam::new(types::I64)));
    sig.returns.push(AbiParam::new(types::I64));
    sig
}

fn lower_function<M: Module>(
    module_backend: &mut M,
    ctx: &mut cranelift_codegen::Context,
    function: &NativeAbiFunction,
    signatures: &FunctionSignatures<'_>,
) -> NativeCraneliftResult<()> {
    let mut builder_context = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_context);
    let blocks = create_blocks(&mut builder, function);
    declare_variables(&mut builder, function);
    let env_params = bind_function_params(&mut builder, function, &blocks)?;
    let mut state = FunctionLowering::new(function, signatures, env_params);

    for block in &function.blocks {
        let clif_block = block_ref(function, &blocks, block.id)?;
        builder.switch_to_block(clif_block);
        bind_block_params(&mut builder, function, block, clif_block)?;
        for stmt in &block.stmts {
            lower_stmt(module_backend, &mut builder, stmt, &mut state)?;
        }
        lower_terminator(&mut builder, &state, &blocks, &block.terminator)?;
    }
    builder.seal_all_blocks();
    builder.finalize();
    Ok(())
}

fn create_blocks(
    builder: &mut FunctionBuilder<'_>,
    function: &NativeAbiFunction,
) -> HashMap<BlockId, ir::Block> {
    let entry = function.blocks.first().map(|block| block.id);
    function
        .blocks
        .iter()
        .map(|block| {
            let clif_block = builder.create_block();
            let params = if Some(block.id) == entry && block.params.starts_with(&function.params) {
                &block.params[function.params.len()..]
            } else {
                block.params.as_slice()
            };
            for _ in params {
                builder.append_block_param(clif_block, types::I64);
            }
            (block.id, clif_block)
        })
        .collect()
}

fn declare_variables(builder: &mut FunctionBuilder<'_>, function: &NativeAbiFunction) {
    let mut values = HashSet::new();
    for value in function_value_ids(function) {
        if values.insert(value) {
            builder.declare_var(variable(value), types::I64);
        }
    }
}

fn bind_function_params(
    builder: &mut FunctionBuilder<'_>,
    function: &NativeAbiFunction,
    blocks: &HashMap<BlockId, ir::Block>,
) -> NativeCraneliftResult<Vec<ir::Value>> {
    let entry = function
        .blocks
        .first()
        .ok_or_else(|| NativeCraneliftError::MissingBlock {
            function: function.name.clone(),
            block: BlockId(0),
        })?;
    let entry_block = block_ref(function, blocks, entry.id)?;
    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);
    let block_params = builder.block_params(entry_block).to_vec();
    let env_params = block_params
        .iter()
        .take(function.environment_slots)
        .copied()
        .collect::<Vec<_>>();
    for (param, value) in function.params.iter().zip(
        block_params
            .iter()
            .skip(function.environment_slots)
            .take(function.params.len())
            .copied()
            .collect::<Vec<_>>(),
    ) {
        builder.def_var(variable(*param), value);
    }
    Ok(env_params)
}

fn bind_block_params(
    builder: &mut FunctionBuilder<'_>,
    function: &NativeAbiFunction,
    block: &NativeAbiBlock,
    clif_block: ir::Block,
) -> NativeCraneliftResult<()> {
    let clif_params = builder.block_params(clif_block).to_vec();
    let offset = if function
        .blocks
        .first()
        .is_some_and(|entry| entry.id == block.id)
    {
        function.environment_slots + function.params.len()
    } else {
        0
    };
    for (param, value) in block
        .params
        .iter()
        .zip(clif_params.into_iter().skip(offset))
    {
        builder.def_var(variable(*param), value);
    }
    Ok(())
}

fn lower_stmt<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    stmt: &NativeAbiStmt,
    state: &mut FunctionLowering<'_>,
) -> NativeCraneliftResult<()> {
    match stmt {
        NativeAbiStmt::Literal { dest, literal } => {
            let value = lower_literal(builder, state.function, literal)?;
            builder.def_var(variable(*dest), value);
        }
        NativeAbiStmt::Primitive { dest, op, args } => {
            let args = read_values(builder, state, args)?;
            let value = lower_primitive(builder, state.function, *op, &args)?;
            builder.def_var(variable(*dest), value);
        }
        NativeAbiStmt::DirectCall { dest, target, args } => {
            let target_function = state.signatures.function(target)?;
            if target_function.environment_slots != 0 {
                return Err(NativeCraneliftError::UnsupportedDirectEnvironmentCall {
                    function: state.function.name.clone(),
                    target: target.clone(),
                    slots: target_function.environment_slots,
                });
            }
            let func_id = state.signatures.ids.get(target).copied().ok_or_else(|| {
                NativeCraneliftError::MissingFunction {
                    name: target.clone(),
                }
            })?;
            let callee = module_backend.declare_func_in_func(func_id, builder.func);
            let args = read_values(builder, state, args)?;
            let call = builder.ins().call(callee, &args);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(NativeCraneliftError::InvalidReturnArity {
                    function: target.clone(),
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
        }
        NativeAbiStmt::Tuple { .. }
        | NativeAbiStmt::Record { .. }
        | NativeAbiStmt::Variant { .. }
        | NativeAbiStmt::Select { .. } => {
            return Err(NativeCraneliftError::UnsupportedStmt {
                function: state.function.name.clone(),
                kind: "value-lane structural stmt",
            });
        }
        NativeAbiStmt::LoadEnv { dest, slot } => {
            let value = state.env_params.get(*slot).copied().ok_or_else(|| {
                NativeCraneliftError::UnsupportedEnvironment {
                    function: state.function.name.clone(),
                    slots: state.function.environment_slots,
                }
            })?;
            builder.def_var(variable(*dest), value);
        }
        NativeAbiStmt::AllocateClosure {
            dest,
            target,
            environment,
        } => {
            state.closures.insert(
                *dest,
                ClosureAllocation {
                    target: target.clone(),
                    environment: environment.clone(),
                },
            );
        }
        NativeAbiStmt::IndirectClosureCall { dest, callee, args } => {
            let closure = state.closures.get(callee).cloned().ok_or_else(|| {
                NativeCraneliftError::UnsupportedClosureValue {
                    function: state.function.name.clone(),
                    value: *callee,
                }
            })?;
            let func_id = state
                .signatures
                .ids
                .get(&closure.target)
                .copied()
                .ok_or_else(|| NativeCraneliftError::MissingFunction {
                    name: closure.target.clone(),
                })?;
            let callee = module_backend.declare_func_in_func(func_id, builder.func);
            let env_args = read_values(builder, state, &closure.environment)?;
            let value_args = read_values(builder, state, args)?;
            let call_args = env_args.into_iter().chain(value_args).collect::<Vec<_>>();
            let call = builder.ins().call(callee, &call_args);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(NativeCraneliftError::InvalidReturnArity {
                    function: closure.target,
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
        }
    }
    Ok(())
}

fn lower_terminator(
    builder: &mut FunctionBuilder<'_>,
    state: &FunctionLowering<'_>,
    blocks: &HashMap<BlockId, ir::Block>,
    terminator: &NativeTerminator,
) -> NativeCraneliftResult<()> {
    match terminator {
        NativeTerminator::Return(value) => {
            let value = read_value(builder, state, *value)?;
            builder.ins().return_(&[value]);
        }
        NativeTerminator::Jump { target, args } => {
            let target = block_ref(state.function, blocks, *target)?;
            let args = read_block_args(builder, state, args)?;
            builder.ins().jump(target, &args);
        }
        NativeTerminator::Branch {
            cond,
            then_block,
            else_block,
        } => {
            let cond = read_value(builder, state, *cond)?;
            let cond = builder
                .ins()
                .icmp_imm(ir::condcodes::IntCC::NotEqual, cond, 0);
            let then_block = block_ref(state.function, blocks, *then_block)?;
            let else_block = block_ref(state.function, blocks, *else_block)?;
            builder.ins().brif(cond, then_block, &[], else_block, &[]);
        }
    }
    Ok(())
}

fn lower_literal(
    builder: &mut FunctionBuilder<'_>,
    function: &NativeAbiFunction,
    literal: &NativeLiteral,
) -> NativeCraneliftResult<ir::Value> {
    match literal {
        NativeLiteral::Int(value) => {
            let value = value.parse::<i64>().map_err(|_| {
                NativeCraneliftError::UnsupportedScalarLiteral {
                    function: function.name.clone(),
                    literal: literal.clone(),
                }
            })?;
            Ok(builder.ins().iconst(types::I64, value))
        }
        NativeLiteral::Bool(value) => Ok(builder.ins().iconst(types::I64, i64::from(*value))),
        NativeLiteral::Unit => Ok(builder.ins().iconst(types::I64, 0)),
        NativeLiteral::Float(_) | NativeLiteral::String(_) => {
            Err(NativeCraneliftError::UnsupportedScalarLiteral {
                function: function.name.clone(),
                literal: literal.clone(),
            })
        }
    }
}

fn lower_primitive(
    builder: &mut FunctionBuilder<'_>,
    function: &NativeAbiFunction,
    op: core_ir::PrimitiveOp,
    args: &[ir::Value],
) -> NativeCraneliftResult<ir::Value> {
    let value = match op {
        core_ir::PrimitiveOp::BoolNot => {
            let zero = builder.ins().iconst(types::I64, 0);
            let is_zero = builder
                .ins()
                .icmp(ir::condcodes::IntCC::Equal, args[0], zero);
            builder.ins().uextend(types::I64, is_zero)
        }
        core_ir::PrimitiveOp::BoolEq | core_ir::PrimitiveOp::IntEq => {
            let eq = builder
                .ins()
                .icmp(ir::condcodes::IntCC::Equal, args[0], args[1]);
            builder.ins().uextend(types::I64, eq)
        }
        core_ir::PrimitiveOp::IntAdd => builder.ins().iadd(args[0], args[1]),
        core_ir::PrimitiveOp::IntSub => builder.ins().isub(args[0], args[1]),
        core_ir::PrimitiveOp::IntMul => builder.ins().imul(args[0], args[1]),
        core_ir::PrimitiveOp::IntDiv => builder.ins().sdiv(args[0], args[1]),
        core_ir::PrimitiveOp::IntLt => int_cmp(builder, ir::condcodes::IntCC::SignedLessThan, args),
        core_ir::PrimitiveOp::IntLe => {
            int_cmp(builder, ir::condcodes::IntCC::SignedLessThanOrEqual, args)
        }
        core_ir::PrimitiveOp::IntGt => {
            int_cmp(builder, ir::condcodes::IntCC::SignedGreaterThan, args)
        }
        core_ir::PrimitiveOp::IntGe => int_cmp(
            builder,
            ir::condcodes::IntCC::SignedGreaterThanOrEqual,
            args,
        ),
        _ => {
            return Err(NativeCraneliftError::UnsupportedScalarPrimitive {
                function: function.name.clone(),
                op,
            });
        }
    };
    Ok(value)
}

fn int_cmp(
    builder: &mut FunctionBuilder<'_>,
    code: ir::condcodes::IntCC,
    args: &[ir::Value],
) -> ir::Value {
    let cmp = builder.ins().icmp(code, args[0], args[1]);
    builder.ins().uextend(types::I64, cmp)
}

fn read_values(
    builder: &mut FunctionBuilder<'_>,
    state: &FunctionLowering<'_>,
    values: &[ValueId],
) -> NativeCraneliftResult<Vec<ir::Value>> {
    values
        .iter()
        .map(|value| read_value(builder, state, *value))
        .collect()
}

fn read_value(
    builder: &mut FunctionBuilder<'_>,
    state: &FunctionLowering<'_>,
    value: ValueId,
) -> NativeCraneliftResult<ir::Value> {
    if state.closures.contains_key(&value) {
        return Err(NativeCraneliftError::UnsupportedClosureValue {
            function: state.function.name.clone(),
            value,
        });
    }
    Ok(builder.use_var(variable(value)))
}

fn read_block_args(
    builder: &mut FunctionBuilder<'_>,
    state: &FunctionLowering<'_>,
    values: &[ValueId],
) -> NativeCraneliftResult<Vec<ir::BlockArg>> {
    Ok(read_values(builder, state, values)?
        .into_iter()
        .map(ir::BlockArg::Value)
        .collect())
}

fn validate_scalar_subset(
    module: &NativeAbiModule,
    reachable: &HashSet<String>,
) -> NativeCraneliftResult<()> {
    for function in reachable_functions(module, reachable) {
        for block in &function.blocks {
            for stmt in &block.stmts {
                validate_scalar_stmt(function, stmt)?;
            }
        }
    }
    Ok(())
}

fn reachable_functions<'a>(
    module: &'a NativeAbiModule,
    reachable: &HashSet<String>,
) -> Vec<&'a NativeAbiFunction> {
    module
        .functions
        .iter()
        .chain(&module.roots)
        .filter(|function| reachable.contains(&function.name))
        .collect()
}

fn reachable_function_names(module: &NativeAbiModule) -> HashSet<String> {
    let functions = module
        .functions
        .iter()
        .chain(&module.roots)
        .map(|function| (function.name.clone(), function))
        .collect::<HashMap<_, _>>();
    let mut reachable = module
        .roots
        .iter()
        .map(|function| function.name.clone())
        .collect::<HashSet<_>>();
    let mut stack = reachable.iter().cloned().collect::<Vec<_>>();
    while let Some(name) = stack.pop() {
        let Some(function) = functions.get(&name) else {
            continue;
        };
        for target in function_call_targets(function) {
            if reachable.insert(target.clone()) {
                stack.push(target);
            }
        }
    }
    reachable
}

fn function_call_targets(function: &NativeAbiFunction) -> Vec<String> {
    let mut targets = Vec::new();
    for block in &function.blocks {
        for stmt in &block.stmts {
            match stmt {
                NativeAbiStmt::DirectCall { target, .. }
                | NativeAbiStmt::AllocateClosure { target, .. } => targets.push(target.clone()),
                NativeAbiStmt::Literal { .. }
                | NativeAbiStmt::Primitive { .. }
                | NativeAbiStmt::Tuple { .. }
                | NativeAbiStmt::Record { .. }
                | NativeAbiStmt::Variant { .. }
                | NativeAbiStmt::Select { .. }
                | NativeAbiStmt::LoadEnv { .. }
                | NativeAbiStmt::IndirectClosureCall { .. } => {}
            }
        }
    }
    targets
}

fn validate_scalar_stmt(
    function: &NativeAbiFunction,
    stmt: &NativeAbiStmt,
) -> NativeCraneliftResult<()> {
    match stmt {
        NativeAbiStmt::Literal { literal, .. } => match literal {
            NativeLiteral::Int(_) | NativeLiteral::Bool(_) | NativeLiteral::Unit => Ok(()),
            NativeLiteral::Float(_) | NativeLiteral::String(_) => {
                Err(NativeCraneliftError::UnsupportedScalarLiteral {
                    function: function.name.clone(),
                    literal: literal.clone(),
                })
            }
        },
        NativeAbiStmt::Primitive { op, .. } => match op {
            core_ir::PrimitiveOp::BoolNot
            | core_ir::PrimitiveOp::BoolEq
            | core_ir::PrimitiveOp::IntAdd
            | core_ir::PrimitiveOp::IntSub
            | core_ir::PrimitiveOp::IntMul
            | core_ir::PrimitiveOp::IntDiv
            | core_ir::PrimitiveOp::IntEq
            | core_ir::PrimitiveOp::IntLt
            | core_ir::PrimitiveOp::IntLe
            | core_ir::PrimitiveOp::IntGt
            | core_ir::PrimitiveOp::IntGe => Ok(()),
            _ => Err(NativeCraneliftError::UnsupportedScalarPrimitive {
                function: function.name.clone(),
                op: *op,
            }),
        },
        NativeAbiStmt::DirectCall { .. } => Ok(()),
        NativeAbiStmt::Tuple { .. }
        | NativeAbiStmt::Record { .. }
        | NativeAbiStmt::Variant { .. }
        | NativeAbiStmt::Select { .. } => Err(NativeCraneliftError::UnsupportedStmt {
            function: function.name.clone(),
            kind: "value-lane structural stmt",
        }),
        NativeAbiStmt::LoadEnv { .. }
        | NativeAbiStmt::AllocateClosure { .. }
        | NativeAbiStmt::IndirectClosureCall { .. } => Ok(()),
    }
}

struct FunctionSignatures<'a> {
    ids: HashMap<String, FuncId>,
    functions: HashMap<String, &'a NativeAbiFunction>,
}

impl<'a> FunctionSignatures<'a> {
    fn new(ids: HashMap<String, FuncId>, module: &'a NativeAbiModule) -> Self {
        let functions = module
            .functions
            .iter()
            .chain(&module.roots)
            .map(|function| (function.name.clone(), function))
            .collect();
        Self { ids, functions }
    }

    fn function(&self, name: &str) -> NativeCraneliftResult<&'a NativeAbiFunction> {
        self.functions
            .get(name)
            .copied()
            .ok_or_else(|| NativeCraneliftError::MissingFunction {
                name: name.to_string(),
            })
    }
}

struct FunctionLowering<'a> {
    function: &'a NativeAbiFunction,
    signatures: &'a FunctionSignatures<'a>,
    env_params: Vec<ir::Value>,
    closures: HashMap<ValueId, ClosureAllocation>,
}

impl<'a> FunctionLowering<'a> {
    fn new(
        function: &'a NativeAbiFunction,
        signatures: &'a FunctionSignatures<'a>,
        env_params: Vec<ir::Value>,
    ) -> Self {
        Self {
            function,
            signatures,
            env_params,
            closures: HashMap::new(),
        }
    }
}

#[derive(Debug, Clone)]
struct ClosureAllocation {
    target: String,
    environment: Vec<ValueId>,
}

fn function_value_ids(function: &NativeAbiFunction) -> Vec<ValueId> {
    let mut values = Vec::new();
    values.extend(function.params.iter().copied());
    for block in &function.blocks {
        values.extend(block.params.iter().copied());
        for stmt in &block.stmts {
            match stmt {
                NativeAbiStmt::Literal { dest, .. }
                | NativeAbiStmt::Primitive { dest, .. }
                | NativeAbiStmt::DirectCall { dest, .. }
                | NativeAbiStmt::Tuple { dest, .. }
                | NativeAbiStmt::Record { dest, .. }
                | NativeAbiStmt::Variant { dest, .. }
                | NativeAbiStmt::Select { dest, .. }
                | NativeAbiStmt::LoadEnv { dest, .. }
                | NativeAbiStmt::AllocateClosure { dest, .. }
                | NativeAbiStmt::IndirectClosureCall { dest, .. } => values.push(*dest),
            }
        }
    }
    values
}

fn block_ref(
    function: &NativeAbiFunction,
    blocks: &HashMap<BlockId, ir::Block>,
    block: BlockId,
) -> NativeCraneliftResult<ir::Block> {
    blocks
        .get(&block)
        .copied()
        .ok_or_else(|| NativeCraneliftError::MissingBlock {
            function: function.name.clone(),
            block,
        })
}

fn variable(value: ValueId) -> Variable {
    Variable::from_u32(value.0 as u32)
}

fn cranelift_error(error: impl fmt::Display) -> NativeCraneliftError {
    NativeCraneliftError::Cranelift(error.to_string())
}

#[cfg(test)]
mod tests {
    use crate::abi::{NativeAbiBlock, NativeAbiFunction, NativeAbiModule, NativeAbiStmt};

    use super::*;

    #[test]
    fn jit_runs_int_literal_root() {
        let mut module = compile_abi_module(&NativeAbiModule {
            functions: Vec::new(),
            roots: vec![root_with_stmt(
                NativeAbiStmt::Literal {
                    dest: ValueId(0),
                    literal: NativeLiteral::Int("41".to_string()),
                },
                ValueId(0),
            )],
        })
        .expect("compiled");

        assert_eq!(module.run_roots_i64().expect("ran"), vec![41]);
    }

    #[test]
    fn object_emits_int_literal_root() {
        let module = compile_abi_module_to_object(&NativeAbiModule {
            functions: Vec::new(),
            roots: vec![root_with_stmt(
                NativeAbiStmt::Literal {
                    dest: ValueId(0),
                    literal: NativeLiteral::Int("41".to_string()),
                },
                ValueId(0),
            )],
        })
        .expect("compiled object");

        assert!(!module.bytes().is_empty());
    }

    #[test]
    fn jit_runs_direct_call() {
        let add = NativeAbiFunction {
            name: "add".to_string(),
            params: vec![ValueId(0), ValueId(1)],
            environment_slots: 0,
            blocks: vec![NativeAbiBlock {
                id: BlockId(0),
                params: Vec::new(),
                stmts: vec![NativeAbiStmt::Primitive {
                    dest: ValueId(2),
                    op: core_ir::PrimitiveOp::IntAdd,
                    args: vec![ValueId(0), ValueId(1)],
                }],
                terminator: NativeTerminator::Return(ValueId(2)),
            }],
        };
        let root = NativeAbiFunction {
            name: "root".to_string(),
            params: Vec::new(),
            environment_slots: 0,
            blocks: vec![NativeAbiBlock {
                id: BlockId(0),
                params: Vec::new(),
                stmts: vec![
                    NativeAbiStmt::Literal {
                        dest: ValueId(0),
                        literal: NativeLiteral::Int("20".to_string()),
                    },
                    NativeAbiStmt::Literal {
                        dest: ValueId(1),
                        literal: NativeLiteral::Int("22".to_string()),
                    },
                    NativeAbiStmt::DirectCall {
                        dest: ValueId(2),
                        target: "add".to_string(),
                        args: vec![ValueId(0), ValueId(1)],
                    },
                ],
                terminator: NativeTerminator::Return(ValueId(2)),
            }],
        };
        let mut module = compile_abi_module(&NativeAbiModule {
            functions: vec![add],
            roots: vec![root],
        })
        .expect("compiled");

        assert_eq!(module.run_roots_i64().expect("ran"), vec![42]);
    }

    #[test]
    fn jit_runs_branch() {
        let root = NativeAbiFunction {
            name: "root".to_string(),
            params: Vec::new(),
            environment_slots: 0,
            blocks: vec![
                NativeAbiBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![NativeAbiStmt::Literal {
                        dest: ValueId(0),
                        literal: NativeLiteral::Bool(true),
                    }],
                    terminator: NativeTerminator::Branch {
                        cond: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                NativeAbiBlock {
                    id: BlockId(1),
                    params: Vec::new(),
                    stmts: vec![NativeAbiStmt::Literal {
                        dest: ValueId(1),
                        literal: NativeLiteral::Int("7".to_string()),
                    }],
                    terminator: NativeTerminator::Return(ValueId(1)),
                },
                NativeAbiBlock {
                    id: BlockId(2),
                    params: Vec::new(),
                    stmts: vec![NativeAbiStmt::Literal {
                        dest: ValueId(2),
                        literal: NativeLiteral::Int("9".to_string()),
                    }],
                    terminator: NativeTerminator::Return(ValueId(2)),
                },
            ],
        };
        let mut module = compile_abi_module(&NativeAbiModule {
            functions: Vec::new(),
            roots: vec![root],
        })
        .expect("compiled");

        assert_eq!(module.run_roots_i64().expect("ran"), vec![7]);
    }

    #[test]
    fn jit_runs_hosted_closure_call() {
        let add_capture = NativeAbiFunction {
            name: "add_capture".to_string(),
            params: vec![ValueId(1)],
            environment_slots: 1,
            blocks: vec![NativeAbiBlock {
                id: BlockId(0),
                params: vec![ValueId(1)],
                stmts: vec![
                    NativeAbiStmt::LoadEnv {
                        dest: ValueId(0),
                        slot: 0,
                    },
                    NativeAbiStmt::Primitive {
                        dest: ValueId(2),
                        op: core_ir::PrimitiveOp::IntAdd,
                        args: vec![ValueId(0), ValueId(1)],
                    },
                ],
                terminator: NativeTerminator::Return(ValueId(2)),
            }],
        };
        let root = NativeAbiFunction {
            name: "root".to_string(),
            params: Vec::new(),
            environment_slots: 0,
            blocks: vec![NativeAbiBlock {
                id: BlockId(0),
                params: Vec::new(),
                stmts: vec![
                    NativeAbiStmt::Literal {
                        dest: ValueId(0),
                        literal: NativeLiteral::Int("10".to_string()),
                    },
                    NativeAbiStmt::Literal {
                        dest: ValueId(1),
                        literal: NativeLiteral::Int("32".to_string()),
                    },
                    NativeAbiStmt::AllocateClosure {
                        dest: ValueId(2),
                        target: "add_capture".to_string(),
                        environment: vec![ValueId(0)],
                    },
                    NativeAbiStmt::IndirectClosureCall {
                        dest: ValueId(3),
                        callee: ValueId(2),
                        args: vec![ValueId(1)],
                    },
                ],
                terminator: NativeTerminator::Return(ValueId(3)),
            }],
        };
        let mut module = compile_abi_module(&NativeAbiModule {
            functions: vec![add_capture],
            roots: vec![root],
        })
        .expect("compiled");

        assert_eq!(module.run_roots_i64().expect("ran"), vec![42]);
    }

    fn root_with_stmt(stmt: NativeAbiStmt, ret: ValueId) -> NativeAbiFunction {
        NativeAbiFunction {
            name: "root".to_string(),
            params: Vec::new(),
            environment_slots: 0,
            blocks: vec![NativeAbiBlock {
                id: BlockId(0),
                params: Vec::new(),
                stmts: vec![stmt],
                terminator: NativeTerminator::Return(ret),
            }],
        }
    }
}
