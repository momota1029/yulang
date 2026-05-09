use std::collections::{HashMap, HashSet};
use std::fmt;

use cranelift_codegen::ir::{self, AbiParam, InstBuilder, types};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};
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
    UnsupportedEnvironment {
        function: String,
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
            NativeCraneliftError::UnsupportedEnvironment { function, slots } => write!(
                f,
                "native Cranelift scalar prototype does not support environment for `{function}` ({slots} slots)"
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

pub fn compile_abi_module(module: &NativeAbiModule) -> NativeCraneliftResult<NativeJitModule> {
    validate_abi_module(module)?;
    validate_cranelift_prototype_subset(module)?;
    validate_scalar_subset(module)?;

    let builder =
        JITBuilder::new(cranelift_module::default_libcall_names()).map_err(cranelift_error)?;
    let mut jit = JITModule::new(builder);

    let signatures = declare_functions(&mut jit, module)?;
    define_functions(&mut jit, module, &signatures)?;
    let roots = module
        .roots
        .iter()
        .map(|root| {
            signatures.get(&root.name).copied().ok_or_else(|| {
                NativeCraneliftError::MissingFunction {
                    name: root.name.clone(),
                }
            })
        })
        .collect::<NativeCraneliftResult<Vec<_>>>()?;
    Ok(NativeJitModule { module: jit, roots })
}

fn declare_functions(
    jit: &mut JITModule,
    module: &NativeAbiModule,
) -> NativeCraneliftResult<HashMap<String, FuncId>> {
    let mut declared = HashMap::new();
    for function in module.functions.iter().chain(&module.roots) {
        let sig = function_signature(jit, function);
        let id = jit
            .declare_function(&function.name, Linkage::Export, &sig)
            .map_err(cranelift_error)?;
        declared.insert(function.name.clone(), id);
    }
    Ok(declared)
}

fn define_functions(
    jit: &mut JITModule,
    module: &NativeAbiModule,
    signatures: &HashMap<String, FuncId>,
) -> NativeCraneliftResult<()> {
    for function in module.functions.iter().chain(&module.roots) {
        let func_id = signatures.get(&function.name).copied().ok_or_else(|| {
            NativeCraneliftError::MissingFunction {
                name: function.name.clone(),
            }
        })?;
        let mut ctx = jit.make_context();
        ctx.func.signature = function_signature(jit, function);
        lower_function(jit, &mut ctx, function, signatures)?;
        jit.define_function(func_id, &mut ctx)
            .map_err(cranelift_error)?;
        jit.clear_context(&mut ctx);
    }
    Ok(())
}

fn function_signature(jit: &JITModule, function: &NativeAbiFunction) -> ir::Signature {
    let mut sig = jit.make_signature();
    sig.params
        .extend(function.params.iter().map(|_| AbiParam::new(types::I64)));
    sig.returns.push(AbiParam::new(types::I64));
    sig
}

fn lower_function(
    jit: &mut JITModule,
    ctx: &mut cranelift_codegen::Context,
    function: &NativeAbiFunction,
    signatures: &HashMap<String, FuncId>,
) -> NativeCraneliftResult<()> {
    let mut builder_context = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_context);
    let blocks = create_blocks(&mut builder, function);
    declare_variables(&mut builder, function);
    bind_function_params(&mut builder, function, &blocks)?;

    for block in &function.blocks {
        let clif_block = block_ref(function, &blocks, block.id)?;
        builder.switch_to_block(clif_block);
        bind_block_params(&mut builder, function, block, clif_block)?;
        for stmt in &block.stmts {
            lower_stmt(jit, &mut builder, function, stmt, signatures)?;
        }
        lower_terminator(&mut builder, function, &blocks, &block.terminator)?;
    }
    builder.seal_all_blocks();
    builder.finalize();
    Ok(())
}

fn create_blocks(
    builder: &mut FunctionBuilder<'_>,
    function: &NativeAbiFunction,
) -> HashMap<BlockId, ir::Block> {
    function
        .blocks
        .iter()
        .map(|block| {
            let clif_block = builder.create_block();
            for _ in &block.params {
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
) -> NativeCraneliftResult<()> {
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
    for (param, value) in function.params.iter().zip(
        builder
            .block_params(entry_block)
            .iter()
            .take(function.params.len())
            .copied()
            .collect::<Vec<_>>(),
    ) {
        builder.def_var(variable(*param), value);
    }
    Ok(())
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
        function.params.len()
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

fn lower_stmt(
    jit: &mut JITModule,
    builder: &mut FunctionBuilder<'_>,
    function: &NativeAbiFunction,
    stmt: &NativeAbiStmt,
    signatures: &HashMap<String, FuncId>,
) -> NativeCraneliftResult<()> {
    match stmt {
        NativeAbiStmt::Literal { dest, literal } => {
            let value = lower_literal(builder, function, literal)?;
            builder.def_var(variable(*dest), value);
        }
        NativeAbiStmt::Primitive { dest, op, args } => {
            let args = read_values(builder, args);
            let value = lower_primitive(builder, function, *op, &args)?;
            builder.def_var(variable(*dest), value);
        }
        NativeAbiStmt::DirectCall { dest, target, args } => {
            let func_id = signatures.get(target).copied().ok_or_else(|| {
                NativeCraneliftError::MissingFunction {
                    name: target.clone(),
                }
            })?;
            let callee = jit.declare_func_in_func(func_id, builder.func);
            let args = read_values(builder, args);
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
        NativeAbiStmt::LoadEnv { .. }
        | NativeAbiStmt::AllocateClosure { .. }
        | NativeAbiStmt::IndirectClosureCall { .. } => {
            unreachable!("validated Cranelift scalar subset excludes closure statements")
        }
    }
    Ok(())
}

fn lower_terminator(
    builder: &mut FunctionBuilder<'_>,
    function: &NativeAbiFunction,
    blocks: &HashMap<BlockId, ir::Block>,
    terminator: &NativeTerminator,
) -> NativeCraneliftResult<()> {
    match terminator {
        NativeTerminator::Return(value) => {
            let value = builder.use_var(variable(*value));
            builder.ins().return_(&[value]);
        }
        NativeTerminator::Jump { target, args } => {
            let target = block_ref(function, blocks, *target)?;
            let args = read_block_args(builder, args);
            builder.ins().jump(target, &args);
        }
        NativeTerminator::Branch {
            cond,
            then_block,
            else_block,
        } => {
            let cond = builder.use_var(variable(*cond));
            let cond = builder
                .ins()
                .icmp_imm(ir::condcodes::IntCC::NotEqual, cond, 0);
            let then_block = block_ref(function, blocks, *then_block)?;
            let else_block = block_ref(function, blocks, *else_block)?;
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

fn read_values(builder: &mut FunctionBuilder<'_>, values: &[ValueId]) -> Vec<ir::Value> {
    values
        .iter()
        .map(|value| builder.use_var(variable(*value)))
        .collect()
}

fn read_block_args(builder: &mut FunctionBuilder<'_>, values: &[ValueId]) -> Vec<ir::BlockArg> {
    read_values(builder, values)
        .into_iter()
        .map(ir::BlockArg::Value)
        .collect()
}

fn validate_scalar_subset(module: &NativeAbiModule) -> NativeCraneliftResult<()> {
    for function in module.functions.iter().chain(&module.roots) {
        if function.environment_slots != 0 {
            return Err(NativeCraneliftError::UnsupportedEnvironment {
                function: function.name.clone(),
                slots: function.environment_slots,
            });
        }
        for block in &function.blocks {
            for stmt in &block.stmts {
                validate_scalar_stmt(function, stmt)?;
            }
        }
    }
    Ok(())
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
        NativeAbiStmt::LoadEnv { .. }
        | NativeAbiStmt::AllocateClosure { .. }
        | NativeAbiStmt::IndirectClosureCall { .. } => {
            unreachable!("prototype subset validation rejects closure forms first")
        }
    }
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
