use std::collections::{HashMap, HashSet};
use std::fmt;

use cranelift_codegen::ir::{self, AbiParam, InstBuilder, types};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};
use yulang_runtime as runtime;

use crate::abi::{NativeAbiFunction, NativeAbiModule, NativeAbiStmt};
use crate::abi_validate::{NativeAbiValidateError, validate_abi_module};
use crate::control_ir::{BlockId, NativeLiteral, NativeTerminator, ValueId};

pub type NativeValueCraneliftResult<T> = Result<T, NativeValueCraneliftError>;

#[derive(Debug)]
pub enum NativeValueCraneliftError {
    AbiInvalid(NativeAbiValidateError),
    UnsupportedFunction {
        function: String,
        reason: &'static str,
    },
    UnsupportedStmt {
        function: String,
        kind: &'static str,
    },
    UnsupportedLiteral {
        function: String,
        literal: NativeLiteral,
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

impl fmt::Display for NativeValueCraneliftError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeValueCraneliftError::AbiInvalid(error) => write!(f, "{error}"),
            NativeValueCraneliftError::UnsupportedFunction { function, reason } => {
                write!(
                    f,
                    "native value Cranelift prototype does not support `{function}` yet: {reason}"
                )
            }
            NativeValueCraneliftError::UnsupportedStmt { function, kind } => write!(
                f,
                "native value Cranelift prototype does not support {kind} statements in `{function}` yet"
            ),
            NativeValueCraneliftError::UnsupportedLiteral { function, literal } => write!(
                f,
                "native value Cranelift prototype does not support literal {literal:?} in `{function}` yet"
            ),
            NativeValueCraneliftError::MissingBlock { function, block } => {
                write!(
                    f,
                    "native value Cranelift block {block:?} is missing in `{function}`"
                )
            }
            NativeValueCraneliftError::MissingValue { function, value } => write!(
                f,
                "native value Cranelift value {value:?} is missing in `{function}`"
            ),
            NativeValueCraneliftError::InvalidReturnArity { function, arity } => write!(
                f,
                "native value Cranelift function `{function}` has {arity} return values"
            ),
            NativeValueCraneliftError::Cranelift(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for NativeValueCraneliftError {}

impl From<NativeAbiValidateError> for NativeValueCraneliftError {
    fn from(error: NativeAbiValidateError) -> Self {
        NativeValueCraneliftError::AbiInvalid(error)
    }
}

pub struct NativeValueJitModule {
    module: JITModule,
    roots: Vec<FuncId>,
    strings: Vec<Box<str>>,
}

impl NativeValueJitModule {
    pub fn run_roots(&mut self) -> NativeValueCraneliftResult<Vec<runtime::VmValue>> {
        self.module
            .finalize_definitions()
            .map_err(cranelift_error)?;
        let _string_literals_are_kept_alive = self.strings.len();
        self.roots
            .iter()
            .map(|root| {
                let ptr = self.module.get_finalized_function(*root);
                let call = unsafe {
                    std::mem::transmute::<
                        _,
                        extern "C" fn(*mut NativeValueContext) -> *mut runtime::VmValue,
                    >(ptr)
                };
                let mut context = NativeValueContext::default();
                let value = call(&mut context);
                if value.is_null() {
                    return Err(NativeValueCraneliftError::Cranelift(
                        "native value root returned null".to_string(),
                    ));
                }
                Ok(unsafe { (*value).clone() })
            })
            .collect()
    }
}

#[derive(Default)]
struct NativeValueContext {
    values: Vec<Box<runtime::VmValue>>,
}

pub fn compile_value_abi_module(
    module: &NativeAbiModule,
) -> NativeValueCraneliftResult<NativeValueJitModule> {
    validate_abi_module(module)?;
    validate_value_prototype_subset(module)?;

    let mut builder =
        JITBuilder::new(cranelift_module::default_libcall_names()).map_err(cranelift_error)?;
    builder.symbol(
        "yulang_native_make_string",
        yulang_native_make_string as *const u8,
    );
    builder.symbol(
        "yulang_native_concat_string",
        yulang_native_concat_string as *const u8,
    );
    let mut jit = JITModule::new(builder);

    let helpers = declare_helpers(&mut jit)?;
    let mut strings = Vec::new();
    let functions = declare_functions(&mut jit, module)?;
    define_functions(&mut jit, module, &functions, &helpers, &mut strings)?;
    Ok(NativeValueJitModule {
        module: jit,
        roots: module
            .roots
            .iter()
            .map(|root| {
                functions.get(&root.name).copied().ok_or_else(|| {
                    NativeValueCraneliftError::UnsupportedFunction {
                        function: root.name.clone(),
                        reason: "root was not declared",
                    }
                })
            })
            .collect::<NativeValueCraneliftResult<Vec<_>>>()?,
        strings,
    })
}

fn validate_value_prototype_subset(module: &NativeAbiModule) -> NativeValueCraneliftResult<()> {
    for function in module.functions.iter().chain(&module.roots) {
        if function.environment_slots != 0 {
            return Err(NativeValueCraneliftError::UnsupportedFunction {
                function: function.name.clone(),
                reason: "environment slots",
            });
        }
        for block in &function.blocks {
            for stmt in &block.stmts {
                match stmt {
                    NativeAbiStmt::Literal {
                        literal: NativeLiteral::String(_),
                        ..
                    } => {}
                    NativeAbiStmt::Literal { literal, .. } => {
                        return Err(NativeValueCraneliftError::UnsupportedLiteral {
                            function: function.name.clone(),
                            literal: literal.clone(),
                        });
                    }
                    NativeAbiStmt::Primitive {
                        op: yulang_core_ir::PrimitiveOp::StringConcat,
                        ..
                    } => {}
                    NativeAbiStmt::Primitive { .. } => {
                        return Err(NativeValueCraneliftError::UnsupportedStmt {
                            function: function.name.clone(),
                            kind: "primitive",
                        });
                    }
                    NativeAbiStmt::DirectCall { .. } => {}
                    NativeAbiStmt::LoadEnv { .. } => {
                        return Err(NativeValueCraneliftError::UnsupportedStmt {
                            function: function.name.clone(),
                            kind: "environment load",
                        });
                    }
                    NativeAbiStmt::AllocateClosure { .. } => {
                        return Err(NativeValueCraneliftError::UnsupportedStmt {
                            function: function.name.clone(),
                            kind: "closure allocation",
                        });
                    }
                    NativeAbiStmt::IndirectClosureCall { .. } => {
                        return Err(NativeValueCraneliftError::UnsupportedStmt {
                            function: function.name.clone(),
                            kind: "indirect closure call",
                        });
                    }
                }
            }
            match &block.terminator {
                NativeTerminator::Return(_) => {}
                NativeTerminator::Jump { .. } | NativeTerminator::Branch { .. } => {
                    return Err(NativeValueCraneliftError::UnsupportedFunction {
                        function: function.name.clone(),
                        reason: "multi-block control flow",
                    });
                }
            }
        }
    }
    Ok(())
}

fn declare_functions(
    jit: &mut JITModule,
    module: &NativeAbiModule,
) -> NativeValueCraneliftResult<HashMap<String, FuncId>> {
    let mut functions = HashMap::new();
    for function in module.functions.iter().chain(&module.roots) {
        let sig = value_function_signature(jit, function);
        let id = jit
            .declare_function(&function.name, Linkage::Export, &sig)
            .map_err(cranelift_error)?;
        functions.insert(function.name.clone(), id);
    }
    Ok(functions)
}

fn define_functions(
    jit: &mut JITModule,
    module: &NativeAbiModule,
    functions: &HashMap<String, FuncId>,
    helpers: &ValueHelpers,
    strings: &mut Vec<Box<str>>,
) -> NativeValueCraneliftResult<()> {
    for function in module.functions.iter().chain(&module.roots) {
        let id = functions.get(&function.name).copied().ok_or_else(|| {
            NativeValueCraneliftError::UnsupportedFunction {
                function: function.name.clone(),
                reason: "function was not declared",
            }
        })?;
        let mut ctx = jit.make_context();
        ctx.func.signature = value_function_signature(jit, function);
        lower_value_function(jit, &mut ctx, function, functions, helpers, strings)?;
        jit.define_function(id, &mut ctx).map_err(cranelift_error)?;
        jit.clear_context(&mut ctx);
    }
    Ok(())
}

#[derive(Debug, Clone, Copy)]
struct ValueHelpers {
    make_string: FuncId,
    concat_string: FuncId,
}

fn declare_helpers(jit: &mut JITModule) -> NativeValueCraneliftResult<ValueHelpers> {
    Ok(ValueHelpers {
        make_string: declare_make_string(jit)?,
        concat_string: declare_concat_string(jit)?,
    })
}

fn declare_make_string(jit: &mut JITModule) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = jit.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    jit.declare_function("yulang_native_make_string", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_concat_string(jit: &mut JITModule) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = jit.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    jit.declare_function("yulang_native_concat_string", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn value_function_signature(jit: &JITModule, function: &NativeAbiFunction) -> ir::Signature {
    let mut sig = jit.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params
        .extend(function.params.iter().map(|_| AbiParam::new(types::I64)));
    sig.returns.push(AbiParam::new(types::I64));
    sig
}

fn lower_value_function(
    jit: &mut JITModule,
    ctx: &mut cranelift_codegen::Context,
    function: &NativeAbiFunction,
    functions: &HashMap<String, FuncId>,
    helpers: &ValueHelpers,
    strings: &mut Vec<Box<str>>,
) -> NativeValueCraneliftResult<()> {
    let mut builder_context = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_context);
    let block = function
        .blocks
        .first()
        .ok_or_else(|| NativeValueCraneliftError::MissingBlock {
            function: function.name.clone(),
            block: BlockId(0),
        })?;
    let clif_block = builder.create_block();
    builder.append_block_params_for_function_params(clif_block);
    builder.switch_to_block(clif_block);
    let block_params = builder.block_params(clif_block).to_vec();
    let context = block_params[0];
    let mut values = HashMap::new();
    let mut declared = HashSet::new();
    for value in function_value_ids(function) {
        if declared.insert(value) {
            builder.declare_var(variable(value), types::I64);
        }
    }
    for (param, value) in function.params.iter().zip(block_params.into_iter().skip(1)) {
        builder.def_var(variable(*param), value);
        values.insert(*param, ());
    }
    for stmt in &block.stmts {
        let dest = lower_value_stmt(
            jit,
            &mut builder,
            function,
            stmt,
            functions,
            helpers,
            context,
            &values,
            strings,
        )?;
        values.insert(dest, ());
    }
    match &block.terminator {
        NativeTerminator::Return(value) => {
            if !values.contains_key(value) {
                return Err(NativeValueCraneliftError::MissingValue {
                    function: function.name.clone(),
                    value: *value,
                });
            }
            let value = builder.use_var(variable(*value));
            builder.ins().return_(&[value]);
        }
        NativeTerminator::Jump { .. } | NativeTerminator::Branch { .. } => {
            return Err(NativeValueCraneliftError::UnsupportedFunction {
                function: function.name.clone(),
                reason: "multi-block control flow",
            });
        }
    }
    builder.seal_all_blocks();
    builder.finalize();
    Ok(())
}

fn lower_value_stmt(
    jit: &mut JITModule,
    builder: &mut FunctionBuilder<'_>,
    function: &NativeAbiFunction,
    stmt: &NativeAbiStmt,
    functions: &HashMap<String, FuncId>,
    helpers: &ValueHelpers,
    context: ir::Value,
    defined: &HashMap<ValueId, ()>,
    strings: &mut Vec<Box<str>>,
) -> NativeValueCraneliftResult<ValueId> {
    match stmt {
        NativeAbiStmt::Literal {
            dest,
            literal: NativeLiteral::String(value),
        } => {
            let text = value.clone().into_boxed_str();
            let ptr = text.as_ptr() as i64;
            let len = text.len() as i64;
            strings.push(text);
            let callee = jit.declare_func_in_func(helpers.make_string, builder.func);
            let ptr = builder.ins().iconst(types::I64, ptr);
            let len = builder.ins().iconst(types::I64, len);
            let call = builder.ins().call(callee, &[context, ptr, len]);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(NativeValueCraneliftError::InvalidReturnArity {
                    function: "yulang_native_make_string".to_string(),
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
            Ok(*dest)
        }
        NativeAbiStmt::Literal { literal, .. } => {
            Err(NativeValueCraneliftError::UnsupportedLiteral {
                function: function.name.clone(),
                literal: literal.clone(),
            })
        }
        NativeAbiStmt::Primitive {
            dest,
            op: yulang_core_ir::PrimitiveOp::StringConcat,
            args,
        } => {
            let args = read_values(builder, function, defined, args)?;
            let callee = jit.declare_func_in_func(helpers.concat_string, builder.func);
            let call = builder.ins().call(callee, &[context, args[0], args[1]]);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(NativeValueCraneliftError::InvalidReturnArity {
                    function: "yulang_native_concat_string".to_string(),
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
            Ok(*dest)
        }
        NativeAbiStmt::Primitive { .. } => Err(NativeValueCraneliftError::UnsupportedStmt {
            function: function.name.clone(),
            kind: "primitive",
        }),
        NativeAbiStmt::DirectCall { dest, target, args } => {
            let id = functions.get(target).copied().ok_or_else(|| {
                NativeValueCraneliftError::UnsupportedFunction {
                    function: target.clone(),
                    reason: "target was not declared",
                }
            })?;
            let callee = jit.declare_func_in_func(id, builder.func);
            let mut call_args = vec![context];
            call_args.extend(read_values(builder, function, defined, args)?);
            let call = builder.ins().call(callee, &call_args);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(NativeValueCraneliftError::InvalidReturnArity {
                    function: target.clone(),
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
            Ok(*dest)
        }
        NativeAbiStmt::LoadEnv { .. } => Err(NativeValueCraneliftError::UnsupportedStmt {
            function: function.name.clone(),
            kind: "environment load",
        }),
        NativeAbiStmt::AllocateClosure { .. } => Err(NativeValueCraneliftError::UnsupportedStmt {
            function: function.name.clone(),
            kind: "closure allocation",
        }),
        NativeAbiStmt::IndirectClosureCall { .. } => {
            Err(NativeValueCraneliftError::UnsupportedStmt {
                function: function.name.clone(),
                kind: "indirect closure call",
            })
        }
    }
}

fn read_values(
    builder: &mut FunctionBuilder<'_>,
    function: &NativeAbiFunction,
    defined: &HashMap<ValueId, ()>,
    values: &[ValueId],
) -> NativeValueCraneliftResult<Vec<ir::Value>> {
    values
        .iter()
        .map(|value| {
            if !defined.contains_key(value) {
                return Err(NativeValueCraneliftError::MissingValue {
                    function: function.name.clone(),
                    value: *value,
                });
            }
            Ok(builder.use_var(variable(*value)))
        })
        .collect()
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

fn variable(value: ValueId) -> Variable {
    Variable::from_u32(value.0 as u32)
}

fn cranelift_error(error: impl fmt::Display) -> NativeValueCraneliftError {
    NativeValueCraneliftError::Cranelift(error.to_string())
}

extern "C" fn yulang_native_make_string(
    context: *mut NativeValueContext,
    ptr: *const u8,
    len: usize,
) -> *mut runtime::VmValue {
    if context.is_null() || ptr.is_null() {
        return std::ptr::null_mut();
    }
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len) };
    let text = unsafe { std::str::from_utf8_unchecked(bytes) };
    let context = unsafe { &mut *context };
    context.values.push(Box::new(runtime::VmValue::String(
        runtime::runtime::string_tree::StringTree::from_str(text),
    )));
    context
        .values
        .last_mut()
        .map(|value| value.as_mut() as *mut runtime::VmValue)
        .unwrap_or(std::ptr::null_mut())
}

extern "C" fn yulang_native_concat_string(
    context: *mut NativeValueContext,
    left: *mut runtime::VmValue,
    right: *mut runtime::VmValue,
) -> *mut runtime::VmValue {
    if context.is_null() || left.is_null() || right.is_null() {
        return std::ptr::null_mut();
    }
    let left = unsafe { &*left };
    let right = unsafe { &*right };
    let (runtime::VmValue::String(left), runtime::VmValue::String(right)) = (left, right) else {
        return std::ptr::null_mut();
    };
    let context = unsafe { &mut *context };
    context.values.push(Box::new(runtime::VmValue::String(
        runtime::runtime::string_tree::StringTree::concat(left.clone(), right.clone()),
    )));
    context
        .values
        .last_mut()
        .map(|value| value.as_mut() as *mut runtime::VmValue)
        .unwrap_or(std::ptr::null_mut())
}

#[cfg(test)]
mod tests {
    use crate::abi::{NativeAbiBlock, NativeAbiFunction, NativeAbiModule, NativeAbiStmt};

    use super::*;

    #[test]
    fn jit_runs_string_literal_root() {
        let mut module = compile_value_abi_module(&NativeAbiModule {
            functions: Vec::new(),
            roots: vec![NativeAbiFunction {
                name: "root".to_string(),
                params: Vec::new(),
                environment_slots: 0,
                blocks: vec![NativeAbiBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![NativeAbiStmt::Literal {
                        dest: ValueId(0),
                        literal: NativeLiteral::String("hello".to_string()),
                    }],
                    terminator: NativeTerminator::Return(ValueId(0)),
                }],
            }],
        })
        .expect("compiled");

        assert_eq!(
            module.run_roots().expect("ran"),
            vec![runtime::VmValue::String(
                runtime::runtime::string_tree::StringTree::from_str("hello")
            )]
        );
    }

    #[test]
    fn jit_runs_string_concat_direct_call() {
        let mut module = compile_value_abi_module(&NativeAbiModule {
            functions: vec![NativeAbiFunction {
                name: "concat".to_string(),
                params: vec![ValueId(0), ValueId(1)],
                environment_slots: 0,
                blocks: vec![NativeAbiBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![NativeAbiStmt::Primitive {
                        dest: ValueId(2),
                        op: yulang_core_ir::PrimitiveOp::StringConcat,
                        args: vec![ValueId(0), ValueId(1)],
                    }],
                    terminator: NativeTerminator::Return(ValueId(2)),
                }],
            }],
            roots: vec![NativeAbiFunction {
                name: "root".to_string(),
                params: Vec::new(),
                environment_slots: 0,
                blocks: vec![NativeAbiBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![
                        NativeAbiStmt::Literal {
                            dest: ValueId(0),
                            literal: NativeLiteral::String("hello, ".to_string()),
                        },
                        NativeAbiStmt::Literal {
                            dest: ValueId(1),
                            literal: NativeLiteral::String("world".to_string()),
                        },
                        NativeAbiStmt::DirectCall {
                            dest: ValueId(2),
                            target: "concat".to_string(),
                            args: vec![ValueId(0), ValueId(1)],
                        },
                    ],
                    terminator: NativeTerminator::Return(ValueId(2)),
                }],
            }],
        })
        .expect("compiled");

        assert_eq!(
            module.run_roots().expect("ran"),
            vec![runtime::VmValue::String(
                runtime::runtime::string_tree::StringTree::from_str("hello, world")
            )]
        );
    }

    #[test]
    fn rejects_int_literal_in_value_prototype_for_now() {
        let error = match compile_value_abi_module(&NativeAbiModule {
            functions: Vec::new(),
            roots: vec![NativeAbiFunction {
                name: "root".to_string(),
                params: Vec::new(),
                environment_slots: 0,
                blocks: vec![NativeAbiBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![NativeAbiStmt::Literal {
                        dest: ValueId(0),
                        literal: NativeLiteral::Int("1".to_string()),
                    }],
                    terminator: NativeTerminator::Return(ValueId(0)),
                }],
            }],
        }) {
            Ok(_) => panic!("expected unsupported int literal"),
            Err(error) => error,
        };

        assert!(matches!(
            error,
            NativeValueCraneliftError::UnsupportedLiteral { .. }
        ));
    }
}
