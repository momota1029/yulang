use std::fmt::Write as _;

use crate::abi::{NativeAbiBlock, NativeAbiFunction, NativeAbiModule, NativeAbiStmt};
use crate::control_ir::{NativeLiteral, NativeTerminator, ValueId};

pub fn format_abi_module(module: &NativeAbiModule) -> String {
    let mut out = String::new();
    for function in &module.functions {
        format_function(&mut out, "fn", function);
    }
    for root in &module.roots {
        format_function(&mut out, "root", root);
    }
    out
}

fn format_function(out: &mut String, kind: &str, function: &NativeAbiFunction) {
    let _ = writeln!(
        out,
        "{kind} {}({}) env_slots={}:",
        function.name,
        format_values(&function.params),
        function.environment_slots
    );
    for block in &function.blocks {
        format_block(out, block);
    }
    out.push('\n');
}

fn format_block(out: &mut String, block: &NativeAbiBlock) {
    let _ = writeln!(
        out,
        "  block{}({}):",
        block.id.0,
        format_values(&block.params)
    );
    for stmt in &block.stmts {
        let _ = writeln!(out, "    {}", format_stmt(stmt));
    }
    let _ = writeln!(out, "    {}", format_terminator(&block.terminator));
}

fn format_stmt(stmt: &NativeAbiStmt) -> String {
    match stmt {
        NativeAbiStmt::Literal { dest, literal } => {
            format!("{} = {}", format_value(*dest), format_literal(literal))
        }
        NativeAbiStmt::Primitive { dest, op, args } => format!(
            "{} = primitive {:?}({})",
            format_value(*dest),
            op,
            format_values(args)
        ),
        NativeAbiStmt::DirectCall { dest, target, args } => format!(
            "{} = call {target}({})",
            format_value(*dest),
            format_values(args)
        ),
        NativeAbiStmt::Tuple { dest, items } => {
            format!("{} = tuple({})", format_value(*dest), format_values(items))
        }
        NativeAbiStmt::Record { dest, base, fields } => format!(
            "{} = record{}({})",
            format_value(*dest),
            base.map(|base| format!(" ..{}", format_value(base)))
                .unwrap_or_default(),
            fields
                .iter()
                .map(|field| format!("{}: {}", field.name.0, format_value(field.value)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        NativeAbiStmt::Variant { dest, tag, value } => format!(
            "{} = variant :{}({})",
            format_value(*dest),
            tag.0,
            value
                .map(format_value)
                .unwrap_or_else(|| "none".to_string())
        ),
        NativeAbiStmt::Select { dest, base, field } => format!(
            "{} = select {}.{}",
            format_value(*dest),
            format_value(*base),
            field.0
        ),
        NativeAbiStmt::TupleGet { dest, tuple, index } => format!(
            "{} = tuple_get {}[{index}]",
            format_value(*dest),
            format_value(*tuple)
        ),
        NativeAbiStmt::VariantTagEq { dest, variant, tag } => format!(
            "{} = variant_tag_eq {} :{}",
            format_value(*dest),
            format_value(*variant),
            tag.0
        ),
        NativeAbiStmt::VariantPayload { dest, variant } => format!(
            "{} = variant_payload {}",
            format_value(*dest),
            format_value(*variant)
        ),
        NativeAbiStmt::ValueEq { dest, left, right } => format!(
            "{} = value_eq {} {}",
            format_value(*dest),
            format_value(*left),
            format_value(*right)
        ),
        NativeAbiStmt::LoadEnv { dest, slot } => {
            format!("{} = load_env[{slot}]", format_value(*dest))
        }
        NativeAbiStmt::AllocateClosure {
            dest,
            target,
            environment,
        } => format!(
            "{} = closure {target} env({})",
            format_value(*dest),
            format_values(environment)
        ),
        NativeAbiStmt::IndirectClosureCall { dest, callee, args } => format!(
            "{} = call_closure {}({})",
            format_value(*dest),
            format_value(*callee),
            format_values(args)
        ),
    }
}

fn format_terminator(terminator: &NativeTerminator) -> String {
    match terminator {
        NativeTerminator::Return(value) => format!("return {}", format_value(*value)),
        NativeTerminator::Jump { target, args } => {
            format!("jump block{}({})", target.0, format_values(args))
        }
        NativeTerminator::Branch {
            cond,
            then_block,
            else_block,
        } => format!(
            "branch {} block{} block{}",
            format_value(*cond),
            then_block.0,
            else_block.0
        ),
    }
}

fn format_literal(literal: &NativeLiteral) -> String {
    match literal {
        NativeLiteral::Int(value) => value.clone(),
        NativeLiteral::Float(value) => value.clone(),
        NativeLiteral::String(value) => format!("{value:?}"),
        NativeLiteral::Bool(value) => value.to_string(),
        NativeLiteral::Unit => "()".to_string(),
    }
}

fn format_values(values: &[ValueId]) -> String {
    values
        .iter()
        .map(|value| format_value(*value))
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_value(value: ValueId) -> String {
    format!("%{}", value.0)
}

#[cfg(test)]
mod tests {
    use yulang_typed_ir as typed_ir;

    use crate::abi::{NativeAbiBlock, NativeAbiFunction, NativeAbiModule, NativeAbiStmt};
    use crate::control_ir::{BlockId, NativeLiteral, NativeTerminator, ValueId};

    use super::*;

    #[test]
    fn formats_primitive_abi_module() {
        let module = NativeAbiModule {
            functions: vec![NativeAbiFunction {
                name: "add".to_string(),
                params: vec![ValueId(0), ValueId(1)],
                environment_slots: 0,
                blocks: vec![NativeAbiBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![NativeAbiStmt::Primitive {
                        dest: ValueId(2),
                        op: typed_ir::PrimitiveOp::IntAdd,
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
                    stmts: vec![NativeAbiStmt::Literal {
                        dest: ValueId(0),
                        literal: NativeLiteral::Int("41".to_string()),
                    }],
                    terminator: NativeTerminator::Return(ValueId(0)),
                }],
            }],
        };

        assert_eq!(
            format_abi_module(&module),
            concat!(
                "fn add(%0, %1) env_slots=0:\n",
                "  block0():\n",
                "    %2 = primitive IntAdd(%0, %1)\n",
                "    return %2\n",
                "\n",
                "root root() env_slots=0:\n",
                "  block0():\n",
                "    %0 = 41\n",
                "    return %0\n",
                "\n",
            )
        );
    }

    #[test]
    fn formats_closure_abi_forms() {
        let module = NativeAbiModule {
            functions: Vec::new(),
            roots: vec![NativeAbiFunction {
                name: "root".to_string(),
                params: Vec::new(),
                environment_slots: 1,
                blocks: vec![NativeAbiBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![
                        NativeAbiStmt::LoadEnv {
                            dest: ValueId(0),
                            slot: 0,
                        },
                        NativeAbiStmt::AllocateClosure {
                            dest: ValueId(1),
                            target: "root#lambda0".to_string(),
                            environment: vec![ValueId(0)],
                        },
                        NativeAbiStmt::IndirectClosureCall {
                            dest: ValueId(2),
                            callee: ValueId(1),
                            args: vec![ValueId(0)],
                        },
                    ],
                    terminator: NativeTerminator::Return(ValueId(2)),
                }],
            }],
        };

        assert_eq!(
            format_abi_module(&module),
            concat!(
                "root root() env_slots=1:\n",
                "  block0():\n",
                "    %0 = load_env[0]\n",
                "    %1 = closure root#lambda0 env(%0)\n",
                "    %2 = call_closure %1(%0)\n",
                "    return %2\n",
                "\n",
            )
        );
    }
}
