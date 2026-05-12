use std::fmt;

use yulang_typed_ir as typed_ir;

pub type RuntimeResult<T> = Result<T, RuntimeError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeError {
    MissingBindingType {
        path: typed_ir::Path,
    },
    MissingRootType {
        index: usize,
    },
    MissingLocalType {
        path: typed_ir::Path,
    },
    MissingExpectedType {
        node: &'static str,
    },
    MissingApplyEvidence,
    MissingJoinEvidence {
        node: &'static str,
    },
    NonFunctionCallee {
        ty: typed_ir::Type,
    },
    ExpectedThunk {
        ty: typed_ir::Type,
    },
    TypeMismatch {
        expected: typed_ir::Type,
        actual: typed_ir::Type,
        source: TypeSource,
        context: Option<TypeMismatchContext>,
    },
    UnsupportedPatternShape {
        pattern: &'static str,
        ty: typed_ir::Type,
    },
    UnsupportedSelectBase {
        field: typed_ir::Name,
        ty: typed_ir::Type,
    },
    UnboundVariable {
        path: typed_ir::Path,
    },
    ResidualAny {
        ty: typed_ir::Type,
        source: TypeSource,
    },
    NonRuntimeType {
        ty: typed_ir::Type,
        source: TypeSource,
    },
    ResidualPolymorphicBinding {
        path: typed_ir::Path,
        vars: Vec<typed_ir::TypeVar>,
        source: ResidualPolymorphicSource,
    },
    InvariantViolation {
        stage: &'static str,
        context: String,
        message: &'static str,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeSource {
    BindingScheme,
    BindingGraph,
    RootGraph,
    ApplyEvidence,
    ApplyCalleeEvidence,
    ApplyArgumentEvidence,
    ApplyArgumentSourceEdge,
    JoinEvidence,
    Expected,
    Local,
    Literal,
    Structural,
    Validation,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeMismatchContext {
    pub callee: Option<RuntimeCalleeLabel>,
    pub phase: TypeMismatchPhase,
    pub callee_source_edge: Option<u32>,
    pub arg_source_edge: Option<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeCalleeLabel {
    Path(typed_ir::Path),
    Primitive(typed_ir::PrimitiveOp),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeMismatchPhase {
    ApplyCallee,
    ApplyArgument,
    ApplyResult,
    Expected,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResidualPolymorphicSource {
    TypeParams,
    RuntimeTypes,
}

impl RuntimeError {
    pub fn with_type_mismatch_context(self, context: TypeMismatchContext) -> Self {
        match self {
            RuntimeError::TypeMismatch {
                expected,
                actual,
                source,
                context: None,
            } => RuntimeError::TypeMismatch {
                expected,
                actual,
                source,
                context: Some(context),
            },
            other => other,
        }
    }
}

impl ResidualPolymorphicSource {
    fn description(self) -> &'static str {
        match self {
            ResidualPolymorphicSource::TypeParams => "binding type parameters",
            ResidualPolymorphicSource::RuntimeTypes => "runtime body, scheme, or role requirements",
        }
    }
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeError::MissingBindingType { path } => {
                write!(f, "missing binding type for {}", display_path(path))
            }
            RuntimeError::MissingRootType { index } => {
                write!(
                    f,
                    "could not determine the type of expression #{index}. \
This usually means a name, field, method, or operator could not be resolved."
                )
            }
            RuntimeError::MissingLocalType { path } => {
                write!(f, "missing local type for {}", display_path(path))
            }
            RuntimeError::MissingExpectedType { node } => {
                write!(f, "missing expected type for {node}")
            }
            RuntimeError::MissingApplyEvidence => write!(f, "missing apply evidence"),
            RuntimeError::MissingJoinEvidence { node } => {
                write!(f, "missing join evidence for {node}")
            }
            RuntimeError::NonFunctionCallee { ty } => {
                write!(f, "expected a function, but got {}", display_type(ty))
            }
            RuntimeError::ExpectedThunk { ty } => {
                write!(
                    f,
                    "expected an effectful computation, but got {}",
                    display_type(ty)
                )
            }
            RuntimeError::TypeMismatch {
                expected,
                actual,
                source,
                context,
            } => {
                if let Some(context) = context
                    && let Some(callee) = &context.callee
                {
                    let callee = display_callee_label(callee);
                    let mismatch = match context.phase {
                        TypeMismatchPhase::ApplyArgument => "argument type mismatch",
                        TypeMismatchPhase::ApplyCallee => "callee type mismatch",
                        TypeMismatchPhase::ApplyResult => "result type mismatch",
                        TypeMismatchPhase::Expected => "type mismatch",
                    };
                    return write!(
                        f,
                        "{mismatch} in call to `{callee}`: expected {}, got {}",
                        display_type(expected),
                        display_type(actual)
                    );
                }
                let context = match source {
                    TypeSource::ApplyEvidence | TypeSource::ApplyCalleeEvidence => {
                        "function application"
                    }
                    TypeSource::ApplyArgumentEvidence | TypeSource::ApplyArgumentSourceEdge => {
                        "function argument"
                    }
                    TypeSource::JoinEvidence => "branch result",
                    TypeSource::RootGraph => "top-level expression",
                    TypeSource::BindingScheme | TypeSource::BindingGraph => "binding",
                    TypeSource::Local => "local value",
                    TypeSource::Literal => "literal",
                    TypeSource::Structural => "structured value",
                    TypeSource::Validation => "runtime validation",
                    TypeSource::Expected => "expected type",
                };
                write!(
                    f,
                    "{context} type mismatch: expected {}, got {}",
                    display_type(expected),
                    display_type(actual)
                )
            }
            RuntimeError::UnsupportedPatternShape { pattern, ty } => {
                write!(
                    f,
                    "cannot match a {pattern} pattern against {}",
                    display_type(ty)
                )
            }
            RuntimeError::UnsupportedSelectBase { field, ty } => {
                write!(f, "cannot select .{} from {}", field.0, display_type(ty))
            }
            RuntimeError::UnboundVariable { path } => {
                write!(f, "unbound variable {}", display_path(path))
            }
            RuntimeError::ResidualAny { ty, source } => {
                write!(
                    f,
                    "runtime type is still unknown after inference ({source:?}): {}",
                    display_type(ty)
                )
            }
            RuntimeError::NonRuntimeType { ty, source } => {
                write!(
                    f,
                    "type cannot be represented at runtime ({source:?}): {}",
                    display_type(ty)
                )
            }
            RuntimeError::ResidualPolymorphicBinding { path, vars, source } => {
                let plural = if vars.len() == 1 { "" } else { "s" };
                write!(
                    f,
                    "cannot infer all runtime types needed for `{}`. \
                     Add a type annotation that fixes the remaining type \
                     variable{}: {}. Source: {}.",
                    display_path(path),
                    plural,
                    display_type_vars(vars),
                    source.description()
                )
            }
            RuntimeError::InvariantViolation {
                stage,
                context,
                message,
            } => write!(
                f,
                "runtime invariant failed after {stage} at {context}: {message}"
            ),
        }
    }
}

impl std::error::Error for RuntimeError {}

fn display_path(path: &typed_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

fn display_callee_label(label: &RuntimeCalleeLabel) -> String {
    match label {
        RuntimeCalleeLabel::Path(path) => display_callee_path(path),
        RuntimeCalleeLabel::Primitive(op) => display_primitive_op(*op).to_string(),
    }
}

fn display_callee_path(path: &typed_ir::Path) -> String {
    match path.segments.as_slice() {
        [std, int, add] if std.0 == "std" && int.0 == "int" && add.0 == "add" => "+".to_string(),
        [std, int, sub] if std.0 == "std" && int.0 == "int" && sub.0 == "sub" => "-".to_string(),
        [std, int, mul] if std.0 == "std" && int.0 == "int" && mul.0 == "mul" => "*".to_string(),
        [std, int, div] if std.0 == "std" && int.0 == "int" && div.0 == "div" => "/".to_string(),
        _ => display_path(path),
    }
}

fn display_primitive_op(op: typed_ir::PrimitiveOp) -> &'static str {
    match op {
        typed_ir::PrimitiveOp::BoolNot => "not",
        typed_ir::PrimitiveOp::BoolEq => "==",
        typed_ir::PrimitiveOp::IntAdd => "+",
        typed_ir::PrimitiveOp::IntSub => "-",
        typed_ir::PrimitiveOp::IntMul => "*",
        typed_ir::PrimitiveOp::IntDiv => "/",
        typed_ir::PrimitiveOp::IntEq => "==",
        typed_ir::PrimitiveOp::IntLt => "<",
        typed_ir::PrimitiveOp::IntLe => "<=",
        typed_ir::PrimitiveOp::IntGt => ">",
        typed_ir::PrimitiveOp::IntGe => ">=",
        typed_ir::PrimitiveOp::FloatAdd => "+",
        typed_ir::PrimitiveOp::FloatSub => "-",
        typed_ir::PrimitiveOp::FloatMul => "*",
        typed_ir::PrimitiveOp::FloatDiv => "/",
        typed_ir::PrimitiveOp::FloatEq => "==",
        typed_ir::PrimitiveOp::FloatLt => "<",
        typed_ir::PrimitiveOp::FloatLe => "<=",
        typed_ir::PrimitiveOp::FloatGt => ">",
        typed_ir::PrimitiveOp::FloatGe => ">=",
        typed_ir::PrimitiveOp::StringEq => "==",
        typed_ir::PrimitiveOp::StringConcat => "++",
        typed_ir::PrimitiveOp::ListIndex => "[]",
        typed_ir::PrimitiveOp::ListIndexRange => "[..]",
        typed_ir::PrimitiveOp::ListSplice => "splice",
        typed_ir::PrimitiveOp::StringIndex => "[]",
        typed_ir::PrimitiveOp::StringIndexRange => "[..]",
        typed_ir::PrimitiveOp::StringSplice => "splice",
        _ => primitive_op_name(op),
    }
}

fn primitive_op_name(op: typed_ir::PrimitiveOp) -> &'static str {
    match op {
        typed_ir::PrimitiveOp::ListEmpty => "list.empty",
        typed_ir::PrimitiveOp::ListSingleton => "list.singleton",
        typed_ir::PrimitiveOp::ListLen => "list.len",
        typed_ir::PrimitiveOp::ListMerge => "list.merge",
        typed_ir::PrimitiveOp::ListIndexRangeRaw => "list.index_range_raw",
        typed_ir::PrimitiveOp::ListSpliceRaw => "list.splice_raw",
        typed_ir::PrimitiveOp::ListViewRaw => "list.view_raw",
        typed_ir::PrimitiveOp::StringLen => "string.len",
        typed_ir::PrimitiveOp::StringIndexRangeRaw => "string.index_range_raw",
        typed_ir::PrimitiveOp::StringSpliceRaw => "string.splice_raw",
        typed_ir::PrimitiveOp::IntToString => "int.to_string",
        typed_ir::PrimitiveOp::IntToHex => "int.to_hex",
        typed_ir::PrimitiveOp::IntToUpperHex => "int.to_upper_hex",
        typed_ir::PrimitiveOp::FloatToString => "float.to_string",
        typed_ir::PrimitiveOp::BoolToString => "bool.to_string",
        _ => "primitive",
    }
}

fn display_type_vars(vars: &[typed_ir::TypeVar]) -> String {
    if vars.is_empty() {
        return "<none>".to_string();
    }
    vars.iter()
        .map(display_type_var)
        .collect::<Vec<_>>()
        .join(", ")
}

fn display_type_var(var: &typed_ir::TypeVar) -> &str {
    let name = var.0.as_str();
    if name
        .strip_prefix('t')
        .is_some_and(|rest| !rest.is_empty() && rest.chars().all(|ch| ch.is_ascii_digit()))
    {
        "'a"
    } else {
        name
    }
}

fn display_type(ty: &typed_ir::Type) -> String {
    match ty {
        typed_ir::Type::Unknown => "?".to_string(),
        typed_ir::Type::Var(var) => display_type_var(var).to_string(),
        typed_ir::Type::Never => "never".to_string(),
        typed_ir::Type::Any => "_".to_string(),
        typed_ir::Type::Named { path, args } => {
            let name = display_path(path);
            if args.is_empty() {
                name
            } else {
                format!(
                    "{}<{}>",
                    name,
                    args.iter()
                        .map(display_type_arg)
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            let param = display_type(param);
            let param_effect = display_type(param_effect);
            let ret_effect = display_type(ret_effect);
            let ret = display_type(ret);
            if param_effect == "never" && ret_effect == "never" {
                format!("{param} -> {ret}")
            } else {
                format!("{param} -{param_effect} / {ret_effect}-> {ret}")
            }
        }
        typed_ir::Type::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(display_type)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        typed_ir::Type::Record(record) => {
            let mut parts = record
                .fields
                .iter()
                .map(|field| {
                    let optional = if field.optional { "?" } else { "" };
                    format!(
                        "{}{}: {}",
                        field.name.0,
                        optional,
                        display_type(&field.value)
                    )
                })
                .collect::<Vec<_>>();
            match &record.spread {
                Some(typed_ir::RecordSpread::Head(rest))
                | Some(typed_ir::RecordSpread::Tail(rest)) => {
                    parts.push(format!("..{}", display_type(rest)));
                }
                None => {}
            }
            format!("{{{}}}", parts.join(", "))
        }
        typed_ir::Type::Variant(variant) => {
            let mut parts = variant
                .cases
                .iter()
                .map(|case| {
                    if case.payloads.is_empty() {
                        case.name.0.clone()
                    } else {
                        format!(
                            "{}({})",
                            case.name.0,
                            case.payloads
                                .iter()
                                .map(display_type)
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                    }
                })
                .collect::<Vec<_>>();
            if let Some(rest) = &variant.tail {
                parts.push(format!("..{}", display_type(rest)));
            }
            format!("[{}]", parts.join(" | "))
        }
        typed_ir::Type::Row { items, tail } => {
            let mut parts = items.iter().map(display_type).collect::<Vec<_>>();
            parts.push(format!("..{}", display_type(tail)));
            format!("[{}]", parts.join("; "))
        }
        typed_ir::Type::Union(items) => items
            .iter()
            .map(display_type)
            .collect::<Vec<_>>()
            .join(" | "),
        typed_ir::Type::Inter(items) => items
            .iter()
            .map(display_type)
            .collect::<Vec<_>>()
            .join(" & "),
        typed_ir::Type::Recursive { var, body } => {
            format!("rec {}. {}", var.0, display_type(body))
        }
    }
}

fn display_type_arg(arg: &typed_ir::TypeArg) -> String {
    match arg {
        typed_ir::TypeArg::Type(ty) => display_type(ty),
        typed_ir::TypeArg::Bounds(bounds) => display_type_bounds(bounds),
    }
}

fn display_type_bounds(bounds: &typed_ir::TypeBounds) -> String {
    match (&bounds.lower, &bounds.upper) {
        (Some(lower), Some(upper)) if lower == upper => display_type(lower),
        (Some(lower), Some(upper)) => format!("{}..{}", display_type(lower), display_type(upper)),
        (Some(lower), None) => format!("{}..", display_type(lower)),
        (None, Some(upper)) => format!("..{}", display_type(upper)),
        (None, None) => "_".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn displays_apply_type_mismatch_without_debug_type_dump() {
        let error = RuntimeError::TypeMismatch {
            expected: fun_type(named_type("bool"), named_type("bool")),
            actual: fun_type(named_type("int"), named_type("int")),
            source: TypeSource::ApplyEvidence,
            context: None,
        };

        assert_eq!(
            error.to_string(),
            "function application type mismatch: expected bool -> bool, got int -> int"
        );
    }

    #[test]
    fn displays_apply_type_mismatch_with_callee_context() {
        let error = RuntimeError::TypeMismatch {
            expected: fun_type(named_type("bool"), named_type("bool")),
            actual: fun_type(named_type("int"), named_type("int")),
            source: TypeSource::ApplyEvidence,
            context: Some(TypeMismatchContext {
                callee: Some(RuntimeCalleeLabel::Path(typed_ir::Path {
                    segments: vec![
                        typed_ir::Name("std".to_string()),
                        typed_ir::Name("int".to_string()),
                        typed_ir::Name("add".to_string()),
                    ],
                })),
                phase: TypeMismatchPhase::ApplyResult,
                callee_source_edge: Some(1),
                arg_source_edge: Some(2),
            }),
        };

        assert_eq!(
            error.to_string(),
            "result type mismatch in call to `+`: expected bool -> bool, got int -> int"
        );
    }

    #[test]
    fn displays_missing_root_type_as_surface_inference_failure() {
        let error = RuntimeError::MissingRootType { index: 0 };

        assert_eq!(
            error.to_string(),
            "could not determine the type of expression #0. This usually means a name, field, method, or operator could not be resolved."
        );
    }

    #[test]
    fn displays_residual_polymorphic_source() {
        let error = RuntimeError::ResidualPolymorphicBinding {
            path: typed_ir::Path::from_name(typed_ir::Name("f".to_string())),
            vars: vec![typed_ir::TypeVar("a".to_string())],
            source: ResidualPolymorphicSource::RuntimeTypes,
        };

        assert_eq!(
            error.to_string(),
            "cannot infer all runtime types needed for `f`. \
             Add a type annotation that fixes the remaining type variable: a. \
             Source: runtime body, scheme, or role requirements."
        );
    }

    #[test]
    fn displays_internal_type_vars_as_user_type_vars() {
        let error = RuntimeError::ResidualPolymorphicBinding {
            path: typed_ir::Path::from_name(typed_ir::Name("wrap".to_string())),
            vars: vec![typed_ir::TypeVar("t4230".to_string())],
            source: ResidualPolymorphicSource::TypeParams,
        };

        assert_eq!(
            error.to_string(),
            "cannot infer all runtime types needed for `wrap`. \
             Add a type annotation that fixes the remaining type variable: 'a. \
             Source: binding type parameters."
        );
    }

    fn fun_type(param: typed_ir::Type, ret: typed_ir::Type) -> typed_ir::Type {
        typed_ir::Type::Fun {
            param: Box::new(param),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Never),
            ret: Box::new(ret),
        }
    }

    fn named_type(name: &str) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }
}
