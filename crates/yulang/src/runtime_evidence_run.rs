use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

use control_vm::{
    Block, DefId, Expr, ExprId, InstanceId, Pat, Program, RecordSpread, Root, SelectResolution,
    Stmt,
};
use specialize::mono::{Lit, PrimitiveContext, PrimitiveOp};

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct RuntimeEvidenceRunOutput {
    values: Vec<RuntimeEvidenceValue>,
}

impl RuntimeEvidenceRunOutput {
    pub(crate) fn roots_text(&self) -> String {
        format!("run roots {}\n", format_values(&self.values))
    }
}

#[derive(Debug, Clone, PartialEq)]
enum RuntimeEvidenceValue {
    Int(i64),
    BigInt(String),
    Float(f64),
    Str(String),
    Bool(bool),
    Unit,
    Tuple(Vec<SharedValue>),
    Record(Vec<RuntimeEvidenceValueField>),
    PolyVariant {
        tag: String,
        payloads: Vec<SharedValue>,
    },
    DataConstructor {
        def: DefId,
        payloads: Vec<SharedValue>,
    },
    ConstructorFunction {
        def: DefId,
        arity: usize,
        args: Vec<SharedValue>,
    },
    PrimitiveOp {
        op: PrimitiveOp,
        context: PrimitiveContext,
        args: Vec<SharedValue>,
    },
    Closure(Rc<RuntimeEvidenceClosure>),
    EffectOp {
        path: Vec<String>,
    },
    Thunk(Rc<RuntimeEvidenceThunk>),
}

#[derive(Debug, Clone, PartialEq)]
struct RuntimeEvidenceValueField {
    name: String,
    value: SharedValue,
}

#[derive(Debug, Clone, PartialEq)]
struct RuntimeEvidenceClosure {
    param: Pat,
    body: ExprId,
    env: Env,
}

#[derive(Debug, Clone, PartialEq)]
enum RuntimeEvidenceThunk {
    Expr { body: ExprId, env: Env },
}

type SharedValue = Rc<RuntimeEvidenceValue>;
type Env = HashMap<DefId, SharedValue>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RuntimeEvidenceRunError {
    MissingExpr(ExprId),
    MissingInstance(InstanceId),
    MismatchedInstanceSlot {
        requested: InstanceId,
        actual: InstanceId,
    },
    RecursiveInstance(InstanceId),
    UnboundLocal(DefId),
    UnsupportedExpr(&'static str),
    UnsupportedPattern(&'static str),
    UnsupportedPrimitive(PrimitiveOp),
    NotFunction(String),
    NotThunk(String),
    NotRecord(String),
    MissingRecordField(String),
    PatternMismatch,
    DivideByZero,
}

impl fmt::Display for RuntimeEvidenceRunError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingExpr(expr) => write!(f, "runtime-evidence-run missing expr e{}", expr.0),
            Self::MissingInstance(instance) => {
                write!(f, "runtime-evidence-run missing instance i{}", instance.0)
            }
            Self::MismatchedInstanceSlot { requested, actual } => write!(
                f,
                "runtime-evidence-run mismatched instance slot i{} != i{}",
                requested.0, actual.0
            ),
            Self::RecursiveInstance(instance) => {
                write!(f, "runtime-evidence-run recursive instance i{}", instance.0)
            }
            Self::UnboundLocal(def) => write!(f, "runtime-evidence-run unbound local d{}", def.0),
            Self::UnsupportedExpr(kind) => {
                write!(f, "runtime-evidence-run unsupported expr: {kind}")
            }
            Self::UnsupportedPattern(kind) => {
                write!(f, "runtime-evidence-run unsupported pattern: {kind}")
            }
            Self::UnsupportedPrimitive(op) => {
                write!(f, "runtime-evidence-run unsupported primitive: {op:?}")
            }
            Self::NotFunction(value) => write!(f, "runtime-evidence-run not a function: {value}"),
            Self::NotThunk(value) => write!(f, "runtime-evidence-run not a thunk: {value}"),
            Self::NotRecord(value) => write!(f, "runtime-evidence-run not a record: {value}"),
            Self::MissingRecordField(name) => {
                write!(f, "runtime-evidence-run missing record field: {name}")
            }
            Self::PatternMismatch => write!(f, "runtime-evidence-run pattern mismatch"),
            Self::DivideByZero => write!(f, "runtime-evidence-run division by zero"),
        }
    }
}

pub(crate) fn run_program(
    program: &Program,
) -> Result<RuntimeEvidenceRunOutput, RuntimeEvidenceRunError> {
    RuntimeEvidenceRunner::new(program).run()
}

struct RuntimeEvidenceRunner<'a> {
    program: &'a Program,
    instances: HashMap<InstanceId, SharedValue>,
    evaluating_instances: HashSet<InstanceId>,
}

impl<'a> RuntimeEvidenceRunner<'a> {
    fn new(program: &'a Program) -> Self {
        Self {
            program,
            instances: HashMap::new(),
            evaluating_instances: HashSet::new(),
        }
    }

    fn run(&mut self) -> Result<RuntimeEvidenceRunOutput, RuntimeEvidenceRunError> {
        let mut values = Vec::new();
        let mut env = Env::new();
        for root in &self.program.roots {
            match root {
                Root::Instance(instance) => values.push(self.eval_instance(*instance)?),
                Root::EvalInstance(instance) => {
                    let _ = self.eval_instance(*instance)?;
                }
                Root::Expr(expr) => values.push(self.eval_expr(*expr, &mut env)?),
            }
        }
        Ok(RuntimeEvidenceRunOutput {
            values: values
                .into_iter()
                .map(|value| value.as_ref().clone())
                .collect(),
        })
    }

    fn eval_instance(
        &mut self,
        instance: InstanceId,
    ) -> Result<SharedValue, RuntimeEvidenceRunError> {
        if let Some(value) = self.instances.get(&instance) {
            return Ok(value.clone());
        }
        if !self.evaluating_instances.insert(instance) {
            return Err(RuntimeEvidenceRunError::RecursiveInstance(instance));
        }
        let Some(control_instance) = self.program.instances.get(instance.0 as usize) else {
            self.evaluating_instances.remove(&instance);
            return Err(RuntimeEvidenceRunError::MissingInstance(instance));
        };
        if control_instance.id != instance {
            self.evaluating_instances.remove(&instance);
            return Err(RuntimeEvidenceRunError::MismatchedInstanceSlot {
                requested: instance,
                actual: control_instance.id,
            });
        }

        let mut env = Env::new();
        let value = self.eval_expr(control_instance.entry, &mut env);
        self.evaluating_instances.remove(&instance);
        let value = value?;
        self.instances.insert(instance, value.clone());
        Ok(value)
    }

    fn eval_expr(
        &mut self,
        expr: ExprId,
        env: &mut Env,
    ) -> Result<SharedValue, RuntimeEvidenceRunError> {
        let Some(expr) = self.program.exprs.get(expr.0 as usize) else {
            return Err(RuntimeEvidenceRunError::MissingExpr(expr));
        };
        match expr {
            Expr::Lit(lit) => Ok(shared(value_from_lit(lit))),
            Expr::PrimitiveOp { op, context } => self.eval_primitive_op(*op, context.clone()),
            Expr::Constructor { def, arity } => {
                Ok(shared(RuntimeEvidenceValue::ConstructorFunction {
                    def: *def,
                    arity: *arity,
                    args: Vec::new(),
                }))
            }
            Expr::EffectOp { path } => Ok(shared(RuntimeEvidenceValue::EffectOp {
                path: path.clone(),
            })),
            Expr::Local(def) => env
                .get(def)
                .cloned()
                .ok_or(RuntimeEvidenceRunError::UnboundLocal(*def)),
            Expr::InstanceRef(instance) => self.eval_instance(*instance),
            Expr::Coerce { expr, .. } => self.eval_expr(*expr, env),
            Expr::MakeThunk { body, .. } => Ok(shared(RuntimeEvidenceValue::Thunk(Rc::new(
                RuntimeEvidenceThunk::Expr {
                    body: *body,
                    env: env.clone(),
                },
            )))),
            Expr::ForceThunk { thunk, .. } => {
                let thunk = self.eval_expr(*thunk, env)?;
                self.force_thunk(thunk)
            }
            Expr::FunctionAdapter { function, .. } => self.eval_expr(*function, env),
            Expr::MarkerFrame { body, .. } => self.eval_expr(*body, env),
            Expr::Apply { callee, arg } => {
                let callee = self.eval_expr(*callee, env)?;
                let mut arg_env = env.clone();
                let arg = self.eval_expr(*arg, &mut arg_env)?;
                self.apply_value(callee, arg)
            }
            Expr::RefSet { .. } => Err(RuntimeEvidenceRunError::UnsupportedExpr("ref-set")),
            Expr::Lambda { param, body } => Ok(shared(RuntimeEvidenceValue::Closure(Rc::new(
                RuntimeEvidenceClosure {
                    param: param.clone(),
                    body: *body,
                    env: env.clone(),
                },
            )))),
            Expr::Tuple(items) => {
                let mut values = Vec::with_capacity(items.len());
                for item in items {
                    values.push(self.eval_expr(*item, env)?);
                }
                Ok(shared(RuntimeEvidenceValue::Tuple(values)))
            }
            Expr::Record { fields, spread } => {
                let mut values = match spread {
                    RecordSpread::None => Vec::new(),
                    RecordSpread::Head(expr) => {
                        let spread = self.eval_expr(*expr, env)?;
                        record_fields(spread.as_ref())?
                    }
                    RecordSpread::Tail(_) => {
                        return Err(RuntimeEvidenceRunError::UnsupportedExpr(
                            "tail record spread",
                        ));
                    }
                };
                for field in fields {
                    values.push(RuntimeEvidenceValueField {
                        name: field.name.clone(),
                        value: self.eval_expr(field.value, env)?,
                    });
                }
                Ok(shared(RuntimeEvidenceValue::Record(values)))
            }
            Expr::PolyVariant { tag, payloads } => {
                let mut values = Vec::with_capacity(payloads.len());
                for payload in payloads {
                    values.push(self.eval_expr(*payload, env)?);
                }
                Ok(shared(RuntimeEvidenceValue::PolyVariant {
                    tag: tag.clone(),
                    payloads: values,
                }))
            }
            Expr::Select {
                base,
                name,
                resolution,
            } => self.eval_select(*base, name, resolution, env),
            Expr::Case { scrutinee, arms } => {
                let scrutinee = self.eval_expr(*scrutinee, env)?;
                self.eval_case(scrutinee, arms, env)
            }
            Expr::Catch { .. } => Err(RuntimeEvidenceRunError::UnsupportedExpr("catch")),
            Expr::Block(block) => self.eval_block(block, env),
        }
    }

    fn eval_primitive_op(
        &mut self,
        op: PrimitiveOp,
        context: PrimitiveContext,
    ) -> Result<SharedValue, RuntimeEvidenceRunError> {
        if op.arity() == 0 {
            return self.apply_primitive(op, &[]);
        }
        Ok(shared(RuntimeEvidenceValue::PrimitiveOp {
            op,
            context,
            args: Vec::new(),
        }))
    }

    fn apply_value(
        &mut self,
        callee: SharedValue,
        arg: SharedValue,
    ) -> Result<SharedValue, RuntimeEvidenceRunError> {
        match callee.as_ref() {
            RuntimeEvidenceValue::PrimitiveOp { op, context, args } => {
                let mut args = args.clone();
                args.push(arg);
                if args.len() < op.arity() {
                    return Ok(shared(RuntimeEvidenceValue::PrimitiveOp {
                        op: *op,
                        context: context.clone(),
                        args,
                    }));
                }
                self.apply_primitive(*op, &args)
            }
            RuntimeEvidenceValue::ConstructorFunction { def, arity, args } => {
                let mut args = args.clone();
                args.push(arg);
                if args.len() < *arity {
                    return Ok(shared(RuntimeEvidenceValue::ConstructorFunction {
                        def: *def,
                        arity: *arity,
                        args,
                    }));
                }
                Ok(shared(RuntimeEvidenceValue::DataConstructor {
                    def: *def,
                    payloads: args,
                }))
            }
            RuntimeEvidenceValue::Closure(closure) => {
                let mut env = closure.env.clone();
                bind_pat(&closure.param, arg, &mut env)?;
                self.eval_expr(closure.body, &mut env)
            }
            RuntimeEvidenceValue::Thunk(_) => {
                let callee = self.force_thunk(callee)?;
                self.apply_value(callee, arg)
            }
            RuntimeEvidenceValue::EffectOp { .. } => Err(RuntimeEvidenceRunError::UnsupportedExpr(
                "effect operation call",
            )),
            value => Err(RuntimeEvidenceRunError::NotFunction(format_value(value))),
        }
    }

    fn force_thunk(&mut self, thunk: SharedValue) -> Result<SharedValue, RuntimeEvidenceRunError> {
        match thunk.as_ref() {
            RuntimeEvidenceValue::Thunk(thunk) => match thunk.as_ref() {
                RuntimeEvidenceThunk::Expr { body, env } => {
                    let mut env = env.clone();
                    self.eval_expr(*body, &mut env)
                }
            },
            value => Err(RuntimeEvidenceRunError::NotThunk(format_value(value))),
        }
    }

    fn eval_select(
        &mut self,
        base: ExprId,
        name: &str,
        resolution: &Option<SelectResolution>,
        env: &mut Env,
    ) -> Result<SharedValue, RuntimeEvidenceRunError> {
        match resolution {
            Some(SelectResolution::RecordField) | None => {
                let base = self.eval_expr(base, env)?;
                record_field(base.as_ref(), name)
            }
            Some(SelectResolution::Method { instance }) => {
                let base = self.eval_expr(base, env)?;
                let method = self.eval_instance(*instance)?;
                self.apply_value(method, base)
            }
            Some(SelectResolution::TypeclassMethod { .. }) => Err(
                RuntimeEvidenceRunError::UnsupportedExpr("typeclass method select"),
            ),
        }
    }

    fn eval_case(
        &mut self,
        scrutinee: SharedValue,
        arms: &[control_vm::CaseArm],
        env: &Env,
    ) -> Result<SharedValue, RuntimeEvidenceRunError> {
        for arm in arms {
            let mut arm_env = env.clone();
            if bind_pat(&arm.pat, scrutinee.clone(), &mut arm_env).is_err() {
                continue;
            }
            if let Some(guard) = arm.guard {
                let guard = self.eval_expr(guard, &mut arm_env)?;
                if !matches!(guard.as_ref(), RuntimeEvidenceValue::Bool(true)) {
                    continue;
                }
            }
            return self.eval_expr(arm.body, &mut arm_env);
        }
        Err(RuntimeEvidenceRunError::PatternMismatch)
    }

    fn eval_block(
        &mut self,
        block: &Block,
        env: &mut Env,
    ) -> Result<SharedValue, RuntimeEvidenceRunError> {
        let mut last = shared(RuntimeEvidenceValue::Unit);
        for stmt in &block.stmts {
            match stmt {
                Stmt::Let(_, pat, expr) => {
                    let value = self.eval_expr(*expr, env)?;
                    bind_pat(pat, value, env)?;
                }
                Stmt::Expr(expr) => {
                    last = self.eval_expr(*expr, env)?;
                }
                Stmt::Module(_, stmts) => {
                    last = self.eval_block(
                        &Block {
                            stmts: stmts.clone(),
                            tail: None,
                        },
                        env,
                    )?;
                }
            }
        }
        if let Some(tail) = block.tail {
            self.eval_expr(tail, env)
        } else {
            Ok(last)
        }
    }

    fn apply_primitive(
        &mut self,
        op: PrimitiveOp,
        args: &[SharedValue],
    ) -> Result<SharedValue, RuntimeEvidenceRunError> {
        use PrimitiveOp::*;
        let value = match op {
            BoolNot => RuntimeEvidenceValue::Bool(!expect_bool(&args[0])?),
            BoolEq => RuntimeEvidenceValue::Bool(expect_bool(&args[0])? == expect_bool(&args[1])?),
            IntAdd => RuntimeEvidenceValue::Int(expect_int(&args[0])? + expect_int(&args[1])?),
            IntSub => RuntimeEvidenceValue::Int(expect_int(&args[0])? - expect_int(&args[1])?),
            IntMul => RuntimeEvidenceValue::Int(expect_int(&args[0])? * expect_int(&args[1])?),
            IntDiv => {
                let right = expect_int(&args[1])?;
                if right == 0 {
                    return Err(RuntimeEvidenceRunError::DivideByZero);
                }
                RuntimeEvidenceValue::Int(expect_int(&args[0])? / right)
            }
            IntMod => {
                let right = expect_int(&args[1])?;
                if right == 0 {
                    return Err(RuntimeEvidenceRunError::DivideByZero);
                }
                RuntimeEvidenceValue::Int(expect_int(&args[0])? % right)
            }
            IntEq => RuntimeEvidenceValue::Bool(expect_int(&args[0])? == expect_int(&args[1])?),
            IntLt => RuntimeEvidenceValue::Bool(expect_int(&args[0])? < expect_int(&args[1])?),
            IntLe => RuntimeEvidenceValue::Bool(expect_int(&args[0])? <= expect_int(&args[1])?),
            IntGt => RuntimeEvidenceValue::Bool(expect_int(&args[0])? > expect_int(&args[1])?),
            IntGe => RuntimeEvidenceValue::Bool(expect_int(&args[0])? >= expect_int(&args[1])?),
            FloatAdd => {
                RuntimeEvidenceValue::Float(expect_float(&args[0])? + expect_float(&args[1])?)
            }
            FloatSub => {
                RuntimeEvidenceValue::Float(expect_float(&args[0])? - expect_float(&args[1])?)
            }
            FloatMul => {
                RuntimeEvidenceValue::Float(expect_float(&args[0])? * expect_float(&args[1])?)
            }
            FloatDiv => {
                RuntimeEvidenceValue::Float(expect_float(&args[0])? / expect_float(&args[1])?)
            }
            FloatEq => {
                RuntimeEvidenceValue::Bool(expect_float(&args[0])? == expect_float(&args[1])?)
            }
            FloatLt => {
                RuntimeEvidenceValue::Bool(expect_float(&args[0])? < expect_float(&args[1])?)
            }
            FloatLe => {
                RuntimeEvidenceValue::Bool(expect_float(&args[0])? <= expect_float(&args[1])?)
            }
            FloatGt => {
                RuntimeEvidenceValue::Bool(expect_float(&args[0])? > expect_float(&args[1])?)
            }
            FloatGe => {
                RuntimeEvidenceValue::Bool(expect_float(&args[0])? >= expect_float(&args[1])?)
            }
            StringEq => RuntimeEvidenceValue::Bool(expect_str(&args[0])? == expect_str(&args[1])?),
            StringConcat => RuntimeEvidenceValue::Str(format!(
                "{}{}",
                expect_str(&args[0])?,
                expect_str(&args[1])?
            )),
            IntToString => RuntimeEvidenceValue::Str(expect_int(&args[0])?.to_string()),
            FloatToString => RuntimeEvidenceValue::Str(expect_float(&args[0])?.to_string()),
            BoolToString => RuntimeEvidenceValue::Str(expect_bool(&args[0])?.to_string()),
            _ => return Err(RuntimeEvidenceRunError::UnsupportedPrimitive(op)),
        };
        Ok(shared(value))
    }
}

fn bind_pat(pat: &Pat, value: SharedValue, env: &mut Env) -> Result<(), RuntimeEvidenceRunError> {
    match pat {
        Pat::Wild => Ok(()),
        Pat::Var(def) => {
            env.insert(*def, value);
            Ok(())
        }
        Pat::Lit(lit) if lit_matches(lit, value.as_ref()) => Ok(()),
        Pat::Lit(_) => Err(RuntimeEvidenceRunError::PatternMismatch),
        Pat::Tuple(items) => {
            let RuntimeEvidenceValue::Tuple(values) = value.as_ref() else {
                return Err(RuntimeEvidenceRunError::PatternMismatch);
            };
            if items.len() != values.len() {
                return Err(RuntimeEvidenceRunError::PatternMismatch);
            }
            for (pat, value) in items.iter().zip(values) {
                bind_pat(pat, value.clone(), env)?;
            }
            Ok(())
        }
        Pat::PolyVariant(tag, payload_pats) => {
            let RuntimeEvidenceValue::PolyVariant {
                tag: value_tag,
                payloads,
            } = value.as_ref()
            else {
                return Err(RuntimeEvidenceRunError::PatternMismatch);
            };
            if tag != value_tag || payload_pats.len() != payloads.len() {
                return Err(RuntimeEvidenceRunError::PatternMismatch);
            }
            for (pat, value) in payload_pats.iter().zip(payloads) {
                bind_pat(pat, value.clone(), env)?;
            }
            Ok(())
        }
        Pat::Con(def, payload_pats) => {
            let RuntimeEvidenceValue::DataConstructor {
                def: value_def,
                payloads,
            } = value.as_ref()
            else {
                return Err(RuntimeEvidenceRunError::PatternMismatch);
            };
            if def != value_def || payload_pats.len() != payloads.len() {
                return Err(RuntimeEvidenceRunError::PatternMismatch);
            }
            for (pat, value) in payload_pats.iter().zip(payloads) {
                bind_pat(pat, value.clone(), env)?;
            }
            Ok(())
        }
        Pat::As(inner, def) => {
            bind_pat(inner, value.clone(), env)?;
            env.insert(*def, value);
            Ok(())
        }
        Pat::Or(left, right) => {
            let mut left_env = env.clone();
            if bind_pat(left, value.clone(), &mut left_env).is_ok() {
                *env = left_env;
                return Ok(());
            }
            bind_pat(right, value, env)
        }
        Pat::List { .. } => Err(RuntimeEvidenceRunError::UnsupportedPattern("list")),
        Pat::Record { .. } => Err(RuntimeEvidenceRunError::UnsupportedPattern("record")),
        Pat::Ref(_) => Err(RuntimeEvidenceRunError::UnsupportedPattern("ref")),
    }
}

fn value_from_lit(lit: &Lit) -> RuntimeEvidenceValue {
    match lit {
        Lit::Int(value) => RuntimeEvidenceValue::Int(*value),
        Lit::BigInt(value) => RuntimeEvidenceValue::BigInt(value.to_string()),
        Lit::Float(value) => RuntimeEvidenceValue::Float(*value),
        Lit::Str(value) => RuntimeEvidenceValue::Str(value.clone()),
        Lit::Bool(value) => RuntimeEvidenceValue::Bool(*value),
        Lit::Unit => RuntimeEvidenceValue::Unit,
    }
}

fn lit_matches(lit: &Lit, value: &RuntimeEvidenceValue) -> bool {
    match (lit, value) {
        (Lit::Int(left), RuntimeEvidenceValue::Int(right)) => left == right,
        (Lit::BigInt(left), RuntimeEvidenceValue::BigInt(right)) => left.to_string() == *right,
        (Lit::Float(left), RuntimeEvidenceValue::Float(right)) => left == right,
        (Lit::Str(left), RuntimeEvidenceValue::Str(right)) => left == right,
        (Lit::Bool(left), RuntimeEvidenceValue::Bool(right)) => left == right,
        (Lit::Unit, RuntimeEvidenceValue::Unit) => true,
        _ => false,
    }
}

fn expect_int(value: &SharedValue) -> Result<i64, RuntimeEvidenceRunError> {
    match value.as_ref() {
        RuntimeEvidenceValue::Int(value) => Ok(*value),
        value => Err(RuntimeEvidenceRunError::UnsupportedExpr(match value {
            RuntimeEvidenceValue::BigInt(_) => "bigint primitive argument",
            RuntimeEvidenceValue::Float(_) => "float where int expected",
            RuntimeEvidenceValue::Str(_) => "string where int expected",
            RuntimeEvidenceValue::Bool(_) => "bool where int expected",
            _ => "non-int primitive argument",
        })),
    }
}

fn expect_float(value: &SharedValue) -> Result<f64, RuntimeEvidenceRunError> {
    match value.as_ref() {
        RuntimeEvidenceValue::Float(value) => Ok(*value),
        value => Err(RuntimeEvidenceRunError::UnsupportedExpr(match value {
            RuntimeEvidenceValue::Int(_) => "int where float expected",
            _ => "non-float primitive argument",
        })),
    }
}

fn expect_bool(value: &SharedValue) -> Result<bool, RuntimeEvidenceRunError> {
    match value.as_ref() {
        RuntimeEvidenceValue::Bool(value) => Ok(*value),
        _ => Err(RuntimeEvidenceRunError::UnsupportedExpr(
            "non-bool primitive argument",
        )),
    }
}

fn expect_str(value: &SharedValue) -> Result<&str, RuntimeEvidenceRunError> {
    match value.as_ref() {
        RuntimeEvidenceValue::Str(value) => Ok(value),
        _ => Err(RuntimeEvidenceRunError::UnsupportedExpr(
            "non-string primitive argument",
        )),
    }
}

fn record_fields(
    value: &RuntimeEvidenceValue,
) -> Result<Vec<RuntimeEvidenceValueField>, RuntimeEvidenceRunError> {
    match value {
        RuntimeEvidenceValue::Record(fields) => Ok(fields.clone()),
        value => Err(RuntimeEvidenceRunError::NotRecord(format_value(value))),
    }
}

fn record_field(
    value: &RuntimeEvidenceValue,
    name: &str,
) -> Result<SharedValue, RuntimeEvidenceRunError> {
    let fields = record_fields(value)?;
    fields
        .into_iter()
        .find(|field| field.name == name)
        .map(|field| field.value)
        .ok_or_else(|| RuntimeEvidenceRunError::MissingRecordField(name.to_string()))
}

fn shared(value: RuntimeEvidenceValue) -> SharedValue {
    Rc::new(value)
}

fn format_values(values: &[RuntimeEvidenceValue]) -> String {
    let values = values.iter().map(format_value).collect::<Vec<_>>();
    format!("[{}]", values.join(", "))
}

fn format_value(value: &RuntimeEvidenceValue) -> String {
    match value {
        RuntimeEvidenceValue::Int(value) => value.to_string(),
        RuntimeEvidenceValue::BigInt(value) => value.clone(),
        RuntimeEvidenceValue::Float(value) => value.to_string(),
        RuntimeEvidenceValue::Str(value) => format!("{value:?}"),
        RuntimeEvidenceValue::Bool(value) => value.to_string(),
        RuntimeEvidenceValue::Unit => "()".to_string(),
        RuntimeEvidenceValue::Tuple(values) => format_delimited("(", ")", values),
        RuntimeEvidenceValue::Record(fields) => {
            let fields = fields
                .iter()
                .map(|field| format!("{}: {}", field.name, format_value(&field.value)))
                .collect::<Vec<_>>();
            format!("{{{}}}", fields.join(", "))
        }
        RuntimeEvidenceValue::PolyVariant { tag, payloads } => {
            if payloads.is_empty() {
                tag.clone()
            } else {
                format!("{tag}({})", format_shared_values(payloads))
            }
        }
        RuntimeEvidenceValue::DataConstructor { def, payloads } => {
            if payloads.is_empty() {
                format!("<ctor d{}>", def.0)
            } else {
                format!("<ctor d{}>({})", def.0, format_shared_values(payloads))
            }
        }
        RuntimeEvidenceValue::ConstructorFunction { def, .. } => format!("<ctor-fn d{}>", def.0),
        RuntimeEvidenceValue::PrimitiveOp { op, .. } => format!("<primitive {op:?}>"),
        RuntimeEvidenceValue::Closure(_) => "<function>".to_string(),
        RuntimeEvidenceValue::EffectOp { path } => format!("<effect-op {}>", path.join("::")),
        RuntimeEvidenceValue::Thunk(_) => "<thunk>".to_string(),
    }
}

fn format_delimited(open: &str, close: &str, values: &[SharedValue]) -> String {
    let mut out = String::new();
    out.push_str(open);
    out.push_str(&format_shared_values(values));
    if values.len() == 1 && open == "(" {
        out.push(',');
    }
    out.push_str(close);
    out
}

fn format_shared_values(values: &[SharedValue]) -> String {
    values
        .iter()
        .map(|value| format_value(value.as_ref()))
        .collect::<Vec<_>>()
        .join(", ")
}
