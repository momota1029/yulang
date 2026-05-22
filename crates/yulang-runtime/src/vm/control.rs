use super::*;
use crate::ir::RecordSpreadPattern;
use num_bigint::BigInt;
use serde::{Deserialize, Serialize};
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::io;
use std::path::Path;

const CONTROL_VM_ARTIFACT_MAGIC: &[u8; 8] = b"YLCVMIR\0";
pub const CONTROL_VM_ARTIFACT_VERSION: u32 = 8;
const CONTROL_VM_ARTIFACT_HEADER_LEN: usize = CONTROL_VM_ARTIFACT_MAGIC.len() + 4;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
struct ExprId(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
struct ControlSymbolId(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
struct ControlNameId(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
struct ControlLitId(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
struct ControlTypeId(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
struct ControlExprListId(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
struct ControlMatchArmsId(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
struct ControlHandleArmsId(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
struct ControlBlockId(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
struct ControlRecordId(usize);

#[derive(Serialize, Deserialize)]
pub struct ControlVmModule {
    module: ControlModule,
}

impl ControlVmModule {
    pub fn eval_root_expr(&self, index: usize) -> Result<VmResult, VmError> {
        let expr = self
            .module
            .root_exprs
            .get(index)
            .copied()
            .ok_or(VmError::MissingRootExpr(index))?;
        ControlInterpreter::new(&self.module).eval_root_expr(expr)
    }

    pub fn eval_root_expr_profiled(&self, index: usize) -> Result<(VmResult, VmProfile), VmError> {
        let expr = self
            .module
            .root_exprs
            .get(index)
            .copied()
            .ok_or(VmError::MissingRootExpr(index))?;
        let mut interpreter = ControlInterpreter::new(&self.module);
        let result = interpreter.eval_root_expr(expr)?;
        Ok((result, interpreter.profile()))
    }

    pub fn eval_root_expr_with_basic_host_profiled(
        &self,
        index: usize,
        stdout: &mut String,
    ) -> Result<(VmResult, VmProfile), VmError> {
        let expr = self
            .module
            .root_exprs
            .get(index)
            .copied()
            .ok_or(VmError::MissingRootExpr(index))?;
        let mut interpreter = ControlInterpreter::new(&self.module);
        let mut result = interpreter.eval_root_control_result(expr)?;
        loop {
            match result {
                ControlResult::Value(value) => {
                    return Ok((
                        VmResult::Value(export_value(&value, Some(&self.module))?),
                        interpreter.profile(),
                    ));
                }
                ControlResult::Request(request) => {
                    let exported = interpreter.export_request(&request)?;
                    let Some(value) = crate::host::handle_host_request(&exported, stdout) else {
                        return Ok((VmResult::Request(exported), interpreter.profile()));
                    };
                    let value = import_value(&value)?;
                    let resumed = interpreter.resume(request.continuation, value)?;
                    result = interpreter.normalize_root_result(resumed)?;
                }
            }
        }
    }

    pub fn root_count(&self) -> usize {
        self.module.root_exprs.len()
    }

    pub fn write_json_file(&self, path: &Path) -> io::Result<()> {
        let file = std::fs::File::create(path)?;
        serde_json::to_writer(file, self).map_err(io::Error::other)
    }

    pub fn read_json_file(path: &Path) -> io::Result<Self> {
        let file = std::fs::File::open(path)?;
        let mut module: Self = serde_json::from_reader(file).map_err(io::Error::other)?;
        module.module.rebuild_indexes();
        Ok(module)
    }

    pub fn write_artifact_file(&self, path: &Path) -> io::Result<()> {
        std::fs::write(path, self.to_artifact_bytes()?)
    }

    pub fn read_artifact_file(path: &Path) -> io::Result<Self> {
        Self::from_artifact_bytes(&std::fs::read(path)?)
    }

    pub fn to_artifact_bytes(&self) -> io::Result<Vec<u8>> {
        let payload = postcard::to_allocvec(self).map_err(io::Error::other)?;
        let mut bytes = Vec::with_capacity(CONTROL_VM_ARTIFACT_HEADER_LEN + payload.len());
        bytes.extend_from_slice(CONTROL_VM_ARTIFACT_MAGIC);
        bytes.extend_from_slice(&CONTROL_VM_ARTIFACT_VERSION.to_le_bytes());
        bytes.extend_from_slice(&payload);
        Ok(bytes)
    }

    pub fn from_artifact_bytes(bytes: &[u8]) -> io::Result<Self> {
        if bytes.len() < CONTROL_VM_ARTIFACT_HEADER_LEN {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "control VM artifact is shorter than the header",
            ));
        }
        let (magic, rest) = bytes.split_at(CONTROL_VM_ARTIFACT_MAGIC.len());
        if magic != CONTROL_VM_ARTIFACT_MAGIC {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "invalid control VM artifact magic",
            ));
        }
        let (version, payload) = rest.split_at(4);
        let version = u32::from_le_bytes(version.try_into().expect("version header length"));
        if version != CONTROL_VM_ARTIFACT_VERSION {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "unsupported control VM artifact version {version}; expected {CONTROL_VM_ARTIFACT_VERSION}"
                ),
            ));
        }
        let mut module: Self = postcard::from_bytes(payload).map_err(io::Error::other)?;
        module.module.rebuild_indexes();
        Ok(module)
    }
}

pub fn compile_control_vm_module(module: Module) -> Result<ControlVmModule, VmError> {
    check_runtime_invariants(&module, RuntimeStage::BeforeVm).map_err(VmError::Runtime)?;
    let effects = EffectPathResolver::collect(&module);
    let module = erase_module(module, &effects)?;
    Ok(ControlVmModule {
        module: ControlCompiler::compile(module),
    })
}

#[derive(Serialize, Deserialize)]
struct ControlModule {
    symbols: Vec<typed_ir::Path>,
    names: Vec<typed_ir::Name>,
    lits: Vec<typed_ir::Lit>,
    types: Vec<typed_ir::Type>,
    expr_lists: Vec<Vec<ExprId>>,
    match_arms: Vec<Vec<ControlMatchArm>>,
    handle_arms: Vec<Vec<ControlHandleArm>>,
    blocks: Vec<ControlBlock>,
    records: Vec<ControlRecord>,
    exprs: Vec<ControlExpr>,
    bindings: Vec<ControlBinding>,
    #[serde(skip, default)]
    symbol_by_path: HashMap<typed_ir::Path, ControlSymbolId>,
    #[serde(skip, default)]
    binding_by_symbol: Vec<Option<usize>>,
    root_exprs: Vec<ExprId>,
}

impl ControlModule {
    fn rebuild_indexes(&mut self) {
        self.symbol_by_path = self
            .symbols
            .iter()
            .cloned()
            .enumerate()
            .map(|(index, path)| (path, ControlSymbolId(index)))
            .collect();
        self.binding_by_symbol =
            control_binding_index_by_symbol(&self.bindings, self.symbols.len());
    }

    fn symbol_path(&self, symbol: ControlSymbolId) -> &typed_ir::Path {
        &self.symbols[symbol.0]
    }

    fn name(&self, name: ControlNameId) -> &typed_ir::Name {
        &self.names[name.0]
    }

    fn lit(&self, lit: ControlLitId) -> &typed_ir::Lit {
        &self.lits[lit.0]
    }

    fn ty(&self, ty: ControlTypeId) -> &typed_ir::Type {
        &self.types[ty.0]
    }

    fn expr_list(&self, id: ControlExprListId) -> &[ExprId] {
        &self.expr_lists[id.0]
    }

    fn match_arms(&self, id: ControlMatchArmsId) -> &[ControlMatchArm] {
        &self.match_arms[id.0]
    }

    fn handle_arms(&self, id: ControlHandleArmsId) -> &[ControlHandleArm] {
        &self.handle_arms[id.0]
    }

    fn block(&self, id: ControlBlockId) -> &ControlBlock {
        &self.blocks[id.0]
    }

    fn record(&self, id: ControlRecordId) -> &ControlRecord {
        &self.records[id.0]
    }

    fn symbol_for_name(&self, name: &typed_ir::Name) -> ControlSymbolId {
        let path = typed_ir::Path::from_name(name.clone());
        self.symbol_by_path
            .get(&path)
            .copied()
            .expect("compiled control symbol")
    }
}

fn control_binding_index_by_symbol(
    bindings: &[ControlBinding],
    symbol_count: usize,
) -> Vec<Option<usize>> {
    let mut index_by_symbol = vec![None; symbol_count];
    for (index, binding) in bindings.iter().enumerate() {
        index_by_symbol[binding.name.0] = Some(index);
    }
    index_by_symbol
}

#[derive(Serialize, Deserialize)]
struct ControlBinding {
    name: ControlSymbolId,
    body: ExprId,
}

#[derive(Serialize, Deserialize)]
struct ControlExpr {
    kind: ControlExprKind,
}

#[derive(Clone, Copy, Serialize, Deserialize)]
enum ControlExprKind {
    Var(ControlSymbolId),
    EffectOp(ControlSymbolId),
    PrimitiveOp(typed_ir::PrimitiveOp),
    Lit(ControlLitId),
    Lambda {
        param: ControlSymbolId,
        param_forces_thunk_arg: bool,
        body: ExprId,
        result_wraps_thunk: bool,
    },
    Apply {
        callee: ExprId,
        arg: ExprId,
        delay_arg: bool,
    },
    If {
        cond: ExprId,
        then_branch: ExprId,
        else_branch: ExprId,
    },
    Tuple(ControlExprListId),
    Variant {
        tag: ControlNameId,
        value: Option<ExprId>,
    },
    Match {
        scrutinee: ExprId,
        arms: ControlMatchArmsId,
    },
    Block(ControlBlockId),
    Handle {
        body: ExprId,
        arms: ControlHandleArmsId,
        result_wraps_thunk: bool,
    },
    BindHere(ExprId),
    Thunk(ExprId),
    LocalPushId {
        id: EffectIdVar,
        body: ExprId,
    },
    PeekId,
    FindId {
        id: EffectIdRef,
    },
    AddId {
        id: EffectIdRef,
        allowed: ControlTypeId,
        active: bool,
        thunk: ExprId,
    },
    Coerce {
        to: ControlTypeId,
        expr: ExprId,
    },
    Pack(ExprId),
    Select {
        base: ExprId,
        field: ControlNameId,
    },
    Record(ControlRecordId),
}

#[derive(Serialize, Deserialize)]
struct ControlRecord {
    fields: Vec<ControlRecordField>,
    spread: Option<ControlRecordSpread>,
}

#[derive(Clone, Serialize, Deserialize)]
struct ControlRecordField {
    name: typed_ir::Name,
    value: ExprId,
}

#[derive(Clone, Serialize, Deserialize)]
enum ControlRecordSpread {
    Head(ExprId),
    Tail(ExprId),
}

#[derive(Clone, Serialize, Deserialize)]
enum ControlPattern {
    Wildcard,
    Bind {
        name: typed_ir::Name,
    },
    Lit {
        lit: typed_ir::Lit,
    },
    Tuple {
        items: Vec<ControlPattern>,
    },
    List {
        prefix: Vec<ControlPattern>,
        spread: Option<Box<ControlPattern>>,
        suffix: Vec<ControlPattern>,
    },
    Record {
        fields: Vec<ControlRecordPatternField>,
        spread: Option<ControlRecordSpreadPattern>,
    },
    Variant {
        tag: typed_ir::Name,
        value: Option<Box<ControlPattern>>,
    },
    Or {
        left: Box<ControlPattern>,
        right: Box<ControlPattern>,
    },
    As {
        pattern: Box<ControlPattern>,
        name: typed_ir::Name,
    },
}

#[derive(Clone, Serialize, Deserialize)]
struct ControlRecordPatternField {
    name: typed_ir::Name,
    pattern: ControlPattern,
    default: Option<ExprId>,
}

#[derive(Clone, Serialize, Deserialize)]
enum ControlRecordSpreadPattern {
    Head(Box<ControlPattern>),
    Tail(Box<ControlPattern>),
}

#[derive(Clone, Serialize, Deserialize)]
struct ControlMatchArm {
    pattern: ControlPattern,
    guard: Option<ExprId>,
    body: ExprId,
}

#[derive(Clone, Serialize, Deserialize)]
struct ControlHandleArm {
    effect: ControlSymbolId,
    payload: ControlPattern,
    resume: Option<ControlSymbolId>,
    guard: Option<ExprId>,
    body: ExprId,
}

#[derive(Clone, Serialize, Deserialize)]
enum ControlStmt {
    Let {
        pattern: ControlPattern,
        value: ExprId,
    },
    Expr(ExprId),
    Module {
        def: ControlSymbolId,
        body: ExprId,
    },
}

#[derive(Serialize, Deserialize)]
struct ControlBlock {
    stmts: Vec<ControlStmt>,
    tail: Option<ExprId>,
}

struct ControlCompiler {
    symbols: Vec<typed_ir::Path>,
    symbol_by_path: HashMap<typed_ir::Path, ControlSymbolId>,
    names: Vec<typed_ir::Name>,
    name_by_name: HashMap<typed_ir::Name, ControlNameId>,
    lits: Vec<typed_ir::Lit>,
    types: Vec<typed_ir::Type>,
    expr_lists: Vec<Vec<ExprId>>,
    match_arms: Vec<Vec<ControlMatchArm>>,
    handle_arms: Vec<Vec<ControlHandleArm>>,
    blocks: Vec<ControlBlock>,
    records: Vec<ControlRecord>,
    exprs: Vec<ControlExpr>,
}

impl ControlCompiler {
    fn compile(module: Module) -> ControlModule {
        let mut compiler = Self {
            symbols: Vec::new(),
            symbol_by_path: HashMap::new(),
            names: Vec::new(),
            name_by_name: HashMap::new(),
            lits: Vec::new(),
            types: Vec::new(),
            expr_lists: Vec::new(),
            match_arms: Vec::new(),
            handle_arms: Vec::new(),
            blocks: Vec::new(),
            records: Vec::new(),
            exprs: Vec::new(),
        };
        let bindings = module
            .bindings
            .into_iter()
            .map(|binding| ControlBinding {
                name: compiler.intern_path(binding.name),
                body: compiler.expr(binding.body),
            })
            .collect::<Vec<_>>();
        let binding_by_symbol = control_binding_index_by_symbol(&bindings, compiler.symbols.len());
        let root_exprs = module
            .root_exprs
            .into_iter()
            .map(|expr| compiler.expr(expr))
            .collect();
        ControlModule {
            symbols: compiler.symbols,
            names: compiler.names,
            lits: compiler.lits,
            types: compiler.types,
            expr_lists: compiler.expr_lists,
            match_arms: compiler.match_arms,
            handle_arms: compiler.handle_arms,
            blocks: compiler.blocks,
            records: compiler.records,
            exprs: compiler.exprs,
            bindings,
            symbol_by_path: compiler.symbol_by_path,
            binding_by_symbol,
            root_exprs,
        }
    }

    fn intern_path(&mut self, path: typed_ir::Path) -> ControlSymbolId {
        if let Some(symbol) = self.symbol_by_path.get(&path).copied() {
            return symbol;
        }
        let symbol = ControlSymbolId(self.symbols.len());
        self.symbols.push(path.clone());
        self.symbol_by_path.insert(path, symbol);
        symbol
    }

    fn intern_name_path(&mut self, name: &typed_ir::Name) -> ControlSymbolId {
        self.intern_path(typed_ir::Path::from_name(name.clone()))
    }

    fn intern_name(&mut self, name: typed_ir::Name) -> ControlNameId {
        if let Some(id) = self.name_by_name.get(&name).copied() {
            return id;
        }
        let id = ControlNameId(self.names.len());
        self.names.push(name.clone());
        self.name_by_name.insert(name, id);
        id
    }

    fn push_lit(&mut self, lit: typed_ir::Lit) -> ControlLitId {
        let id = ControlLitId(self.lits.len());
        self.lits.push(lit);
        id
    }

    fn push_type(&mut self, ty: typed_ir::Type) -> ControlTypeId {
        let id = ControlTypeId(self.types.len());
        self.types.push(ty);
        id
    }

    fn push_expr_list(&mut self, exprs: Vec<ExprId>) -> ControlExprListId {
        let id = ControlExprListId(self.expr_lists.len());
        self.expr_lists.push(exprs);
        id
    }

    fn push_match_arms(&mut self, arms: Vec<ControlMatchArm>) -> ControlMatchArmsId {
        let id = ControlMatchArmsId(self.match_arms.len());
        self.match_arms.push(arms);
        id
    }

    fn push_handle_arms(&mut self, arms: Vec<ControlHandleArm>) -> ControlHandleArmsId {
        let id = ControlHandleArmsId(self.handle_arms.len());
        self.handle_arms.push(arms);
        id
    }

    fn push_block(&mut self, block: ControlBlock) -> ControlBlockId {
        let id = ControlBlockId(self.blocks.len());
        self.blocks.push(block);
        id
    }

    fn push_record(&mut self, record: ControlRecord) -> ControlRecordId {
        let id = ControlRecordId(self.records.len());
        self.records.push(record);
        id
    }

    fn pattern(&mut self, pattern: Pattern) -> ControlPattern {
        match pattern {
            Pattern::Wildcard { .. } => ControlPattern::Wildcard,
            Pattern::Bind { name, .. } => {
                self.intern_name_path(&name);
                ControlPattern::Bind { name }
            }
            Pattern::Lit { lit, .. } => ControlPattern::Lit { lit },
            Pattern::Tuple { items, .. } => ControlPattern::Tuple {
                items: items.into_iter().map(|item| self.pattern(item)).collect(),
            },
            Pattern::List {
                prefix,
                spread,
                suffix,
                ..
            } => ControlPattern::List {
                prefix: prefix.into_iter().map(|item| self.pattern(item)).collect(),
                spread: spread.map(|item| Box::new(self.pattern(*item))),
                suffix: suffix.into_iter().map(|item| self.pattern(item)).collect(),
            },
            Pattern::Record { fields, spread, .. } => ControlPattern::Record {
                fields: fields
                    .into_iter()
                    .map(|field| ControlRecordPatternField {
                        name: field.name,
                        pattern: self.pattern(field.pattern),
                        default: field.default.map(|default| self.expr(default)),
                    })
                    .collect(),
                spread: spread.map(|spread| match spread {
                    RecordSpreadPattern::Head(pattern) => {
                        ControlRecordSpreadPattern::Head(Box::new(self.pattern(*pattern)))
                    }
                    RecordSpreadPattern::Tail(pattern) => {
                        ControlRecordSpreadPattern::Tail(Box::new(self.pattern(*pattern)))
                    }
                }),
            },
            Pattern::Variant { tag, value, .. } => ControlPattern::Variant {
                tag,
                value: value.map(|value| Box::new(self.pattern(*value))),
            },
            Pattern::Or { left, right, .. } => ControlPattern::Or {
                left: Box::new(self.pattern(*left)),
                right: Box::new(self.pattern(*right)),
            },
            Pattern::As { pattern, name, .. } => {
                self.intern_name_path(&name);
                ControlPattern::As {
                    pattern: Box::new(self.pattern(*pattern)),
                    name,
                }
            }
        }
    }

    fn expr(&mut self, expr: Expr) -> ExprId {
        let Expr { ty, kind } = expr;
        let kind = match kind {
            ExprKind::Var(path) => ControlExprKind::Var(self.intern_path(path)),
            ExprKind::EffectOp(path) => ControlExprKind::EffectOp(self.intern_path(path)),
            ExprKind::PrimitiveOp(op) => ControlExprKind::PrimitiveOp(op),
            ExprKind::Lit(lit) => ControlExprKind::Lit(self.push_lit(lit)),
            ExprKind::Lambda { param, body, .. } => {
                let (param_forces_thunk_arg, result_wraps_thunk) =
                    control_lambda_shape(&ty, &body.ty);
                let param = self.intern_name_path(&param);
                ControlExprKind::Lambda {
                    param,
                    param_forces_thunk_arg,
                    body: self.expr(*body),
                    result_wraps_thunk,
                }
            }
            ExprKind::Apply { callee, arg, .. } => {
                let delay_arg = expects_thunk_arg(&callee.ty);
                ControlExprKind::Apply {
                    callee: self.expr(*callee),
                    arg: self.expr(*arg),
                    delay_arg,
                }
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => ControlExprKind::If {
                cond: self.expr(*cond),
                then_branch: self.expr(*then_branch),
                else_branch: self.expr(*else_branch),
            },
            ExprKind::Tuple(items) => {
                let items = items.into_iter().map(|item| self.expr(item)).collect();
                ControlExprKind::Tuple(self.push_expr_list(items))
            }
            ExprKind::Variant { tag, value } => ControlExprKind::Variant {
                tag: self.intern_name(tag),
                value: value.map(|value| self.expr(*value)),
            },
            ExprKind::Match {
                scrutinee, arms, ..
            } => {
                let scrutinee = self.expr(*scrutinee);
                let arms = arms
                    .into_iter()
                    .map(|arm| ControlMatchArm {
                        pattern: self.pattern(arm.pattern),
                        guard: arm.guard.map(|guard| self.expr(guard)),
                        body: self.expr(arm.body),
                    })
                    .collect();
                ControlExprKind::Match {
                    scrutinee,
                    arms: self.push_match_arms(arms),
                }
            }
            ExprKind::Block { stmts, tail } => {
                let stmts = stmts.into_iter().map(|stmt| self.stmt(stmt)).collect();
                let tail = tail.map(|tail| self.expr(*tail));
                ControlExprKind::Block(self.push_block(ControlBlock { stmts, tail }))
            }
            ExprKind::Handle {
                body,
                arms,
                evidence,
                ..
            } => {
                let body = self.expr(*body);
                let arms = arms
                    .into_iter()
                    .map(|arm| ControlHandleArm {
                        effect: self.intern_path(arm.effect),
                        payload: self.pattern(arm.payload),
                        resume: arm.resume.map(|resume| self.intern_name_path(&resume.name)),
                        guard: arm.guard.map(|guard| self.expr(guard)),
                        body: self.expr(arm.body),
                    })
                    .collect();
                ControlExprKind::Handle {
                    body,
                    arms: self.push_handle_arms(arms),
                    result_wraps_thunk: type_wraps_thunk(&Type::core(evidence.result)),
                }
            }
            ExprKind::BindHere { expr } => ControlExprKind::BindHere(self.expr(*expr)),
            ExprKind::Thunk { expr, .. } => ControlExprKind::Thunk(self.expr(*expr)),
            ExprKind::LocalPushId { id, body } => ControlExprKind::LocalPushId {
                id,
                body: self.expr(*body),
            },
            ExprKind::PeekId => ControlExprKind::PeekId,
            ExprKind::FindId { id } => ControlExprKind::FindId { id },
            ExprKind::AddId {
                id,
                allowed,
                active,
                thunk,
            } => ControlExprKind::AddId {
                id,
                allowed: self.push_type(allowed),
                active,
                thunk: self.expr(*thunk),
            },
            ExprKind::Coerce { to, expr, .. } => ControlExprKind::Coerce {
                to: self.push_type(to),
                expr: self.expr(*expr),
            },
            ExprKind::Pack { expr, .. } => ControlExprKind::Pack(self.expr(*expr)),
            ExprKind::Select { base, field } => ControlExprKind::Select {
                base: self.expr(*base),
                field: self.intern_name(field),
            },
            ExprKind::Record { fields, spread } => {
                let fields = fields
                    .into_iter()
                    .map(|field| ControlRecordField {
                        name: field.name,
                        value: self.expr(field.value),
                    })
                    .collect();
                let spread = spread.map(|spread| match spread {
                    RecordSpreadExpr::Head(expr) => ControlRecordSpread::Head(self.expr(*expr)),
                    RecordSpreadExpr::Tail(expr) => ControlRecordSpread::Tail(self.expr(*expr)),
                });
                ControlExprKind::Record(self.push_record(ControlRecord { fields, spread }))
            }
        };
        let id = ExprId(self.exprs.len());
        self.exprs.push(ControlExpr { kind });
        id
    }

    fn stmt(&mut self, stmt: Stmt) -> ControlStmt {
        match stmt {
            Stmt::Let { pattern, value } => ControlStmt::Let {
                pattern: self.pattern(pattern),
                value: self.expr(value),
            },
            Stmt::Expr(expr) => ControlStmt::Expr(self.expr(expr)),
            Stmt::Module { def, body } => ControlStmt::Module {
                def: self.intern_path(def),
                body: self.expr(body),
            },
        }
    }
}

#[derive(Clone)]
enum ControlValue {
    Int(ControlInt),
    Float(String),
    String(StringTree),
    Bytes(BytesTree),
    Path(Rc<PathBuf>),
    Bool(bool),
    Unit,
    List(ListTree<Rc<ControlValue>>),
    Tuple(Vec<ControlValue>),
    Record(BTreeMap<typed_ir::Name, ControlValue>),
    Variant {
        tag: typed_ir::Name,
        value: Option<Box<ControlValue>>,
    },
    EffectOp(ControlSymbolId),
    PrimitiveOp(ControlHeap<ControlPrimitive>),
    Resume(ControlHeap<ControlResume>),
    Closure(ControlHeap<ControlClosure>),
    Thunk(ControlHeap<ControlThunk>),
    EffectId(u64),
}

#[derive(Clone)]
#[repr(transparent)]
struct ControlHeap<T>(Rc<T>);

impl<T> ControlHeap<T> {
    #[inline]
    fn new(value: T) -> Self {
        Self(Rc::new(value))
    }

    #[inline]
    fn try_unwrap(self) -> Result<T, Self> {
        Rc::try_unwrap(self.0).map_err(Self)
    }
}

impl<T> std::ops::Deref for ControlHeap<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone)]
enum ControlInt {
    Small(i64),
    Big(Box<BigInt>),
}

impl ControlInt {
    fn from_text(value: String) -> Result<Self, VmError> {
        if let Ok(value) = value.parse() {
            return Ok(Self::Small(value));
        }
        value
            .parse()
            .map(|value| Self::Big(Box::new(value)))
            .map_err(|_| VmError::ExpectedInt(VmValue::Int(value)))
    }

    fn from_lit(value: &str) -> Self {
        Self::from_text(value.to_owned()).expect("typed int literal should parse")
    }

    fn to_vm_string(&self) -> String {
        match self {
            Self::Small(value) => value.to_string(),
            Self::Big(value) => value.to_string(),
        }
    }

    fn to_float_string(&self) -> String {
        match self {
            Self::Small(value) => format!("{value}.0"),
            Self::Big(value) => format!("{value}.0"),
        }
    }

    fn as_i64(&self) -> Result<i64, VmError> {
        match self {
            Self::Small(value) => Ok(*value),
            Self::Big(value) => value
                .to_string()
                .parse()
                .map_err(|_| VmError::ExpectedInt(VmValue::Int(value.to_string()))),
        }
    }

    fn add(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Small(left), Self::Small(right)) => left
                .checked_add(*right)
                .map(Self::Small)
                .unwrap_or_else(|| Self::normalize(BigInt::from(*left) + BigInt::from(*right))),
            _ => Self::normalize(self.to_bigint() + other.to_bigint()),
        }
    }

    fn sub(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Small(left), Self::Small(right)) => left
                .checked_sub(*right)
                .map(Self::Small)
                .unwrap_or_else(|| Self::normalize(BigInt::from(*left) - BigInt::from(*right))),
            _ => Self::normalize(self.to_bigint() - other.to_bigint()),
        }
    }

    fn mul(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Small(left), Self::Small(right)) => left
                .checked_mul(*right)
                .map(Self::Small)
                .unwrap_or_else(|| Self::normalize(BigInt::from(*left) * BigInt::from(*right))),
            _ => Self::normalize(self.to_bigint() * other.to_bigint()),
        }
    }

    fn div(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Small(left), Self::Small(right)) => left
                .checked_div(*right)
                .map(Self::Small)
                .unwrap_or_else(|| Self::normalize(BigInt::from(*left) / BigInt::from(*right))),
            _ => Self::normalize(self.to_bigint() / other.to_bigint()),
        }
    }

    fn rem(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Small(left), Self::Small(right)) => left
                .checked_rem(*right)
                .map(Self::Small)
                .unwrap_or_else(|| Self::normalize(BigInt::from(*left) % BigInt::from(*right))),
            _ => Self::normalize(self.to_bigint() % other.to_bigint()),
        }
    }

    fn to_bigint(&self) -> BigInt {
        match self {
            Self::Small(value) => BigInt::from(*value),
            Self::Big(value) => (**value).clone(),
        }
    }

    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::Small(left), Self::Small(right)) => left.cmp(right),
            _ => self.to_bigint().cmp(&other.to_bigint()),
        }
    }

    fn normalize(value: BigInt) -> Self {
        value
            .to_string()
            .parse()
            .map(Self::Small)
            .unwrap_or_else(|_| Self::Big(Box::new(value)))
    }
}

impl PartialEq for ControlInt {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}

impl Eq for ControlInt {}

#[derive(Clone)]
struct ControlPrimitive {
    op: typed_ir::PrimitiveOp,
    args: Vec<ControlValue>,
}

#[derive(Clone)]
struct ControlClosure {
    param: ControlSymbolId,
    param_forces_thunk_arg: bool,
    body: ExprId,
    result_wraps_thunk: bool,
    env: ControlEnv,
    guard_stack: GuardStack,
    self_name: Option<ControlSymbolId>,
}

#[derive(Clone)]
struct ControlThunk {
    body: ControlThunkBody,
    env: ControlEnv,
    guard_stack: GuardStack,
    blocked: Vec<BlockedEffect>,
}

#[derive(Clone)]
enum ControlThunkBody {
    Value(ControlValue),
    Expr(ExprId),
    Emit {
        effect: ControlSymbolId,
        payload: ControlValue,
    },
}

#[derive(Clone)]
struct ControlResume {
    continuation: ControlContinuation,
}

#[derive(Clone, Default)]
struct ControlContinuation {
    frames: VecDeque<ControlFrame>,
    guard_stack: GuardStack,
}

#[derive(Clone)]
struct ControlRequest {
    effect: ControlSymbolId,
    payload: ControlValue,
    continuation: ControlContinuation,
    blocked_id: Option<u64>,
    blocked_ids: Vec<u64>,
}

enum ControlResult {
    Value(ControlValue),
    Request(ControlRequest),
}

#[derive(Clone)]
enum ControlFrame {
    BindHere,
    ApplyCallee {
        arg: ExprId,
        env: ControlEnv,
        delay_arg: bool,
    },
    ApplyArg {
        callee: ControlValue,
    },
    If {
        then_branch: ExprId,
        else_branch: ExprId,
        env: ControlEnv,
    },
    Tuple {
        done: Vec<ControlValue>,
        items: ControlExprListId,
        next_index: usize,
        env: ControlEnv,
    },
    Select {
        field: typed_ir::Name,
    },
    Match {
        arms: ControlMatchArmsId,
        env: ControlEnv,
    },
    Variant {
        tag: ControlNameId,
    },
    BlockLet {
        block: ControlBlockId,
        stmt_index: usize,
        env: ControlEnv,
    },
    BlockExpr {
        block: ControlBlockId,
        next_index: usize,
        env: ControlEnv,
    },
    Handle {
        id: u64,
        arms: ControlHandleArmsId,
        env: ControlEnv,
        guard_stack: GuardStack,
        result_wraps_thunk: bool,
    },
    HandleGuard {
        id: u64,
        request: ControlRequest,
        outer: ControlContinuation,
        handler_guard_stack: GuardStack,
        arms: ControlHandleArmsId,
        next_arm_index: usize,
        env: ControlEnv,
        arm_env: ControlEnv,
        body: ExprId,
        result_wraps_thunk: bool,
    },
    LocalPushId {
        parent: GuardStack,
    },
    BlockedEffects {
        blocked: Vec<BlockedEffect>,
        active: bool,
    },
    Coerce {
        to: typed_ir::Type,
    },
    WrapThunkResult,
}

#[derive(Clone, Default)]
struct ControlEnv {
    slots: Rc<Vec<Option<ControlValue>>>,
}

impl ControlEnv {
    fn new() -> Self {
        Self {
            slots: Rc::new(Vec::new()),
        }
    }

    fn get(&self, symbol: ControlSymbolId) -> Option<&ControlValue> {
        self.slots.get(symbol.0).and_then(Option::as_ref)
    }

    fn insert(&mut self, symbol: ControlSymbolId, value: ControlValue) {
        let slots = Rc::make_mut(&mut self.slots);
        if slots.len() <= symbol.0 {
            slots.resize_with(symbol.0 + 1, || None);
        }
        slots[symbol.0] = Some(value);
    }
}

struct ControlInterpreter<'m> {
    module: &'m ControlModule,
    next_guard_id: u64,
    guard_stack: GuardStack,
    eval_depth: usize,
    profile: VmProfile,
}

impl<'m> ControlInterpreter<'m> {
    fn new(module: &'m ControlModule) -> Self {
        Self {
            module,
            next_guard_id: 0,
            guard_stack: GuardStack::default(),
            eval_depth: 0,
            profile: VmProfile::default(),
        }
    }

    fn profile(&self) -> VmProfile {
        self.profile
    }

    fn expr(&self, id: ExprId) -> &ControlExpr {
        &self.module.exprs[id.0]
    }

    fn eval_root_expr(&mut self, expr: ExprId) -> Result<VmResult, VmError> {
        let result = self.eval_root_control_result(expr)?;
        self.export_result(result)
    }

    fn eval_root_control_result(&mut self, expr: ExprId) -> Result<ControlResult, VmError> {
        let result = self.eval_expr(expr, &ControlEnv::new())?;
        self.normalize_root_result(result)
    }

    fn normalize_root_result(&mut self, result: ControlResult) -> Result<ControlResult, VmError> {
        let mut result = result;
        loop {
            result = match result {
                ControlResult::Value(ControlValue::Thunk(thunk)) => {
                    self.bind_here(ControlValue::Thunk(thunk))?
                }
                ControlResult::Request(request) => match self.propagate_request(request)? {
                    ControlResult::Request(request) => return Ok(ControlResult::Request(request)),
                    result => result,
                },
                result => return Ok(result),
            };
        }
    }

    fn export_result(&self, result: ControlResult) -> Result<VmResult, VmError> {
        match result {
            ControlResult::Value(value) => {
                Ok(VmResult::Value(export_value(&value, Some(self.module))?))
            }
            ControlResult::Request(request) => {
                Ok(VmResult::Request(self.export_request(&request)?))
            }
        }
    }

    fn export_request(&self, request: &ControlRequest) -> Result<VmRequest, VmError> {
        Ok(VmRequest {
            effect: self.module.symbol_path(request.effect).clone(),
            payload: export_value(&request.payload, Some(self.module))?,
            continuation: VmContinuation {
                frames: Vec::new(),
                guard_stack: GuardStack::default(),
                blocked_ids: request.blocked_ids.clone(),
            },
            blocked_id: request.blocked_id,
        })
    }

    fn eval_expr(&mut self, expr: ExprId, env: &ControlEnv) -> Result<ControlResult, VmError> {
        self.profile.eval_expr_calls += 1;
        self.eval_depth += 1;
        self.profile.max_eval_depth = self.profile.max_eval_depth.max(self.eval_depth);
        let result = self.eval_expr_inner(expr, env);
        self.eval_depth -= 1;
        result
    }

    fn eval_expr_inner(
        &mut self,
        expr: ExprId,
        env: &ControlEnv,
    ) -> Result<ControlResult, VmError> {
        let kind = self.expr(expr).kind;
        match kind {
            ControlExprKind::Var(path) => self.eval_var(path, env),
            ControlExprKind::EffectOp(path) => {
                Ok(ControlResult::Value(ControlValue::EffectOp(path)))
            }
            ControlExprKind::PrimitiveOp(typed_ir::PrimitiveOp::YadaYada) => Err(VmError::YadaYada),
            ControlExprKind::PrimitiveOp(op) => Ok(ControlResult::Value(
                ControlValue::PrimitiveOp(ControlHeap::new(ControlPrimitive {
                    op,
                    args: Vec::new(),
                })),
            )),
            ControlExprKind::Lit(lit) => Ok(ControlResult::Value(control_value_from_lit(
                self.module.lit(lit),
            ))),
            ControlExprKind::Lambda {
                param,
                param_forces_thunk_arg,
                body,
                result_wraps_thunk,
            } => Ok(ControlResult::Value(ControlValue::Closure(
                ControlHeap::new(ControlClosure {
                    param,
                    param_forces_thunk_arg,
                    body,
                    result_wraps_thunk,
                    env: env.clone(),
                    guard_stack: self.guard_stack.clone(),
                    self_name: None,
                }),
            ))),
            ControlExprKind::Apply {
                callee,
                arg,
                delay_arg,
            } => match self.eval_expr(callee, env)? {
                ControlResult::Value(callee) => {
                    self.continue_apply_arg(callee, arg, env, delay_arg)
                }
                ControlResult::Request(request) => Ok(ControlResult::Request(push_frame(
                    request,
                    ControlFrame::ApplyCallee {
                        arg,
                        env: env.clone(),
                        delay_arg,
                    },
                ))),
            },
            ControlExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let result = self.eval_expr(cond, env)?;
                self.continue_if_result(result, then_branch, else_branch, env)
            }
            ControlExprKind::Tuple(items) => self.eval_tuple(Vec::new(), items, 0, env.clone()),
            ControlExprKind::Variant { tag, value } => match value {
                Some(value) => {
                    let result = self.eval_expr(value, env)?;
                    let result = self.force_value_result(result)?;
                    self.continue_variant_value(tag, result)
                }
                None => Ok(ControlResult::Value(ControlValue::Variant {
                    tag: self.module.name(tag).clone(),
                    value: None,
                })),
            },
            ControlExprKind::Match { scrutinee, arms } => match self.eval_expr(scrutinee, env)? {
                ControlResult::Value(value) => self.eval_match(value, arms, env),
                ControlResult::Request(request) => Ok(ControlResult::Request(push_frame(
                    request,
                    ControlFrame::Match {
                        arms,
                        env: env.clone(),
                    },
                ))),
            },
            ControlExprKind::Block(block) => self.eval_block(block, 0, env.clone()),
            ControlExprKind::Handle {
                body,
                arms,
                result_wraps_thunk,
            } => self.eval_handle(body, arms, result_wraps_thunk, env),
            ControlExprKind::BindHere(expr) => match self.eval_expr(expr, env)? {
                ControlResult::Value(value) => self.bind_here(value),
                ControlResult::Request(request) => Ok(ControlResult::Request(push_frame(
                    request,
                    ControlFrame::BindHere,
                ))),
            },
            ControlExprKind::Thunk(expr) => Ok(ControlResult::Value(ControlValue::Thunk(
                ControlHeap::new(ControlThunk {
                    body: ControlThunkBody::Expr(expr),
                    env: env.clone(),
                    guard_stack: self.guard_stack.clone(),
                    blocked: Vec::new(),
                }),
            ))),
            ControlExprKind::LocalPushId { id, body } => {
                let guard_id = self.fresh_guard_id();
                let parent = self.guard_stack.clone();
                self.guard_stack = parent.push(GuardEntry {
                    var: id,
                    id: guard_id,
                });
                let result = self.eval_expr(body, env);
                self.guard_stack = parent.clone();
                match result? {
                    ControlResult::Request(request) => Ok(ControlResult::Request(push_frame(
                        request,
                        ControlFrame::LocalPushId { parent },
                    ))),
                    value => Ok(value),
                }
            }
            ControlExprKind::PeekId => {
                let id = self.guard_stack.peek().ok_or(VmError::UnsupportedFindId)?;
                Ok(ControlResult::Value(ControlValue::EffectId(id)))
            }
            ControlExprKind::FindId { id } => Ok(ControlResult::Value(ControlValue::Bool(
                self.find_effect_id(id)?,
            ))),
            ControlExprKind::AddId {
                id,
                allowed,
                active,
                thunk,
            } => {
                let id = self.eval_effect_id(id)?;
                let result = self.eval_expr(thunk, env)?;
                let ControlResult::Value(ControlValue::Thunk(thunk)) = result else {
                    return Ok(match result {
                        ControlResult::Request(request) => {
                            let blocked = [BlockedEffect {
                                guard_id: id,
                                allowed: self.module.ty(allowed).clone(),
                                active,
                            }];
                            let request = if active {
                                mark_control_request_with_active_blocked(
                                    self.module,
                                    request,
                                    &blocked,
                                )
                            } else {
                                mark_control_request_with_blocked(self.module, request, &blocked)
                            };
                            ControlResult::Request(request)
                        }
                        other => other,
                    });
                };
                let mut thunk = (*thunk).clone();
                thunk.blocked.push(BlockedEffect {
                    guard_id: id,
                    allowed: self.module.ty(allowed).clone(),
                    active,
                });
                Ok(ControlResult::Value(ControlValue::Thunk(ControlHeap::new(
                    thunk,
                ))))
            }
            ControlExprKind::Coerce { to, expr } => match self.eval_expr(expr, env)? {
                ControlResult::Value(value) => Ok(ControlResult::Value(control_cast_value(
                    value,
                    self.module.ty(to),
                ))),
                ControlResult::Request(request) => Ok(ControlResult::Request(push_frame(
                    request,
                    ControlFrame::Coerce {
                        to: self.module.ty(to).clone(),
                    },
                ))),
            },
            ControlExprKind::Pack(expr) => self.eval_expr(expr, env),
            ControlExprKind::Select { base, field } => match self.eval_expr(base, env)? {
                ControlResult::Value(value) => self.select_field(value, self.module.name(field)),
                ControlResult::Request(request) => Ok(ControlResult::Request(push_frame(
                    request,
                    ControlFrame::Select {
                        field: self.module.name(field).clone(),
                    },
                ))),
            },
            ControlExprKind::Record(record) => self.eval_record(record, env),
        }
    }

    fn eval_var(
        &mut self,
        path: ControlSymbolId,
        env: &ControlEnv,
    ) -> Result<ControlResult, VmError> {
        if let Some(value) = env.get(path) {
            return Ok(ControlResult::Value(value.clone()));
        }
        if let Some(index) = self
            .module
            .binding_by_symbol
            .get(path.0)
            .and_then(|index| *index)
        {
            return self.eval_expr(self.module.bindings[index].body, &ControlEnv::new());
        }
        let path_ref = self.module.symbol_path(path);
        if path_ref.segments.len() > 1 {
            return Ok(ControlResult::Value(ControlValue::EffectOp(path)));
        }
        Err(VmError::UnboundVariable(path_ref.clone()))
    }

    fn continue_if_result(
        &mut self,
        result: ControlResult,
        then_branch: ExprId,
        else_branch: ExprId,
        env: &ControlEnv,
    ) -> Result<ControlResult, VmError> {
        match result {
            ControlResult::Value(ControlValue::Thunk(thunk)) => {
                match self.bind_here(ControlValue::Thunk(thunk))? {
                    ControlResult::Value(value) => {
                        self.continue_if_value(value, then_branch, else_branch, env)
                    }
                    ControlResult::Request(request) => Ok(ControlResult::Request(push_frame(
                        request,
                        ControlFrame::If {
                            then_branch,
                            else_branch,
                            env: env.clone(),
                        },
                    ))),
                }
            }
            ControlResult::Value(value) => {
                self.continue_if_value(value, then_branch, else_branch, env)
            }
            ControlResult::Request(request) => Ok(ControlResult::Request(push_frame(
                request,
                ControlFrame::If {
                    then_branch,
                    else_branch,
                    env: env.clone(),
                },
            ))),
        }
    }

    fn continue_if_value(
        &mut self,
        value: ControlValue,
        then_branch: ExprId,
        else_branch: ExprId,
        env: &ControlEnv,
    ) -> Result<ControlResult, VmError> {
        match value {
            ControlValue::Bool(true) => self.eval_expr(then_branch, env),
            ControlValue::Bool(false) => self.eval_expr(else_branch, env),
            other => Err(VmError::ExpectedBool(export_value_lossy(
                &other,
                Some(self.module),
            ))),
        }
    }

    fn continue_if_value_frame(
        &mut self,
        value: ControlValue,
        then_branch: ExprId,
        else_branch: ExprId,
        env: ControlEnv,
    ) -> Result<ControlResult, VmError> {
        match value {
            ControlValue::Thunk(thunk) => match self.bind_here(ControlValue::Thunk(thunk))? {
                ControlResult::Value(value) => {
                    self.continue_if_value_frame(value, then_branch, else_branch, env)
                }
                ControlResult::Request(request) => Ok(ControlResult::Request(push_frame(
                    request,
                    ControlFrame::If {
                        then_branch,
                        else_branch,
                        env,
                    },
                ))),
            },
            ControlValue::Bool(true) => self.eval_expr(then_branch, &env),
            ControlValue::Bool(false) => self.eval_expr(else_branch, &env),
            other => Err(VmError::ExpectedBool(export_value_lossy(
                &other,
                Some(self.module),
            ))),
        }
    }

    fn eval_value(&mut self, expr: ExprId, env: &ControlEnv) -> Result<ControlValue, VmError> {
        match self.eval_expr(expr, env)? {
            ControlResult::Value(value) => Ok(value),
            ControlResult::Request(request) => Err(VmError::UnexpectedRequest(
                self.module.symbol_path(request.effect).clone(),
            )),
        }
    }

    fn bind_here(&mut self, value: ControlValue) -> Result<ControlResult, VmError> {
        let ControlValue::Thunk(thunk) = value else {
            return Ok(ControlResult::Value(value));
        };
        let parent = self.guard_stack.clone();
        self.guard_stack = thunk.guard_stack.clone();
        let result = match &thunk.body {
            ControlThunkBody::Value(value) => Ok(ControlResult::Value(value.clone())),
            ControlThunkBody::Expr(expr) => match self.eval_expr(*expr, &thunk.env)? {
                ControlResult::Value(ControlValue::Thunk(next)) => {
                    match self.bind_here(ControlValue::Thunk(next))? {
                        ControlResult::Request(request) => Ok(ControlResult::Request(
                            push_thunk_boundary_frame(request, &thunk),
                        )),
                        other => Ok(other),
                    }
                }
                ControlResult::Request(request) => Ok(ControlResult::Request(
                    push_thunk_expr_frames(request, &thunk),
                )),
                other => Ok(other),
            },
            ControlThunkBody::Emit { effect, payload } => {
                Ok(ControlResult::Request(push_thunk_boundary_frame(
                    ControlRequest {
                        effect: *effect,
                        payload: payload.clone(),
                        continuation: ControlContinuation {
                            frames: VecDeque::new(),
                            guard_stack: self.guard_stack.clone(),
                        },
                        blocked_id: None,
                        blocked_ids: Vec::new(),
                    },
                    &thunk,
                )))
            }
        };
        self.guard_stack = parent;
        result
    }

    fn continue_apply_arg(
        &mut self,
        callee: ControlValue,
        arg: ExprId,
        env: &ControlEnv,
        delay_arg: bool,
    ) -> Result<ControlResult, VmError> {
        if matches!(callee, ControlValue::Thunk(_)) {
            return self.force_apply_callee(callee, arg, env.clone(), delay_arg);
        }
        if delay_arg {
            return self.apply(
                callee,
                ControlValue::Thunk(ControlHeap::new(ControlThunk {
                    body: ControlThunkBody::Expr(arg),
                    env: env.clone(),
                    guard_stack: self.guard_stack.clone(),
                    blocked: Vec::new(),
                })),
            );
        }
        match self.eval_expr(arg, env)? {
            ControlResult::Value(arg) => self.apply(callee, arg),
            ControlResult::Request(request) => Ok(ControlResult::Request(push_frame(
                request,
                ControlFrame::ApplyArg { callee },
            ))),
        }
    }

    fn force_apply_callee(
        &mut self,
        callee: ControlValue,
        arg: ExprId,
        env: ControlEnv,
        delay_arg: bool,
    ) -> Result<ControlResult, VmError> {
        match self.bind_here(callee)? {
            ControlResult::Value(callee) => self.continue_apply_arg(callee, arg, &env, delay_arg),
            ControlResult::Request(request) => Ok(ControlResult::Request(push_frame(
                request,
                ControlFrame::ApplyCallee {
                    arg,
                    env,
                    delay_arg,
                },
            ))),
        }
    }

    fn apply(&mut self, callee: ControlValue, arg: ControlValue) -> Result<ControlResult, VmError> {
        match callee {
            ControlValue::Closure(callee) => {
                if callee.param_forces_thunk_arg && matches!(arg, ControlValue::Thunk(_)) {
                    return self.force_apply_arg(ControlValue::Closure(callee), arg);
                }
                let mut env = callee.env.clone();
                if let Some(self_name) = &callee.self_name {
                    env.insert(*self_name, ControlValue::Closure(callee.clone()));
                }
                env.insert(callee.param, arg);
                let parent_guard_stack = self.guard_stack.clone();
                self.guard_stack = parent_guard_stack.overlay_newer(&callee.guard_stack);
                let result = self.eval_expr(callee.body, &env)?;
                self.guard_stack = parent_guard_stack.clone();
                if let ControlResult::Request(request) = result {
                    return Ok(ControlResult::Request(push_frame(
                        request,
                        ControlFrame::LocalPushId {
                            parent: parent_guard_stack,
                        },
                    )));
                }
                Ok(control_wrap_result(result, callee.result_wraps_thunk))
            }
            ControlValue::Resume(resume) => self.resume(resume.continuation.clone(), arg),
            ControlValue::EffectOp(effect) => Ok(ControlResult::Value(ControlValue::Thunk(
                ControlHeap::new(ControlThunk {
                    body: ControlThunkBody::Emit {
                        effect,
                        payload: arg,
                    },
                    env: ControlEnv::new(),
                    guard_stack: self.guard_stack.clone(),
                    blocked: Vec::new(),
                }),
            ))),
            ControlValue::PrimitiveOp(primitive) => {
                if matches!(arg, ControlValue::Thunk(_)) {
                    return self.force_apply_arg(ControlValue::PrimitiveOp(primitive), arg);
                }
                self.apply_primitive(primitive, arg)
            }
            other => Err(VmError::ExpectedClosure(export_value_lossy(
                &other,
                Some(self.module),
            ))),
        }
    }

    fn force_apply_arg(
        &mut self,
        callee: ControlValue,
        arg: ControlValue,
    ) -> Result<ControlResult, VmError> {
        match self.bind_here(arg)? {
            ControlResult::Value(arg) => self.apply(callee, arg),
            ControlResult::Request(request) => Ok(ControlResult::Request(push_frame(
                request,
                ControlFrame::ApplyArg { callee },
            ))),
        }
    }

    fn apply_primitive(
        &mut self,
        primitive: ControlHeap<ControlPrimitive>,
        arg: ControlValue,
    ) -> Result<ControlResult, VmError> {
        let mut primitive = match primitive.try_unwrap() {
            Ok(primitive) => primitive,
            Err(primitive) => (*primitive).clone(),
        };
        primitive.args.push(arg);
        if primitive.args.len() < primitive_arity(primitive.op) {
            return Ok(ControlResult::Value(ControlValue::PrimitiveOp(
                ControlHeap::new(primitive),
            )));
        }
        Ok(ControlResult::Value(control_apply_primitive(
            primitive.op,
            &primitive.args,
        )?))
    }

    fn eval_tuple(
        &mut self,
        mut done: Vec<ControlValue>,
        items: ControlExprListId,
        mut next_index: usize,
        env: ControlEnv,
    ) -> Result<ControlResult, VmError> {
        let exprs = self.module.expr_list(items);
        while let Some(&next) = exprs.get(next_index) {
            next_index += 1;
            let result = self.eval_expr(next, &env)?;
            match self.force_value_result(result)? {
                ControlResult::Value(value) => done.push(value),
                ControlResult::Request(request) => {
                    return Ok(ControlResult::Request(push_frame(
                        request,
                        ControlFrame::Tuple {
                            done,
                            items,
                            next_index,
                            env,
                        },
                    )));
                }
            }
        }
        Ok(ControlResult::Value(ControlValue::Tuple(done)))
    }

    fn force_value_result(&mut self, result: ControlResult) -> Result<ControlResult, VmError> {
        match result {
            ControlResult::Value(ControlValue::Thunk(thunk)) => {
                self.bind_here(ControlValue::Thunk(thunk))
            }
            result => Ok(result),
        }
    }

    fn continue_tuple_item(
        &mut self,
        mut done: Vec<ControlValue>,
        items: ControlExprListId,
        next_index: usize,
        env: ControlEnv,
        value: ControlValue,
    ) -> Result<ControlResult, VmError> {
        match value {
            ControlValue::Thunk(thunk) => match self.bind_here(ControlValue::Thunk(thunk))? {
                ControlResult::Value(value) => {
                    self.continue_tuple_item(done, items, next_index, env, value)
                }
                ControlResult::Request(request) => Ok(ControlResult::Request(push_frame(
                    request,
                    ControlFrame::Tuple {
                        done,
                        items,
                        next_index,
                        env,
                    },
                ))),
            },
            value => {
                done.push(value);
                self.eval_tuple(done, items, next_index, env)
            }
        }
    }

    fn continue_variant_value(
        &mut self,
        tag: ControlNameId,
        result: ControlResult,
    ) -> Result<ControlResult, VmError> {
        match result {
            ControlResult::Value(ControlValue::Thunk(thunk)) => {
                match self.bind_here(ControlValue::Thunk(thunk))? {
                    result @ ControlResult::Value(_) => self.continue_variant_value(tag, result),
                    ControlResult::Request(request) => Ok(ControlResult::Request(push_frame(
                        request,
                        ControlFrame::Variant { tag },
                    ))),
                }
            }
            ControlResult::Value(value) => Ok(ControlResult::Value(ControlValue::Variant {
                tag: self.module.name(tag).clone(),
                value: Some(Box::new(value)),
            })),
            ControlResult::Request(request) => Ok(ControlResult::Request(push_frame(
                request,
                ControlFrame::Variant { tag },
            ))),
        }
    }

    fn eval_record(
        &mut self,
        record: ControlRecordId,
        env: &ControlEnv,
    ) -> Result<ControlResult, VmError> {
        let record = self.module.record(record);
        let mut values = BTreeMap::new();
        if let Some(spread) = &record.spread {
            let spread_expr = match spread {
                ControlRecordSpread::Head(expr) | ControlRecordSpread::Tail(expr) => *expr,
            };
            let ControlValue::Record(base) = self.eval_value(spread_expr, env)? else {
                return Err(VmError::ExpectedRecord(VmValue::Unit));
            };
            values.extend(base);
        }
        for field in &record.fields {
            values.insert(field.name.clone(), self.eval_value(field.value, env)?);
        }
        Ok(ControlResult::Value(ControlValue::Record(values)))
    }

    fn select_field(
        &self,
        value: ControlValue,
        field: &typed_ir::Name,
    ) -> Result<ControlResult, VmError> {
        let ControlValue::Record(fields) = value else {
            return Err(VmError::ExpectedRecord(export_value_lossy(
                &value,
                Some(self.module),
            )));
        };
        fields
            .get(field)
            .cloned()
            .map(ControlResult::Value)
            .ok_or(VmError::PatternMismatch)
    }

    fn eval_match(
        &mut self,
        value: ControlValue,
        arms: ControlMatchArmsId,
        env: &ControlEnv,
    ) -> Result<ControlResult, VmError> {
        let value = match value {
            ControlValue::Thunk(thunk) => match self.bind_here(ControlValue::Thunk(thunk))? {
                ControlResult::Value(value) => value,
                ControlResult::Request(request) => {
                    return Ok(ControlResult::Request(push_frame(
                        request,
                        ControlFrame::Match {
                            arms,
                            env: env.clone(),
                        },
                    )));
                }
            },
            value => value,
        };
        for arm in self.module.match_arms(arms) {
            let mut arm_env = env.clone();
            if self
                .bind_pattern(&arm.pattern, value.clone(), &mut arm_env)
                .is_err()
            {
                continue;
            }
            if let Some(guard) = arm.guard {
                match self.eval_value(guard, &arm_env)? {
                    ControlValue::Bool(true) => {}
                    ControlValue::Bool(false) => continue,
                    other => {
                        return Err(VmError::ExpectedBool(export_value_lossy(
                            &other,
                            Some(self.module),
                        )));
                    }
                }
            }
            return self.eval_expr(arm.body, &arm_env);
        }
        Err(VmError::PatternMismatch)
    }

    fn eval_block(
        &mut self,
        block: ControlBlockId,
        mut stmt_index: usize,
        mut env: ControlEnv,
    ) -> Result<ControlResult, VmError> {
        let block_ref = self.module.block(block);
        while let Some(stmt) = block_ref.stmts.get(stmt_index) {
            match stmt {
                ControlStmt::Let { pattern, value } => match self.eval_expr(*value, &env)? {
                    ControlResult::Value(ControlValue::Thunk(thunk)) => {
                        match self.bind_here(ControlValue::Thunk(thunk))? {
                            ControlResult::Value(mut value) => {
                                value = make_recursive_local_value(self.module, &pattern, value);
                                self.bind_pattern(&pattern, value, &mut env)?;
                            }
                            ControlResult::Request(request) => {
                                return Ok(ControlResult::Request(push_frame(
                                    request,
                                    ControlFrame::BlockLet {
                                        block,
                                        stmt_index,
                                        env,
                                    },
                                )));
                            }
                        }
                    }
                    ControlResult::Value(mut value) => {
                        value = make_recursive_local_value(self.module, &pattern, value);
                        self.bind_pattern(&pattern, value, &mut env)?;
                    }
                    ControlResult::Request(request) => {
                        return Ok(ControlResult::Request(push_frame(
                            request,
                            ControlFrame::BlockLet {
                                block,
                                stmt_index,
                                env,
                            },
                        )));
                    }
                },
                ControlStmt::Expr(expr) => match self.eval_expr(*expr, &env)? {
                    ControlResult::Value(ControlValue::Thunk(thunk)) => {
                        match self.bind_here(ControlValue::Thunk(thunk))? {
                            ControlResult::Value(_) => {}
                            ControlResult::Request(request) => {
                                return Ok(ControlResult::Request(push_frame(
                                    request,
                                    ControlFrame::BlockExpr {
                                        block,
                                        next_index: stmt_index + 1,
                                        env,
                                    },
                                )));
                            }
                        }
                    }
                    ControlResult::Value(_) => {}
                    ControlResult::Request(request) => {
                        return Ok(ControlResult::Request(push_frame(
                            request,
                            ControlFrame::BlockExpr {
                                block,
                                next_index: stmt_index + 1,
                                env,
                            },
                        )));
                    }
                },
                ControlStmt::Module { def, body } => {
                    let value = self.eval_value(*body, &env)?;
                    env.insert(*def, value);
                }
            }
            stmt_index += 1;
        }
        match block_ref.tail {
            Some(tail) => self.eval_expr(tail, &env),
            None => Ok(ControlResult::Value(ControlValue::Unit)),
        }
    }

    fn continue_block_expr(
        &mut self,
        value: ControlValue,
        block: ControlBlockId,
        next_index: usize,
        env: ControlEnv,
    ) -> Result<ControlResult, VmError> {
        match value {
            ControlValue::Thunk(thunk) => match self.bind_here(ControlValue::Thunk(thunk))? {
                ControlResult::Value(_) => self.eval_block(block, next_index, env),
                ControlResult::Request(request) => Ok(ControlResult::Request(push_frame(
                    request,
                    ControlFrame::BlockExpr {
                        block,
                        next_index,
                        env,
                    },
                ))),
            },
            _ => self.eval_block(block, next_index, env),
        }
    }

    fn eval_handle(
        &mut self,
        body: ExprId,
        arms: ControlHandleArmsId,
        result_wraps_thunk: bool,
        env: &ControlEnv,
    ) -> Result<ControlResult, VmError> {
        let id = self.fresh_guard_id();
        let handler_guard_stack = self.guard_stack.clone();
        let result = match self.eval_expr(body, env)? {
            ControlResult::Value(ControlValue::Thunk(thunk)) => {
                self.bind_here(ControlValue::Thunk(thunk))?
            }
            other => other,
        };
        match result {
            ControlResult::Value(value) => self.handle_value(value, arms, env, result_wraps_thunk),
            ControlResult::Request(request) => {
                let request = push_frame(
                    request,
                    ControlFrame::Handle {
                        id,
                        arms,
                        env: env.clone(),
                        guard_stack: handler_guard_stack,
                        result_wraps_thunk,
                    },
                );
                self.propagate_request(request)
            }
        }
    }

    fn handle_value(
        &mut self,
        value: ControlValue,
        arms: ControlHandleArmsId,
        env: &ControlEnv,
        result_wraps_thunk: bool,
    ) -> Result<ControlResult, VmError> {
        for arm in self
            .module
            .handle_arms(arms)
            .iter()
            .filter(|arm| self.module.symbol_path(arm.effect).segments.is_empty())
        {
            let mut arm_env = env.clone();
            if self
                .bind_pattern(&arm.payload, value.clone(), &mut arm_env)
                .is_err()
            {
                continue;
            }
            let result = self.eval_expr(arm.body, &arm_env)?;
            return self.force_handle_result(result, result_wraps_thunk);
        }
        Ok(ControlResult::Value(value))
    }

    fn handle_request(
        &mut self,
        request: ControlRequest,
        id: u64,
        arms: ControlHandleArmsId,
        start_arm_index: usize,
        env: &ControlEnv,
        handler_guard_stack: &GuardStack,
        result_wraps_thunk: bool,
    ) -> Result<ControlResult, VmError> {
        if control_request_is_blocked_by_stack(&request, handler_guard_stack) {
            return Ok(ControlResult::Request(request));
        }
        let arms_slice = self.module.handle_arms(arms);
        let Some((arm_index, arm)) =
            arms_slice
                .iter()
                .enumerate()
                .skip(start_arm_index)
                .find(|(_, arm)| {
                    effect_operation_path_matches(
                        self.module.symbol_path(arm.effect),
                        self.module.symbol_path(request.effect),
                    )
                })
        else {
            return Ok(ControlResult::Request(request));
        };
        let next_arm_index = arm_index + 1;
        let (outer, inner) = split_handle_continuations(&request.continuation, id);
        let mut arm_env = env.clone();
        if let Some(guard) = arm.guard {
            self.bind_pattern(&arm.payload, request.payload.clone(), &mut arm_env)?;
            insert_control_resume(&mut arm_env, arm.resume, inner);
            let previous = std::mem::replace(&mut self.guard_stack, handler_guard_stack.clone());
            let guard_result = self.eval_expr(guard, &arm_env);
            self.guard_stack = previous;
            return match guard_result? {
                ControlResult::Value(guard) => self.continue_handle_guard(
                    guard,
                    request,
                    outer,
                    id,
                    arms,
                    next_arm_index,
                    env.clone(),
                    handler_guard_stack.clone(),
                    arm_env,
                    arm.body,
                    result_wraps_thunk,
                ),
                ControlResult::Request(guard_request) => Ok(ControlResult::Request(push_frame(
                    guard_request,
                    ControlFrame::HandleGuard {
                        id,
                        request,
                        outer,
                        handler_guard_stack: handler_guard_stack.clone(),
                        arms,
                        next_arm_index,
                        env: env.clone(),
                        arm_env,
                        body: arm.body,
                        result_wraps_thunk,
                    },
                ))),
            };
        }
        self.bind_pattern(&arm.payload, request.payload, &mut arm_env)?;
        insert_control_resume(&mut arm_env, arm.resume, inner);
        let previous = std::mem::replace(&mut self.guard_stack, handler_guard_stack.clone());
        let result = self.eval_expr(arm.body, &arm_env);
        self.guard_stack = previous;
        let result = result?;
        self.continue_handle_result(result, outer, result_wraps_thunk)
    }

    #[allow(clippy::too_many_arguments)]
    fn continue_handle_guard(
        &mut self,
        guard: ControlValue,
        request: ControlRequest,
        outer: ControlContinuation,
        id: u64,
        arms: ControlHandleArmsId,
        next_arm_index: usize,
        env: ControlEnv,
        handler_guard_stack: GuardStack,
        arm_env: ControlEnv,
        body: ExprId,
        result_wraps_thunk: bool,
    ) -> Result<ControlResult, VmError> {
        match guard {
            ControlValue::Bool(true) => {
                let previous =
                    std::mem::replace(&mut self.guard_stack, handler_guard_stack.clone());
                let result = self.eval_expr(body, &arm_env);
                self.guard_stack = previous;
                let result = result?;
                self.continue_handle_result(result, outer, result_wraps_thunk)
            }
            ControlValue::Bool(false) => self.handle_request(
                request,
                id,
                arms,
                next_arm_index,
                &env,
                &handler_guard_stack,
                result_wraps_thunk,
            ),
            other => Err(VmError::ExpectedBool(export_value_lossy(
                &other,
                Some(self.module),
            ))),
        }
    }

    fn resume(
        &mut self,
        mut continuation: ControlContinuation,
        mut value: ControlValue,
    ) -> Result<ControlResult, VmError> {
        let previous = std::mem::replace(&mut self.guard_stack, continuation.guard_stack.clone());
        self.profile.max_continuation_frames = self
            .profile
            .max_continuation_frames
            .max(continuation.frames.len());
        let result = loop {
            let Some(frame) = continuation.frames.pop_back() else {
                break Ok(ControlResult::Value(value));
            };
            self.profile.continuation_steps += 1;
            self.profile.max_continuation_frames = self
                .profile
                .max_continuation_frames
                .max(continuation.frames.len());
            match self.apply_frame(frame, &mut continuation, value)? {
                ControlResult::Value(next) => value = next,
                ControlResult::Request(mut request) => {
                    prepend_frames(&mut request.continuation, continuation.frames);
                    break self.propagate_request(request);
                }
            }
        };
        self.guard_stack = previous;
        result
    }

    fn apply_frame(
        &mut self,
        frame: ControlFrame,
        continuation: &mut ControlContinuation,
        value: ControlValue,
    ) -> Result<ControlResult, VmError> {
        match frame {
            ControlFrame::BindHere => self.bind_here(value),
            ControlFrame::ApplyCallee {
                arg,
                env,
                delay_arg,
            } => self.continue_apply_arg(value, arg, &env, delay_arg),
            ControlFrame::ApplyArg { callee } => self.apply(callee, value),
            ControlFrame::If {
                then_branch,
                else_branch,
                env,
            } => self.continue_if_value_frame(value, then_branch, else_branch, env),
            ControlFrame::Tuple {
                done,
                items,
                next_index,
                env,
            } => self.continue_tuple_item(done, items, next_index, env, value),
            ControlFrame::Select { field } => self.select_field(value, &field),
            ControlFrame::Match { arms, env } => self.eval_match(value, arms, &env),
            ControlFrame::Variant { tag } => {
                self.continue_variant_value(tag, ControlResult::Value(value))
            }
            ControlFrame::BlockLet {
                block,
                stmt_index,
                mut env,
            } => {
                let ControlStmt::Let { pattern, .. } = &self.module.block(block).stmts[stmt_index]
                else {
                    return Err(VmError::PatternMismatch);
                };
                self.bind_pattern(&pattern, value, &mut env)?;
                self.eval_block(block, stmt_index + 1, env)
            }
            ControlFrame::BlockExpr {
                block,
                next_index,
                env,
            } => self.continue_block_expr(value, block, next_index, env),
            ControlFrame::Handle {
                id,
                arms,
                env,
                guard_stack,
                result_wraps_thunk,
            } => match value {
                ControlValue::Thunk(thunk) => {
                    let result = self.bind_here(ControlValue::Thunk(thunk))?;
                    continuation.frames.push_back(ControlFrame::Handle {
                        id,
                        arms,
                        env,
                        guard_stack,
                        result_wraps_thunk,
                    });
                    Ok(result)
                }
                value => {
                    continuation.guard_stack = guard_stack;
                    self.handle_value(value, arms, &env, result_wraps_thunk)
                }
            },
            ControlFrame::HandleGuard {
                id,
                request,
                outer,
                handler_guard_stack,
                arms,
                next_arm_index,
                env,
                arm_env,
                body,
                result_wraps_thunk,
            } => self.continue_handle_guard(
                value,
                request,
                outer,
                id,
                arms,
                next_arm_index,
                env,
                handler_guard_stack,
                arm_env,
                body,
                result_wraps_thunk,
            ),
            ControlFrame::LocalPushId { parent } => {
                continuation.guard_stack = parent;
                Ok(ControlResult::Value(value))
            }
            ControlFrame::BlockedEffects { .. } => Ok(ControlResult::Value(value)),
            ControlFrame::Coerce { to } => Ok(ControlResult::Value(control_cast_value(value, &to))),
            ControlFrame::WrapThunkResult => {
                Ok(ControlResult::Value(control_wrap_value(value, true)))
            }
        }
    }

    fn continue_result(
        &mut self,
        result: ControlResult,
        continuation: ControlContinuation,
    ) -> Result<ControlResult, VmError> {
        match result {
            ControlResult::Value(value) => self.resume(continuation, value),
            ControlResult::Request(mut request) => {
                prepend_frames(&mut request.continuation, continuation.frames);
                self.propagate_request(request)
            }
        }
    }

    fn force_handle_result(
        &mut self,
        result: ControlResult,
        result_wraps_thunk: bool,
    ) -> Result<ControlResult, VmError> {
        if result_wraps_thunk {
            return Ok(result);
        }
        match result {
            ControlResult::Value(ControlValue::Thunk(thunk)) => {
                self.bind_here(ControlValue::Thunk(thunk))
            }
            ControlResult::Request(request) => Ok(ControlResult::Request(push_frame(
                request,
                ControlFrame::BindHere,
            ))),
            other => Ok(other),
        }
    }

    fn continue_handle_result(
        &mut self,
        result: ControlResult,
        mut continuation: ControlContinuation,
        result_wraps_thunk: bool,
    ) -> Result<ControlResult, VmError> {
        if result_wraps_thunk {
            return self.continue_result(result, continuation);
        }
        match result {
            ControlResult::Value(ControlValue::Thunk(thunk)) => {
                let result = self.bind_here(ControlValue::Thunk(thunk))?;
                self.continue_result(result, continuation)
            }
            ControlResult::Request(request) => {
                continuation.frames.push_back(ControlFrame::BindHere);
                self.continue_result(ControlResult::Request(request), continuation)
            }
            other => self.continue_result(other, continuation),
        }
    }

    fn propagate_request(&mut self, request: ControlRequest) -> Result<ControlResult, VmError> {
        self.propagate_request_before(request, usize::MAX)
    }

    fn propagate_request_before(
        &mut self,
        mut request: ControlRequest,
        before: usize,
    ) -> Result<ControlResult, VmError> {
        let end = before.min(request.continuation.frames.len());
        let Some(index) = request
            .continuation
            .frames
            .iter()
            .take(end)
            .rposition(|frame| {
                matches!(
                    frame,
                    ControlFrame::Handle { .. } | ControlFrame::BlockedEffects { .. }
                )
            })
        else {
            return Ok(ControlResult::Request(request));
        };
        if let ControlFrame::BlockedEffects { blocked, active } =
            request.continuation.frames[index].clone()
        {
            request.continuation.frames.remove(index);
            request = if active {
                mark_control_request_with_active_blocked(self.module, request, &blocked)
            } else {
                mark_control_request_with_blocked(self.module, request, &blocked)
            };
            return self.propagate_request(request);
        }
        let ControlFrame::Handle {
            id,
            arms,
            env,
            guard_stack,
            result_wraps_thunk,
        } = request.continuation.frames[index].clone()
        else {
            unreachable!();
        };
        match self.handle_request(request, id, arms, 0, &env, &guard_stack, result_wraps_thunk)? {
            ControlResult::Request(request) => self.propagate_request_before(request, index),
            value => Ok(value),
        }
    }

    fn bind_pattern(
        &mut self,
        pattern: &ControlPattern,
        value: ControlValue,
        env: &mut ControlEnv,
    ) -> Result<(), VmError> {
        match pattern {
            ControlPattern::Wildcard => Ok(()),
            ControlPattern::Bind { name } => {
                env.insert(self.module.symbol_for_name(name), value);
                Ok(())
            }
            ControlPattern::Lit { lit } if value == control_value_from_lit(lit) => Ok(()),
            ControlPattern::Lit { .. } => Err(VmError::PatternMismatch),
            ControlPattern::Tuple { items } => {
                let ControlValue::Tuple(values) = value else {
                    return Err(VmError::PatternMismatch);
                };
                if items.len() != values.len() {
                    return Err(VmError::PatternMismatch);
                }
                for (item, value) in items.iter().zip(values) {
                    self.bind_pattern(item, value, env)?;
                }
                Ok(())
            }
            ControlPattern::Variant {
                tag,
                value: pattern_value,
            } => {
                let ControlValue::Variant {
                    tag: actual,
                    value: actual_value,
                } = value
                else {
                    return Err(VmError::PatternMismatch);
                };
                if tag != &actual {
                    return Err(VmError::PatternMismatch);
                }
                match (pattern_value, actual_value) {
                    (Some(pattern), Some(value)) => self.bind_pattern(pattern, *value, env),
                    (None, None) => Ok(()),
                    _ => Err(VmError::PatternMismatch),
                }
            }
            ControlPattern::Or { left, right } => {
                let snapshot = env.clone();
                if self.bind_pattern(left, value.clone(), env).is_ok() {
                    return Ok(());
                }
                *env = snapshot;
                self.bind_pattern(right, value, env)
            }
            ControlPattern::As { pattern, name } => {
                self.bind_pattern(pattern, value.clone(), env)?;
                env.insert(self.module.symbol_for_name(name), value);
                Ok(())
            }
            ControlPattern::Record { fields, spread } => {
                let ControlValue::Record(values) = value else {
                    return Err(VmError::PatternMismatch);
                };
                let mut rest = values.clone();
                for field in fields {
                    rest.remove(&field.name);
                    let Some(value) = values.get(&field.name).cloned() else {
                        let Some(default) = field.default else {
                            return Err(VmError::PatternMismatch);
                        };
                        let value = self.eval_value(default, env)?;
                        self.bind_pattern(&field.pattern, value, env)?;
                        continue;
                    };
                    self.bind_pattern(&field.pattern, value, env)?;
                }
                if let Some(spread) = spread {
                    let spread = match spread {
                        ControlRecordSpreadPattern::Head(pattern)
                        | ControlRecordSpreadPattern::Tail(pattern) => pattern,
                    };
                    self.bind_pattern(spread, ControlValue::Record(rest), env)?;
                }
                Ok(())
            }
            ControlPattern::List {
                prefix,
                spread,
                suffix,
            } => {
                let ControlValue::List(values) = value else {
                    return Err(VmError::PatternMismatch);
                };
                if values.len() < prefix.len() + suffix.len() {
                    return Err(VmError::PatternMismatch);
                }
                if spread.is_none() && values.len() != prefix.len() + suffix.len() {
                    return Err(VmError::PatternMismatch);
                }
                for (index, pattern) in prefix.iter().enumerate() {
                    let Some(value) = values.index(index) else {
                        return Err(VmError::PatternMismatch);
                    };
                    self.bind_pattern(pattern, (*value).clone(), env)?;
                }
                if let Some(spread) = spread {
                    let start = prefix.len();
                    let end = values.len() - suffix.len();
                    let Some(slice) = values.index_range(start, end) else {
                        return Err(VmError::PatternMismatch);
                    };
                    self.bind_pattern(spread, ControlValue::List(slice), env)?;
                }
                let suffix_start = values.len() - suffix.len();
                for (offset, pattern) in suffix.iter().enumerate() {
                    let Some(value) = values.index(suffix_start + offset) else {
                        return Err(VmError::PatternMismatch);
                    };
                    self.bind_pattern(pattern, (*value).clone(), env)?;
                }
                Ok(())
            }
        }
    }

    fn eval_effect_id(&self, id: EffectIdRef) -> Result<u64, VmError> {
        match id {
            EffectIdRef::Peek => self.guard_stack.peek().ok_or(VmError::UnsupportedFindId),
            EffectIdRef::Var(var) => self
                .guard_stack
                .find_var(var)
                .or_else(|| self.guard_stack.peek())
                .ok_or(VmError::UnsupportedEffectIdVar(var.0)),
        }
    }

    fn find_effect_id(&self, id: EffectIdRef) -> Result<bool, VmError> {
        let id = self.eval_effect_id(id)?;
        Ok(self.guard_stack.contains(id))
    }

    fn fresh_guard_id(&mut self) -> u64 {
        let id = self.next_guard_id;
        self.next_guard_id += 1;
        id
    }
}

fn split_handle_continuations(
    continuation: &ControlContinuation,
    id: u64,
) -> (ControlContinuation, ControlContinuation) {
    let Some(index) = continuation.frames.iter().position(
        |frame| matches!(frame, ControlFrame::Handle { id: current, .. } if *current == id),
    ) else {
        return (
            ControlContinuation {
                frames: VecDeque::new(),
                guard_stack: continuation.guard_stack.clone(),
            },
            ControlContinuation {
                frames: VecDeque::new(),
                guard_stack: continuation.guard_stack.clone(),
            },
        );
    };

    let outer_guard_stack =
        if let ControlFrame::Handle { guard_stack, .. } = &continuation.frames[index] {
            guard_stack.clone()
        } else {
            continuation.guard_stack.clone()
        };

    (
        ControlContinuation {
            frames: continuation.frames.iter().take(index).cloned().collect(),
            guard_stack: outer_guard_stack,
        },
        ControlContinuation {
            frames: continuation
                .frames
                .iter()
                .skip(index + 1)
                .cloned()
                .collect(),
            guard_stack: continuation.guard_stack.clone(),
        },
    )
}

fn insert_control_resume(
    env: &mut ControlEnv,
    resume: Option<ControlSymbolId>,
    continuation: ControlContinuation,
) {
    if let Some(resume) = resume {
        env.insert(
            resume,
            ControlValue::Resume(ControlHeap::new(ControlResume { continuation })),
        );
    }
}

fn push_frame(mut request: ControlRequest, frame: ControlFrame) -> ControlRequest {
    request.continuation.frames.push_front(frame);
    request
}

fn prepend_frames(continuation: &mut ControlContinuation, mut frames: VecDeque<ControlFrame>) {
    frames.append(&mut continuation.frames);
    continuation.frames = frames;
}

fn push_thunk_expr_frames(request: ControlRequest, thunk: &ControlThunk) -> ControlRequest {
    let request = push_frame(request, ControlFrame::BindHere);
    push_thunk_boundary_frame(request, thunk)
}

fn push_thunk_boundary_frame(request: ControlRequest, thunk: &ControlThunk) -> ControlRequest {
    if thunk.blocked.is_empty() {
        return request;
    }
    push_frame(
        request,
        ControlFrame::BlockedEffects {
            blocked: thunk.blocked.clone(),
            active: thunk.blocked.iter().any(|blocked| blocked.active),
        },
    )
}

fn mark_control_request_with_blocked(
    module: &ControlModule,
    mut request: ControlRequest,
    blocked_effects: &[BlockedEffect],
) -> ControlRequest {
    for blocked in blocked_effects {
        if effect_is_allowed(&blocked.allowed, module.symbol_path(request.effect)) {
            continue;
        }
        let has_live_blocker = control_request_has_live_blocker(&request);
        add_control_request_blocker(&mut request, blocked.guard_id, !has_live_blocker);
    }
    request
}

fn mark_control_request_with_active_blocked(
    module: &ControlModule,
    mut request: ControlRequest,
    blocked_effects: &[BlockedEffect],
) -> ControlRequest {
    for blocked in blocked_effects.iter().rev() {
        if effect_is_allowed(&blocked.allowed, module.symbol_path(request.effect)) {
            continue;
        }
        let has_live_blocker = control_request_has_live_blocker(&request);
        add_control_request_blocker(&mut request, blocked.guard_id, !has_live_blocker);
    }
    request
}

fn control_request_is_blocked_by_stack(request: &ControlRequest, stack: &GuardStack) -> bool {
    request
        .blocked_id
        .is_some_and(|blocked| stack.contains(blocked))
        || request
            .blocked_ids
            .iter()
            .any(|blocked| stack.contains(*blocked))
}

fn add_control_request_blocker(request: &mut ControlRequest, guard_id: u64, replace_primary: bool) {
    if replace_primary {
        if let Some(previous) = request.blocked_id
            && previous != guard_id
            && !request.blocked_ids.contains(&previous)
        {
            request.blocked_ids.push(previous);
        }
        request.blocked_id = Some(guard_id);
    } else if request.blocked_id != Some(guard_id) && !request.blocked_ids.contains(&guard_id) {
        request.blocked_ids.push(guard_id);
    }
}

fn control_request_has_live_blocker(request: &ControlRequest) -> bool {
    control_request_blocker_is_live(request, request.blocked_id)
        || request
            .blocked_ids
            .iter()
            .any(|blocked| control_request_blocker_is_live(request, Some(*blocked)))
}

fn control_request_blocker_is_live(request: &ControlRequest, blocked: Option<u64>) -> bool {
    blocked.is_some_and(|blocked| {
        request.continuation.guard_stack.contains(blocked)
            || request.continuation.frames.iter().any(|frame| match frame {
                ControlFrame::Handle { guard_stack, .. } => guard_stack.contains(blocked),
                ControlFrame::HandleGuard {
                    handler_guard_stack,
                    ..
                } => handler_guard_stack.contains(blocked),
                _ => false,
            })
    })
}

fn make_recursive_local_value(
    module: &ControlModule,
    pattern: &ControlPattern,
    value: ControlValue,
) -> ControlValue {
    let Some(name) = single_bind_name(pattern) else {
        return value;
    };
    let ControlValue::Closure(closure) = value else {
        return value;
    };
    let mut closure = (*closure).clone();
    closure.self_name = Some(module.symbol_for_name(&name));
    ControlValue::Closure(ControlHeap::new(closure))
}

fn single_bind_name(pattern: &ControlPattern) -> Option<typed_ir::Name> {
    match pattern {
        ControlPattern::Bind { name } => Some(name.clone()),
        ControlPattern::As { name, .. } => Some(name.clone()),
        _ => None,
    }
}

fn control_lambda_shape(lambda_ty: &Type, body_ty: &Type) -> (bool, bool) {
    match lambda_ty {
        Type::Fun { param, ret } => (
            control_param_forces_thunk_arg(param),
            type_wraps_thunk(ret.as_ref()),
        ),
        _ => (false, type_wraps_thunk(body_ty)),
    }
}

fn control_param_forces_thunk_arg(param_ty: &Type) -> bool {
    !matches!(
        param_ty,
        Type::Thunk { .. } | Type::Core(typed_ir::Type::Any)
    )
}

fn type_wraps_thunk(ty: &Type) -> bool {
    matches!(ty, Type::Thunk { .. })
}

fn control_wrap_result(result: ControlResult, result_wraps_thunk: bool) -> ControlResult {
    if !result_wraps_thunk {
        return result;
    }
    match result {
        ControlResult::Value(value) => ControlResult::Value(control_wrap_value(value, true)),
        ControlResult::Request(request) => {
            ControlResult::Request(push_frame(request, ControlFrame::WrapThunkResult))
        }
    }
}

fn control_wrap_value(value: ControlValue, result_wraps_thunk: bool) -> ControlValue {
    if !result_wraps_thunk || matches!(value, ControlValue::Thunk(_)) {
        return value;
    }
    ControlValue::Thunk(ControlHeap::new(ControlThunk {
        body: ControlThunkBody::Value(value),
        env: ControlEnv::new(),
        guard_stack: GuardStack::default(),
        blocked: Vec::new(),
    }))
}

fn control_value_from_lit(lit: &typed_ir::Lit) -> ControlValue {
    match lit {
        typed_ir::Lit::Int(value) => ControlValue::Int(ControlInt::from_lit(value)),
        typed_ir::Lit::Float(value) => ControlValue::Float(value.clone()),
        typed_ir::Lit::String(value) => ControlValue::String(StringTree::from_str(value)),
        typed_ir::Lit::Bool(value) => ControlValue::Bool(*value),
        typed_ir::Lit::Unit => ControlValue::Unit,
    }
}

fn control_cast_value(value: ControlValue, expected: &typed_ir::Type) -> ControlValue {
    if is_float_type(expected) {
        return match value {
            ControlValue::Int(value) => ControlValue::Float(value.to_float_string()),
            value => value,
        };
    }
    value
}

fn control_apply_primitive(
    op: typed_ir::PrimitiveOp,
    args: &[ControlValue],
) -> Result<ControlValue, VmError> {
    match op {
        typed_ir::PrimitiveOp::YadaYada => Err(VmError::YadaYada),
        typed_ir::PrimitiveOp::BoolNot => Ok(ControlValue::Bool(!control_bool_value(&args[0])?)),
        typed_ir::PrimitiveOp::BoolEq => Ok(ControlValue::Bool(
            control_bool_value(&args[0])? == control_bool_value(&args[1])?,
        )),
        typed_ir::PrimitiveOp::IntAdd => Ok(ControlValue::Int(
            control_int_value(&args[0])?.add(control_int_value(&args[1])?),
        )),
        typed_ir::PrimitiveOp::IntSub => Ok(ControlValue::Int(
            control_int_value(&args[0])?.sub(control_int_value(&args[1])?),
        )),
        typed_ir::PrimitiveOp::IntMul => Ok(ControlValue::Int(
            control_int_value(&args[0])?.mul(control_int_value(&args[1])?),
        )),
        typed_ir::PrimitiveOp::IntDiv => Ok(ControlValue::Int(
            control_int_value(&args[0])?.div(control_int_value(&args[1])?),
        )),
        typed_ir::PrimitiveOp::IntMod => Ok(ControlValue::Int(
            control_int_value(&args[0])?.rem(control_int_value(&args[1])?),
        )),
        typed_ir::PrimitiveOp::IntEq => Ok(ControlValue::Bool(
            control_int_value(&args[0])? == control_int_value(&args[1])?,
        )),
        typed_ir::PrimitiveOp::IntLt => Ok(ControlValue::Bool(
            control_int_value(&args[0])?
                .cmp(control_int_value(&args[1])?)
                .is_lt(),
        )),
        typed_ir::PrimitiveOp::IntLe => Ok(ControlValue::Bool(
            !control_int_value(&args[0])?
                .cmp(control_int_value(&args[1])?)
                .is_gt(),
        )),
        typed_ir::PrimitiveOp::IntGt => Ok(ControlValue::Bool(
            control_int_value(&args[0])?
                .cmp(control_int_value(&args[1])?)
                .is_gt(),
        )),
        typed_ir::PrimitiveOp::IntGe => Ok(ControlValue::Bool(
            !control_int_value(&args[0])?
                .cmp(control_int_value(&args[1])?)
                .is_lt(),
        )),
        typed_ir::PrimitiveOp::ListEmpty => Ok(ControlValue::List(ListTree::empty())),
        typed_ir::PrimitiveOp::ListSingleton => Ok(ControlValue::List(ListTree::singleton(
            Rc::new(args[0].clone()),
        ))),
        typed_ir::PrimitiveOp::ListLen => Ok(ControlValue::Int(ControlInt::Small(
            control_list_value(&args[0])?.len() as i64,
        ))),
        typed_ir::PrimitiveOp::ListMerge => {
            let left = control_list_value(&args[0])?;
            let right = control_list_value(&args[1])?;
            Ok(ControlValue::List(ListTree::concat(
                left.clone(),
                right.clone(),
            )))
        }
        typed_ir::PrimitiveOp::ListIndex => {
            let list = control_list_value(&args[0])?;
            let index = usize::try_from(control_int_value(&args[1])?.as_i64()?)
                .map_err(|_| VmError::ExpectedInt(export_value_lossy(&args[1], None)))?;
            list.index(index)
                .map(|value| (*value).clone())
                .ok_or_else(|| VmError::ExpectedList(export_value_lossy(&args[0], None)))
        }
        typed_ir::PrimitiveOp::ListIndexRangeRaw => {
            let list = control_list_value(&args[0])?;
            let start = usize::try_from(control_int_value(&args[1])?.as_i64()?)
                .map_err(|_| VmError::ExpectedInt(export_value_lossy(&args[1], None)))?;
            let end = usize::try_from(control_int_value(&args[2])?.as_i64()?)
                .map_err(|_| VmError::ExpectedInt(export_value_lossy(&args[2], None)))?;
            list.index_range(start, end)
                .map(ControlValue::List)
                .ok_or_else(|| VmError::ExpectedList(export_value_lossy(&args[0], None)))
        }
        typed_ir::PrimitiveOp::ListSpliceRaw => {
            let list = control_list_value(&args[0])?;
            let start = usize::try_from(control_int_value(&args[1])?.as_i64()?)
                .map_err(|_| VmError::ExpectedInt(export_value_lossy(&args[1], None)))?;
            let end = usize::try_from(control_int_value(&args[2])?.as_i64()?)
                .map_err(|_| VmError::ExpectedInt(export_value_lossy(&args[2], None)))?;
            let insert = control_list_value(&args[3])?;
            list.splice(start, end, insert.clone())
                .map(ControlValue::List)
                .ok_or_else(|| VmError::ExpectedList(export_value_lossy(&args[0], None)))
        }
        typed_ir::PrimitiveOp::ListViewRaw => match control_list_value(&args[0])?.view() {
            ListView::Empty => Ok(ControlValue::Variant {
                tag: typed_ir::Name("empty".to_string()),
                value: None,
            }),
            ListView::Leaf(single) => Ok(ControlValue::Variant {
                tag: typed_ir::Name("leaf".to_string()),
                value: Some(Box::new((*single).clone())),
            }),
            ListView::Node { left, right, .. } => Ok(ControlValue::Variant {
                tag: typed_ir::Name("node".to_string()),
                value: Some(Box::new(ControlValue::Tuple(vec![
                    ControlValue::List(left),
                    ControlValue::List(right),
                ]))),
            }),
        },
        _ => apply_primitive(
            op,
            &args
                .iter()
                .map(|value| export_value(value, None))
                .collect::<Result<Vec<_>, _>>()?,
        )
        .and_then(|value| import_value(&value)),
    }
}

fn control_int_value(value: &ControlValue) -> Result<&ControlInt, VmError> {
    match value {
        ControlValue::Int(value) => Ok(value),
        other => Err(VmError::ExpectedInt(export_value_lossy(other, None))),
    }
}

fn control_bool_value(value: &ControlValue) -> Result<bool, VmError> {
    match value {
        ControlValue::Bool(value) => Ok(*value),
        other => Err(VmError::ExpectedBool(export_value_lossy(other, None))),
    }
}

fn control_list_value(value: &ControlValue) -> Result<&ListTree<Rc<ControlValue>>, VmError> {
    match value {
        ControlValue::List(value) => Ok(value),
        other => Err(VmError::ExpectedList(export_value_lossy(other, None))),
    }
}

fn export_value(value: &ControlValue, module: Option<&ControlModule>) -> Result<VmValue, VmError> {
    Ok(match value {
        ControlValue::Int(value) => VmValue::Int(value.to_vm_string()),
        ControlValue::Float(value) => VmValue::Float(value.clone()),
        ControlValue::String(value) => VmValue::String(value.clone()),
        ControlValue::Bytes(value) => VmValue::Bytes(value.clone()),
        ControlValue::Path(value) => VmValue::Path(value.clone()),
        ControlValue::Bool(value) => VmValue::Bool(*value),
        ControlValue::Unit => VmValue::Unit,
        ControlValue::List(value) => {
            let mut items = Vec::with_capacity(value.len());
            value.for_each_ref(&mut |item| {
                items.push(Rc::new(export_value_lossy(item, module)));
            });
            VmValue::List(ListTree::from_items(items))
        }
        ControlValue::Tuple(items) => VmValue::Tuple(
            items
                .iter()
                .map(|value| export_value(value, module))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        ControlValue::Record(fields) => VmValue::Record(
            fields
                .iter()
                .map(|(name, value)| Ok((name.clone(), export_value(value, module)?)))
                .collect::<Result<BTreeMap<_, _>, VmError>>()?,
        ),
        ControlValue::Variant { tag, value } => VmValue::Variant {
            tag: tag.clone(),
            value: value
                .as_ref()
                .map(|value| export_value(value, module).map(Box::new))
                .transpose()?,
        },
        ControlValue::EffectOp(symbol) => VmValue::EffectOp(
            module
                .map(|module| module.symbol_path(*symbol).clone())
                .unwrap_or_default(),
        ),
        ControlValue::PrimitiveOp(primitive) => VmValue::PrimitiveOp(Rc::new(VmPrimitive {
            op: primitive.op,
            args: primitive
                .args
                .iter()
                .map(|value| export_value(value, module))
                .collect::<Result<Vec<_>, _>>()?,
        })),
        ControlValue::EffectId(id) => VmValue::EffectId(*id),
        ControlValue::Closure(_) | ControlValue::Thunk(_) | ControlValue::Resume(_) => {
            return Err(VmError::ExpectedList(VmValue::Unit));
        }
    })
}

fn export_value_lossy(value: &ControlValue, module: Option<&ControlModule>) -> VmValue {
    export_value(value, module).unwrap_or(VmValue::Unit)
}

fn import_value(value: &VmValue) -> Result<ControlValue, VmError> {
    Ok(match value {
        VmValue::Int(value) => ControlValue::Int(ControlInt::from_text(value.clone())?),
        VmValue::Float(value) => ControlValue::Float(value.clone()),
        VmValue::String(value) => ControlValue::String(value.clone()),
        VmValue::Bytes(value) => ControlValue::Bytes(value.clone()),
        VmValue::Path(value) => ControlValue::Path(value.clone()),
        VmValue::Bool(value) => ControlValue::Bool(*value),
        VmValue::Unit => ControlValue::Unit,
        VmValue::List(value) => {
            let mut items = Vec::with_capacity(value.len());
            value.for_each_ref(&mut |item| {
                items.push(Rc::new(import_value(item).unwrap_or(ControlValue::Unit)));
            });
            ControlValue::List(ListTree::from_items(items))
        }
        VmValue::Tuple(items) => ControlValue::Tuple(
            items
                .iter()
                .map(import_value)
                .collect::<Result<Vec<_>, _>>()?,
        ),
        VmValue::Record(fields) => ControlValue::Record(
            fields
                .iter()
                .map(|(name, value)| Ok((name.clone(), import_value(value)?)))
                .collect::<Result<BTreeMap<_, _>, VmError>>()?,
        ),
        VmValue::Variant { tag, value } => ControlValue::Variant {
            tag: tag.clone(),
            value: value
                .as_ref()
                .map(|value| import_value(value).map(Box::new))
                .transpose()?,
        },
        VmValue::EffectId(id) => ControlValue::EffectId(*id),
        VmValue::EffectOp(_) => return Err(VmError::ExpectedClosure(value.clone())),
        VmValue::PrimitiveOp(primitive) => {
            ControlValue::PrimitiveOp(ControlHeap::new(ControlPrimitive {
                op: primitive.op,
                args: primitive
                    .args
                    .iter()
                    .map(import_value)
                    .collect::<Result<Vec<_>, _>>()?,
            }))
        }
        VmValue::Closure(_) | VmValue::Thunk(_) | VmValue::Resume(_) => {
            return Err(VmError::ExpectedList(VmValue::Unit));
        }
    })
}

impl PartialEq for ControlValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Int(left), Self::Int(right)) => left == right,
            (Self::Float(left), Self::Float(right)) => left == right,
            (Self::String(left), Self::String(right)) => left == right,
            (Self::Bytes(left), Self::Bytes(right)) => left == right,
            (Self::Path(left), Self::Path(right)) => left == right,
            (Self::Bool(left), Self::Bool(right)) => left == right,
            (Self::Unit, Self::Unit) => true,
            (
                Self::Variant {
                    tag: left_tag,
                    value: left_value,
                },
                Self::Variant {
                    tag: right_tag,
                    value: right_value,
                },
            ) => left_tag == right_tag && left_value == right_value,
            (Self::Tuple(left), Self::Tuple(right)) => left == right,
            _ => false,
        }
    }
}
