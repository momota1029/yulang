use num_bigint::BigInt;
use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};

use crate::cast_resolution::{OrdinaryCastResolution, classify_ordinary_cast_candidates};
use crate::roles::RoleImplTable;
use crate::types::{Scheme, SubtractId, TypeArena, TypeIds, TypeVar};

/// 多相 IR の本体を置く Arena。
///
/// `ExprId` / `PatId` / `DefId` / `RefId` / `SelectId` は、この Arena の中だけで意味を持つ。
/// 位置依存の ID を cache 境界へ出さないため、Arena は永続データというよりも
/// 1回の lowering / inference run の結果を読むための器として扱う。
///
/// 型推論中に増える一時情報はここへ入れない。式の一時型、RefId の use-site 型、
/// selection の receiver 型、SCC の open component は `infer` crate 側で管理する。
/// `poly` に残すのは、最終的に IR として意味を持つ本体と解決結果だけ。
#[derive(Clone, Serialize, Deserialize)]
pub struct Arena {
    /// トップレベル定義の並び（旧 top を一本化）。
    pub roots: Vec<DefId>,
    /// 実行対象になる top-level item の並び。
    ///
    /// 裸式だけでなく、RHS 評価で計算が発生する top-level binding もここへ入る。
    /// 実行順を保つため、式 root と computed binding root を同じ列で保持する。
    pub runtime_roots: Vec<RuntimeRoot>,
    /// トップレベルに裸で現れた式の並び。主に dump / debug 用。
    ///
    /// `roots` は module 直下の定義一覧であり、runtime demand root ではない。
    /// `1` だけの source も実行対象になるため、式 root は定義 root と分けて保持する。
    pub root_exprs: Vec<ExprId>,
    /// root expression の境界型を持つ hidden definition。
    ///
    /// 通常の root expression は erased expression だけで specialize できるため、ここには入れない。
    /// lowering helper を持つ root expression だけが、infer で得た全体境界を specialize の初期 demand
    /// として渡すために hidden def を持つ。
    pub root_expr_defs: FxHashMap<ExprId, DefId>,
    /// 疎な定義（scheme/body を内包）。登録し直しで更新する。
    pub defs: DefArena,
    /// RefId → 解決先 DefId。名前解決前は None。
    refs: Vec<Option<DefId>>,
    /// SelectId → selection site。解決前は field 名だけを持つ。
    selects: Vec<Select>,
    /// source lowering で宣言された direct cast 規則。
    ///
    /// cast は単相化でも subtype 境界として効くため、infer 内部の一時 table だけでなく、
    /// principal scheme と同じ poly 境界へ残す。
    pub cast_rules: Vec<CastRule>,
    /// source lowering で解決された role impl candidate。
    ///
    /// downstream stages need role impls to materialize role-constrained schemes without
    /// depending on infer's mutable solver tables.
    pub role_impls: RoleImplTable,
    /// source lowering で解決された effect operation。
    ///
    /// effect operation は body を持たない `Def::Let` として型だけを持つが、runtime では
    /// effect request を送出する値である。後段が `DefId` から送出 path を読めるように
    /// 構造化された metadata として残す。
    pub effect_operations: FxHashMap<DefId, EffectOperation>,
    /// source lowering が生成した local mutable var effect family。
    ///
    /// This is a compiler certificate, not a naming convention. Later stages may match this
    /// family against handler/effect paths, but only after the family appears here.
    #[serde(default)]
    pub synthetic_var_effects: Vec<SyntheticVarEffect>,
    /// source lowering で宣言された data constructor。
    ///
    /// constructor も body を持たない `Def::Let` だが、runtime では constructor 値として
    /// 評価する必要がある。単相化後段が `DefId` から arity と owner を読めるようにここへ残す。
    pub constructors: FxHashMap<DefId, Constructor>,
    /// Source annotations that make a function argument an explicit effect contract.
    ///
    /// This is separate from `Def::Arg`: most inferred callback effects are not contracts, and
    /// downstream adapter hygiene must not reconstruct that distinction from the mono type shape.
    #[serde(default)]
    pub arg_effect_contracts: FxHashMap<DefId, ArgEffectContract>,
    /// `struct` field projection として登録された value receiver method。
    ///
    /// field projection は selection 解決時には `Method` として見えるが、runtime では method
    /// instance ではなく constructor payload への projection として読む。
    pub field_projections: FxHashSet<DefId>,
    expr: Vec<Expr>,
    pat: Vec<Pat>,
    type_ids: TypeIds,
    pub typ: TypeArena,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct CastRule {
    pub def: DefId,
    pub source: Vec<String>,
    pub target: Vec<String>,
    pub scheme: Scheme,
    #[serde(default)]
    pub kind: CastRuleKind,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum CastRuleKind {
    #[default]
    Value,
    EffectUp,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct EffectOperation {
    pub path: Vec<String>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct SyntheticVarEffect {
    pub effect_path: Vec<String>,
    #[serde(default)]
    pub get_operation: Option<DefId>,
    #[serde(default)]
    pub set_operation: Option<DefId>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct Constructor {
    pub owner_path: Vec<String>,
    pub name: String,
    pub arity: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ArgEffectContract {
    pub markers: Vec<ArgEffectContractMarker>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ArgEffectContractMarker {
    pub path: Vec<String>,
    pub depth: u32,
    pub resume: ContractResumePolicy,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ContractResumePolicy {
    PreserveMatchingPath,
    ForeignOnly,
}

/// block 内に現れる文の構造。
///
/// ここには構文上の順序と子 node への ID だけを残す。名前解決の作業状態や型情報は持たせない。
#[derive(Clone, Serialize, Deserialize)]
pub enum Stmt {
    Let(Vis, PatId, ExprId),
    Expr(ExprId),
    Module(DefId, Vec<Stmt>),
}
impl Arena {
    pub fn new() -> Self {
        Self {
            roots: Vec::new(),
            runtime_roots: Vec::new(),
            root_exprs: Vec::new(),
            root_expr_defs: FxHashMap::default(),
            defs: DefArena::new(),
            refs: Vec::new(),
            selects: Vec::new(),
            cast_rules: Vec::new(),
            role_impls: RoleImplTable::new(),
            effect_operations: FxHashMap::default(),
            synthetic_var_effects: Vec::new(),
            constructors: FxHashMap::default(),
            arg_effect_contracts: FxHashMap::default(),
            field_projections: FxHashSet::default(),
            expr: Vec::new(),
            pat: Vec::new(),
            type_ids: TypeIds::new(),
            typ: TypeArena::new(),
        }
    }
    pub fn expr(&self, id: ExprId) -> &Expr {
        &self.expr[id.0 as usize]
    }
    pub fn pat(&self, id: PatId) -> &Pat {
        &self.pat[id.0 as usize]
    }

    pub fn exprs(&self) -> &[Expr] {
        &self.expr
    }

    pub fn pats(&self) -> &[Pat] {
        &self.pat
    }

    pub fn refs(&self) -> &[Option<DefId>] {
        &self.refs
    }

    pub fn selects(&self) -> &[Select] {
        &self.selects
    }

    /// Resolve ordinary value declarations for one exact constructor pair by cardinality.
    pub fn resolve_value_cast(
        &self,
        source: &[String],
        target: &[String],
    ) -> OrdinaryCastResolution<&CastRule> {
        classify_ordinary_cast_candidates(self.cast_rules.iter().filter(|rule| {
            rule.kind == CastRuleKind::Value
                && rule.source.as_slice() == source
                && rule.target.as_slice() == target
        }))
    }

    pub fn root_expr_def(&self, expr: ExprId) -> Option<DefId> {
        self.root_expr_defs.get(&expr).copied()
    }

    pub fn add_expr(&mut self, expr: Expr) -> ExprId {
        let id = ExprId(self.expr.len() as u32);
        self.expr.push(expr);
        id
    }

    /// Arena-local ID remapping uses a two-pass import: reserve all IDs first,
    /// then overwrite placeholders after child IDs are known.
    pub fn reserve_expr_slot(&mut self) -> ExprId {
        self.add_expr(Expr::Lit(Lit::Unit))
    }

    pub fn set_expr(&mut self, id: ExprId, expr: Expr) {
        self.expr[id.0 as usize] = expr;
    }

    pub fn add_pat(&mut self, pat: Pat) -> PatId {
        let id = PatId(self.pat.len() as u32);
        self.pat.push(pat);
        id
    }

    /// See `reserve_expr_slot`; pattern graphs need the same import shape.
    pub fn reserve_pat_slot(&mut self) -> PatId {
        self.add_pat(Pat::Wild)
    }

    pub fn set_pat(&mut self, id: PatId, pat: Pat) {
        self.pat[id.0 as usize] = pat;
    }

    // --- 参照: RefId → 解決先 DefId（名前解決前は None）---

    /// 未解決の参照スロットを確保して RefId を発行する。
    pub fn add_ref(&mut self) -> RefId {
        let id = RefId(self.refs.len() as u32);
        self.refs.push(None);
        id
    }
    /// 名前解決の結果を書き戻す。
    pub fn resolve_ref(&mut self, id: RefId, def: DefId) {
        self.refs[id.0 as usize] = Some(def);
    }
    pub fn ref_target(&self, id: RefId) -> Option<DefId> {
        self.refs[id.0 as usize]
    }

    // --- selection site: SelectId → field/method 解決結果 ---

    /// field / method selection site を確保する。
    pub fn add_select(&mut self, name: impl Into<String>) -> SelectId {
        let id = SelectId(self.selects.len() as u32);
        self.selects.push(Select {
            name: name.into(),
            resolution: None,
        });
        id
    }
    pub fn select(&self, id: SelectId) -> &Select {
        &self.selects[id.0 as usize]
    }
    pub fn resolve_select(&mut self, id: SelectId, resolution: SelectResolution) {
        self.selects[id.0 as usize].resolution = Some(resolution);
    }

    /// 型変数 ID は Arena ごとの作業メモリ内だけで安定させる。
    pub fn fresh_type_var(&mut self) -> TypeVar {
        self.type_ids.fresh_type_var()
    }

    /// SubtractId も TypeVar と同じく、Arena ごとの engine-local ID として発行する。
    pub fn fresh_subtract_id(&mut self) -> SubtractId {
        self.type_ids.fresh_subtract_id()
    }

    pub fn register_synthetic_var_effect(&mut self, effect_path: Vec<String>) {
        self.ensure_synthetic_var_effect(effect_path);
    }

    pub fn register_synthetic_var_effect_operations(
        &mut self,
        effect_path: Vec<String>,
        get_operation: DefId,
        set_operation: DefId,
    ) {
        let effect = self.ensure_synthetic_var_effect(effect_path);
        effect.get_operation = Some(get_operation);
        effect.set_operation = Some(set_operation);
    }

    fn ensure_synthetic_var_effect(&mut self, effect_path: Vec<String>) -> &mut SyntheticVarEffect {
        if let Some(index) = self
            .synthetic_var_effects
            .iter()
            .position(|effect| effect.effect_path == effect_path)
        {
            return &mut self.synthetic_var_effects[index];
        }
        let index = self.synthetic_var_effects.len();
        self.synthetic_var_effects.push(SyntheticVarEffect {
            effect_path,
            get_operation: None,
            set_operation: None,
        });
        &mut self.synthetic_var_effects[index]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RuntimeRoot {
    Expr(ExprId),
    ComputedDef(DefId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
/// 定義を指す Arena-local ID。
///
/// `DefId` は symbol の安定名ではなく、この Arena の中で採番された作業 ID。
/// cache や外部表現では、最終的に scheme や path 側の情報へ写す。
pub struct DefId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
/// 参照 use-site を指す Arena-local ID。
///
/// `RefId -> DefId` の解決結果は `Arena::refs` に置く。use-site の parent や型は
/// 推論中の情報なので `infer::uses::RefUseTable` に置く。
pub struct RefId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
/// field / method selection の use-site を指す Arena-local ID。
///
/// `Expr::Select` は文字列名を直接持たず `SelectId` を持つ。こうしておくと、
/// 型制約から method が解けたあとに、同じ site へ解決結果を書き戻せる。
pub struct SelectId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
/// 式 node を指す Arena-local ID。
///
/// 式には永続的な型を持たせない。lowering 中の型は `infer::typing::Computation` で
/// 引き回し、必要なところだけ DefId / RefId に残す。
pub struct ExprId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
/// pattern node を指す Arena-local ID。
///
/// pattern も式と同じく永続的な型 table を持たない。束縛が生まれる場所だけ
/// `DefId` として残し、型は DefId 側につける。
pub struct PatId(pub u32);

/// 疎な定義の置き場。
///
/// `fresh` で DefId を採番し、`set` で登録し直す。in-place な mut borrow を避け、
/// 親子・エイリアスを読みながら新しい `Def` を組み立てて登録できるようにするため。
/// コストは clone だが、Def は疎なのでここでは許容する。
#[derive(Clone, Serialize, Deserialize)]
pub struct DefArena {
    map: FxHashMap<DefId, Def>,
    next: u32,
}
impl DefArena {
    pub fn new() -> Self {
        Self {
            map: FxHashMap::default(),
            next: 0,
        }
    }
    /// DefId を採番する（登録はまだ。直後に `set` すること）。
    pub fn fresh(&mut self) -> DefId {
        let id = DefId(self.next);
        self.next += 1;
        id
    }
    /// 定義を登録する（既存があれば登録し直し）。
    pub fn set(&mut self, id: DefId, def: Def) {
        self.map.insert(id, def);
    }
    pub fn get(&self, id: DefId) -> Option<&Def> {
        self.map.get(&id)
    }
    /// 既存 def を in-place に更新する。
    ///
    /// pass2 で `Def::Let.body` だけを埋めるように、scheme / visibility / children を保ったまま
    /// 小さい field 更新を行うための入口。
    pub fn get_mut(&mut self, id: DefId) -> Option<&mut Def> {
        self.map.get_mut(&id)
    }
    pub fn iter(&self) -> impl Iterator<Item = (DefId, &Def)> {
        self.map.iter().map(|(id, def)| (*id, def))
    }
    pub fn len(&self) -> usize {
        self.map.len()
    }
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

/// 名前解決と型推論の単位になる定義。
///
/// `Def::Let` は scheme と body を同じ場所に持つ。後段が DefId から定義を読んだときに、
/// 「型だけ別 table」「body だけ別 table」を探し回らないため。
///
/// `scheme: None` は未推論を表す。型が曖昧だから `Any` に逃がすための場所ではない。
#[derive(Clone, Serialize, Deserialize)]
pub enum Def {
    Mod {
        vis: Vis,
        children: Vec<DefId>,
    },
    Let {
        vis: Vis,
        scheme: Option<Scheme>,
        body: Option<ExprId>,
        children: Vec<DefId>,
    },
    Arg,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
/// Yulang の visibility。
///
/// 省略時は `Our`。`poly` はこの区別を保持するだけで、公開範囲の閉包計算や import 解決は
/// sources / infer 側の仕事として分ける。
pub enum Vis {
    Pub,
    Our,
    My,
}

/// 多相 IR の式。
///
/// ここに入るのは、構文を Arena ID で結んだ構造と、名前解決・selection 解決に必要な site ID。
/// 式ごとの型や effect は保持しない。式型は lowering 中の `Computation` と制約から扱い、
/// 最終的に DefId / RefId / scheme へ必要な分だけ残す。
#[derive(Clone, Serialize, Deserialize)]
pub enum Expr {
    Lit(Lit),
    PrimitiveOp(PrimitiveOp),
    Var(RefId),
    App(ExprId, ExprId),
    RefSet(ExprId, ExprId),
    Lambda(PatId, ExprId),
    Tuple(Vec<ExprId>),
    Record {
        fields: Vec<(String, ExprId)>,
        spread: RecordSpread<ExprId>,
    },
    PolyVariant(String, Vec<ExprId>),
    Select(ExprId, SelectId),
    Case(ExprId, Vec<CaseArm>),
    Catch(ExprId, Vec<CatchArm>),
    Block(Vec<Stmt>, Option<ExprId>),
}

/// `case` の arm。
///
/// guard は pattern が match した後に、その pattern が束縛した local を見ながら評価される。
/// body へ潰すと「guard が false なら次の arm を試す」という意味を失うため、IR に分けて残す。
#[derive(Clone, Serialize, Deserialize)]
pub struct CaseArm {
    pub pat: PatId,
    pub guard: Option<ExprId>,
    pub body: ExprId,
}

/// `catch` の arm。
///
/// effect arm は `continuation` を持ち、value arm は持たない。guard はどちらにも付けられる。
#[derive(Clone, Serialize, Deserialize)]
pub struct CatchArm {
    pub operation: Option<CatchOperation>,
    pub pat: PatId,
    pub continuation: Option<PatId>,
    pub guard: Option<ExprId>,
    pub body: ExprId,
}

/// `catch` の effect arm が扱う operation。
///
/// `path` は runtime handler が effect request と照合する exact path である。
/// `def` は operation 宣言が解決できた場合だけ入り、後段が payload / continuation の
/// mono 型を通常の scheme 経由で読むために使う。
#[derive(Clone, Serialize, Deserialize)]
pub struct CatchOperation {
    pub path: Vec<String>,
    pub def: Option<DefId>,
}

/// compiler builtin operation の値。
///
/// std source の `builtin_op::...` はこの enum に解決される。`poly` は typed/runtime IR に
/// 依存しないため、variant 名だけを同じにして後段で変換する。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PrimitiveOp {
    YadaYada,
    BoolNot,
    BoolEq,
    ListEmpty,
    ListSingleton,
    ListLen,
    ListMerge,
    ListIndex,
    ListIndexRange,
    ListSplice,
    ListIndexRangeRaw,
    ListSpliceRaw,
    ListViewRaw,
    StringLen,
    StringIndex,
    StringIndexRange,
    StringSplice,
    StringIndexRangeRaw,
    StringSpliceRaw,
    StringLineCount,
    StringLineRange,
    IntAdd,
    IntSub,
    IntMul,
    IntDiv,
    IntMod,
    IntEq,
    IntLt,
    IntLe,
    IntGt,
    IntGe,
    FloatAdd,
    FloatSub,
    FloatMul,
    FloatDiv,
    FloatEq,
    FloatLt,
    FloatLe,
    FloatGt,
    FloatGe,
    StringEq,
    StringConcat,
    StringToBytes,
    CharEq,
    CharToString,
    CharIsWhitespace,
    CharIsPunctuation,
    CharIsWord,
    BytesLen,
    BytesEq,
    BytesConcat,
    BytesIndex,
    BytesIndexRange,
    BytesToUtf8Raw,
    BytesToPath,
    PathToBytes,
    IntToString,
    IntToHex,
    IntToUpperHex,
    IntToFloat,
    FloatToString,
    BoolToString,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
/// selection site の本体。
///
/// `name` は surface に書かれた field / method 名。`resolution` は型制約や名前解決の進行で
/// 後から埋まる。`SelectId` を介すことで、dot selection が method として解けた時点で
/// SCC machine へ dependency を渡せる。
pub struct Select {
    pub name: String,
    pub resolution: Option<SelectResolution>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
/// selection site の解決結果。
///
/// record field は SCC 依存を作らない。method / typeclass method は hidden use として
/// target def へ edge を張るため、`DefId` を構造化して残す。
pub enum SelectResolution {
    RecordField,
    Method { def: DefId },
    TypeclassMethod { member: DefId },
}

/// literal。型推論は literal の形から制約を作るが、ここには推論結果を残さない。
#[derive(Clone, Serialize, Deserialize)]
pub enum Lit {
    Int(i64),
    BigInt(BigInt),
    Float(f64),
    Str(String),
    Bool(bool),
    Unit,
}

/// record spread の位置を明示するための共通 enum。
///
/// head / tail spread は構文上の向きが意味を持つため、単なる `Option` ではなく形を分ける。
#[derive(Clone, Serialize, Deserialize)]
pub enum RecordSpread<Id> {
    Head(Id),
    Tail(Id),
    None,
}

/// pattern IR。
///
/// pattern 自体へ型は付けない。変数束縛や constructor 参照など、後段で意味を持つ点だけ
/// `DefId` / `RefId` として残す。
#[derive(Clone, Serialize, Deserialize)]
pub enum Pat {
    Wild,
    Lit(Lit),
    Tuple(Vec<PatId>),
    List {
        prefix: Vec<PatId>,
        spread: Option<PatId>,
        suffix: Vec<PatId>,
    },
    Record {
        fields: Vec<RecordPatField>,
        spread: RecordSpread<DefId>,
    },
    PolyVariant(String, Vec<PatId>),
    Con(RefId, Vec<PatId>),
    Ref(RefId),
    Var(DefId),
    Or(PatId, PatId),
    As(PatId, DefId),
}

#[derive(Clone, Serialize, Deserialize)]
pub struct RecordPatField {
    pub name: String,
    pub pat: PatId,
    pub default: Option<ExprId>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_ids_are_arena_local() {
        let mut first = Arena::new();
        let mut second = Arena::new();

        assert_eq!(first.fresh_type_var(), TypeVar(0));
        assert_eq!(first.fresh_type_var(), TypeVar(1));
        assert_eq!(second.fresh_type_var(), TypeVar(0));

        assert_eq!(first.fresh_subtract_id(), SubtractId(0));
        assert_eq!(first.fresh_subtract_id(), SubtractId(1));
        assert_eq!(second.fresh_subtract_id(), SubtractId(0));
    }

    #[test]
    fn nested_expr_and_pattern_edges_use_arena_ids() {
        let mut arena = Arena::new();
        let param = arena.add_pat(Pat::Wild);
        let body = arena.add_expr(Expr::Lit(Lit::Unit));
        let lambda = arena.add_expr(Expr::Lambda(param, body));

        match arena.expr(lambda) {
            Expr::Lambda(actual_param, actual_body) => {
                assert_eq!(*actual_param, param);
                assert_eq!(*actual_body, body);
            }
            _ => panic!("expected lambda"),
        }

        let ctor = arena.add_ref();
        let payload = arena.add_pat(Pat::Wild);
        let con = arena.add_pat(Pat::Con(ctor, vec![payload]));

        match arena.pat(con) {
            Pat::Con(actual_ctor, payloads) => {
                assert_eq!(*actual_ctor, ctor);
                assert_eq!(payloads, &vec![payload]);
            }
            _ => panic!("expected constructor pattern"),
        }
    }

    #[test]
    fn selection_sites_have_arena_ids_and_late_resolution() {
        let mut arena = Arena::new();
        let recv = arena.add_expr(Expr::Lit(Lit::Unit));
        let select = arena.add_select("display");
        let expr = arena.add_expr(Expr::Select(recv, select));

        match arena.expr(expr) {
            Expr::Select(actual_recv, actual_select) => {
                assert_eq!(*actual_recv, recv);
                assert_eq!(*actual_select, select);
            }
            _ => panic!("expected select"),
        }

        assert_eq!(arena.select(select).name, "display");
        assert_eq!(arena.select(select).resolution, None);

        let method = DefId(7);
        arena.resolve_select(select, SelectResolution::Method { def: method });
        assert_eq!(
            arena.select(select).resolution,
            Some(SelectResolution::Method { def: method })
        );
    }
}
