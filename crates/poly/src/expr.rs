use num_bigint::BigInt;
use rustc_hash::FxHashMap;

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
pub struct Arena {
    /// トップレベル定義の並び（旧 top を一本化）。
    pub roots: Vec<DefId>,
    /// 疎な定義（scheme/body を内包）。登録し直しで更新する。
    pub defs: DefArena,
    /// RefId → 解決先 DefId。名前解決前は None。
    refs: Vec<Option<DefId>>,
    /// SelectId → selection site。解決前は field 名だけを持つ。
    selects: Vec<Select>,
    expr: Vec<Expr>,
    pat: Vec<Pat>,
    type_ids: TypeIds,
    pub typ: TypeArena,
}

/// block 内に現れる文の構造。
///
/// ここには構文上の順序と子 node への ID だけを残す。名前解決の作業状態や型情報は持たせない。
pub enum Stmt {
    Let(Vis, PatId, ExprId),
    Expr(ExprId),
    Module(DefId, Vec<Stmt>),
}
impl Arena {
    pub fn new() -> Self {
        Self {
            roots: Vec::new(),
            defs: DefArena::new(),
            refs: Vec::new(),
            selects: Vec::new(),
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

    pub fn add_expr(&mut self, expr: Expr) -> ExprId {
        let id = ExprId(self.expr.len() as u32);
        self.expr.push(expr);
        id
    }
    pub fn add_pat(&mut self, pat: Pat) -> PatId {
        let id = PatId(self.pat.len() as u32);
        self.pat.push(pat);
        id
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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// 定義を指す Arena-local ID。
///
/// `DefId` は symbol の安定名ではなく、この Arena の中で採番された作業 ID。
/// cache や外部表現では、最終的に scheme や path 側の情報へ写す。
pub struct DefId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// 参照 use-site を指す Arena-local ID。
///
/// `RefId -> DefId` の解決結果は `Arena::refs` に置く。use-site の parent や型は
/// 推論中の情報なので `infer::uses::RefUseTable` に置く。
pub struct RefId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// field / method selection の use-site を指す Arena-local ID。
///
/// `Expr::Select` は文字列名を直接持たず `SelectId` を持つ。こうしておくと、
/// 型制約から method が解けたあとに、同じ site へ解決結果を書き戻せる。
pub struct SelectId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// 式 node を指す Arena-local ID。
///
/// 式には永続的な型を持たせない。lowering 中の型は `infer::typing::Computation` で
/// 引き回し、必要なところだけ DefId / RefId に残す。
pub struct ExprId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
pub enum Expr {
    Lit(Lit),
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
    Case(ExprId, Vec<(PatId, ExprId)>),
    Catch(ExprId, Vec<(PatId, Option<PatId>, ExprId)>),
    Block(Vec<Stmt>, Option<ExprId>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// selection site の本体。
///
/// `name` は surface に書かれた field / method 名。`resolution` は型制約や名前解決の進行で
/// 後から埋まる。`SelectId` を介すことで、dot selection が method として解けた時点で
/// SCC machine へ dependency を渡せる。
pub struct Select {
    pub name: String,
    pub resolution: Option<SelectResolution>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
pub enum RecordSpread<Id> {
    Head(Id),
    Tail(Id),
    None,
}

/// pattern IR。
///
/// pattern 自体へ型は付けない。変数束縛や constructor 参照など、後段で意味を持つ点だけ
/// `DefId` / `RefId` として残す。
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
        fields: Vec<(String, PatId)>,
        spread: RecordSpread<DefId>,
    },
    PolyVariant(String, Vec<PatId>),
    Con(RefId, Vec<PatId>),
    Ref(RefId),
    Var(DefId),
    Or(PatId, PatId),
    As(PatId, DefId),
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
