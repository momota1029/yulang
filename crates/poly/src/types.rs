//! 型表現の最終寄りデータ構造。
//!
//! `Pos` / `Neg` / `Neu` は polarity を分けた Simple-sub 系の型表現。
//! 制約を解く途中の上下界 table は `infer` に置き、ここには型そのものと scheme だけを置く。
//! `TypeArena` は同じ型構造を ID で共有するための hash-cons arena。

use rustc_hash::FxHashMap;

/// generalize 済みの多相型。
///
/// `predicate` は scheme 本体の正側型、`quantifiers` はこの scheme が束縛する型変数。
/// `role_predicates` は型クラス相当の未解決 role 制約を、通常の型本体から分けて残す。
/// `recursive_bounds` は compact finalize で分離した再帰変数の side table。
/// `stack_quantifiers` は `StackWeight` 内に残る `#id` の量化集合。
/// `subtracts` は subtract table 由来の side table で、`#id` の量化そのものとは分けて持つ。
#[derive(Clone)]
pub struct Scheme {
    pub quantifiers: Vec<TypeVar>,
    pub role_predicates: Vec<RolePredicate>,
    pub recursive_bounds: Vec<SchemeRecursiveBound>,
    pub stack_quantifiers: Vec<SubtractId>,
    pub predicate: PosId,
    pub subtracts: Vec<SchemeSubtractFact>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// scheme に残る再帰変数の bounds。
///
/// `predicate` 側へ無理に混ぜると compact の簡約情報を失うため、中心変数と neutral bounds を
/// side table として保持する。instantiate 時に use-site の constraint へ戻す。
pub struct SchemeRecursiveBound {
    pub var: TypeVar,
    pub bounds: NeuId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// scheme に残る旧 `S-subtract(α, #a)` fact。
///
/// `subtractability` は scheme 側の `TypeArena` に載った `NeuId` を参照する。instantiate はこの fact を
/// fresh 化して infer 側の subtract table へ戻す。
pub struct SchemeSubtractFact {
    pub var: TypeVar,
    pub id: SubtractId,
    pub subtractability: Subtractability,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// scheme に残る role predicate。
///
/// `inputs` は通常引数、`associated` は `out = ...` のような関連型を表す。
/// role 引数は不変なので、final 表現では `NeuId` として持つ。
pub struct RolePredicate {
    pub role: Vec<String>,
    pub inputs: Vec<NeuId>,
    pub associated: Vec<RoleAssociatedType>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleAssociatedType {
    pub name: String,
    pub value: NeuId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
/// 言語コアが直接知っている builtin 型。
///
/// これは std module 内の `DefId` ではない。literal や unit argument のように std/prelude を
/// 読まなくても必要になる型 identity を、source path 文字列から切り離して扱うための小さな核。
pub enum BuiltinType {
    Int,
    Float,
    Bool,
    Unit,
    Never,
}

impl BuiltinType {
    pub fn from_surface_name(name: &str) -> Option<Self> {
        match name {
            "int" => Some(Self::Int),
            "float" => Some(Self::Float),
            "bool" => Some(Self::Bool),
            "unit" => Some(Self::Unit),
            "never" => Some(Self::Never),
            _ => None,
        }
    }

    pub fn surface_name(self) -> &'static str {
        match self {
            Self::Int => "int",
            Self::Float => "float",
            Self::Bool => "bool",
            Self::Unit => "unit",
            Self::Never => "never",
        }
    }
}

#[derive(Debug, Clone, Default)]
/// 型変数と SubtractId の採番器。
///
/// ID は Arena-local。グローバル counter にすると cache や差分推論の境界で意味が揺れるため、
/// `poly::Arena` / `infer::Arena` のような作業単位ごとに 0 から採番する。
pub struct TypeIds {
    next_type_var: u32,
    next_subtract_id: u32,
}

impl TypeIds {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn fresh_type_var(&mut self) -> TypeVar {
        let id = TypeVar(self.next_type_var);
        self.next_type_var += 1;
        id
    }

    pub fn reserve_type_vars_until(&mut self, next_type_var: u32) {
        self.next_type_var = self.next_type_var.max(next_type_var);
    }

    pub fn fresh_subtract_id(&mut self) -> SubtractId {
        let id = SubtractId(self.next_subtract_id);
        self.next_subtract_id += 1;
        id
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// 型変数。
///
/// 未解決の placeholder を表す ID だが、`Any` のような top 型ではない。
/// 上下界や量化の意味は `infer` 側の constraint / scheme が与える。
pub struct TypeVar(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// effect row の stack 寿命を追跡するための ID。
pub struct SubtractId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// stack entry の effect path 集合。
///
/// 旧 `S-subtract` の名前を残しているが、現行仕様では `stack(T, @S)` の `H` として使う。
/// 引数付き effect は stack 集合演算では path family だけを見る。引数そのものは通常の型制約で見る。
pub enum Subtractability {
    Empty,
    All,
    AllExcept(Vec<String>, Vec<NeuId>),
    AllExceptMany(Vec<(Vec<String>, Vec<NeuId>)>),
    Set(Vec<String>, Vec<NeuId>),
    SetMany(Vec<(Vec<String>, Vec<NeuId>)>),
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
/// `stack(T, @S)` の `@S`。
///
/// `@S` は `SubtractId` ごとに `pop(p)[H1, ..., Hn]` の正規形で持つ。
/// 合成は可換ではなく、左の後ろに右を積む。
pub struct StackWeight {
    entries: Vec<StackWeightEntry>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StackWeightEntry {
    pub id: SubtractId,
    pub pops: u32,
    pub stack: Vec<Subtractability>,
}

impl StackWeight {
    pub fn empty() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    pub fn pop(id: SubtractId) -> Self {
        Self::pops(id, 1)
    }

    pub fn pops(id: SubtractId, count: u32) -> Self {
        let mut out = Self::empty();
        out.push_pops(id, count);
        out
    }

    pub fn from_ids(ids: impl IntoIterator<Item = SubtractId>) -> Self {
        let mut out = Self::empty();
        for id in ids {
            out.push_pops(id, 1);
        }
        out
    }

    pub fn push(id: SubtractId, subtractability: Subtractability) -> Self {
        let mut out = Self::empty();
        out.push_stack(id, subtractability);
        out
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn entries(&self) -> &[StackWeightEntry] {
        &self.entries
    }

    pub fn contains(&self, id: SubtractId) -> bool {
        self.entries.iter().any(|entry| entry.id == id)
    }

    pub fn iter(&self) -> impl Iterator<Item = SubtractId> + '_ {
        self.entries.iter().map(|entry| entry.id)
    }

    pub fn stack_items(&self) -> impl Iterator<Item = &Subtractability> {
        self.entries.iter().flat_map(|entry| entry.stack.iter())
    }

    pub fn has_stack_entry(&self) -> bool {
        self.entries.iter().any(|entry| !entry.stack.is_empty())
    }

    pub fn compose(&self, other: &Self) -> Self {
        let mut out = self.clone();
        out.append(other);
        out
    }

    pub fn union(&self, other: &Self) -> Self {
        self.compose(other)
    }

    pub fn without_ids(&self, dead: impl Fn(SubtractId) -> bool) -> Self {
        let entries = self
            .entries
            .iter()
            .filter(|entry| !dead(entry.id))
            .cloned()
            .collect();
        Self { entries }
    }

    /// Bounds replay の循環で増え続ける未対応 pop だけを飽和させる。
    /// stack 列は `common_stack` の入力なので、重複や順序をここでは変えない。
    pub fn saturate_unmatched_pops(&self) -> Self {
        let entries = self
            .entries
            .iter()
            .cloned()
            .map(|mut entry| {
                if entry.pops > 0 {
                    entry.pops = u32::MAX;
                }
                entry
            })
            .collect();
        Self { entries }
    }

    fn append(&mut self, other: &Self) {
        for entry in &other.entries {
            self.push_pops(entry.id, entry.pops);
            for subtractability in &entry.stack {
                self.push_stack(entry.id, subtractability.clone());
            }
        }
    }

    fn push_stack(&mut self, id: SubtractId, subtractability: Subtractability) {
        let entry = self.entry_mut(id);
        entry.stack.push(subtractability);
    }

    fn push_pops(&mut self, id: SubtractId, count: u32) {
        if count == 0 {
            return;
        }
        let entry = self.entry_mut(id);
        if count == u32::MAX {
            entry.stack.clear();
            entry.pops = u32::MAX;
            return;
        }
        let removable = entry.stack.len().min(count as usize);
        if removable > 0 {
            entry.stack.truncate(entry.stack.len() - removable);
        }
        let remaining = count.saturating_sub(removable as u32);
        if remaining > 0 {
            entry.pops = entry.pops.saturating_add(remaining);
            if entry.pops == u32::MAX {
                entry.stack.clear();
            }
        }
        self.remove_empty_entry(id);
    }

    fn entry_mut(&mut self, id: SubtractId) -> &mut StackWeightEntry {
        match self.entries.binary_search_by_key(&id.0, |entry| entry.id.0) {
            Ok(index) => &mut self.entries[index],
            Err(index) => {
                self.entries.insert(
                    index,
                    StackWeightEntry {
                        id,
                        pops: 0,
                        stack: Vec::new(),
                    },
                );
                &mut self.entries[index]
            }
        }
    }

    fn remove_empty_entry(&mut self, id: SubtractId) {
        if let Ok(index) = self.entries.binary_search_by_key(&id.0, |entry| entry.id.0)
            && self.entries[index].pops == 0
            && self.entries[index].stack.is_empty()
        {
            self.entries.remove(index);
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// 正側型を指す `TypeArena` 内 ID。
pub struct PosId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// 負側型を指す `TypeArena` 内 ID。
pub struct NegId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// 中立型を指す `TypeArena` 内 ID。
pub struct NeuId(pub u32);

/// 極性分離した型 node を hash-cons する Arena。
///
/// `PosId` / `NegId` / `NeuId` はこの Arena の中だけで意味を持つ。構造を直接 clone して
/// 持ち回るのではなく ID 化することで、制約伝播や scheme freeze の途中で同じ型を共有する。
pub struct TypeArena {
    pos: Vec<Pos>,
    neg: Vec<Neg>,
    neu: Vec<Neu>,
    pos_id: FxHashMap<Pos, PosId>,
    neg_id: FxHashMap<Neg, NegId>,
    neu_id: FxHashMap<Neu, NeuId>,
}

impl TypeArena {
    pub fn new() -> Self {
        Self {
            pos: Vec::new(),
            neg: Vec::new(),
            neu: Vec::new(),
            pos_id: FxHashMap::default(),
            neg_id: FxHashMap::default(),
            neu_id: FxHashMap::default(),
        }
    }
    pub fn alloc_pos(&mut self, pos: Pos) -> PosId {
        if let Some(id) = self.pos_id.get(&pos) {
            return *id;
        }
        let id = PosId(self.pos.len() as u32);
        self.pos.push(pos.clone());
        self.pos_id.insert(pos, id);
        id
    }
    pub fn alloc_neg(&mut self, neg: Neg) -> NegId {
        if let Some(id) = self.neg_id.get(&neg) {
            return *id;
        }
        let id = NegId(self.neg.len() as u32);
        self.neg.push(neg.clone());
        self.neg_id.insert(neg, id);
        id
    }
    pub fn alloc_neu(&mut self, neu: Neu) -> NeuId {
        if let Some(id) = self.neu_id.get(&neu) {
            return *id;
        }
        let id = NeuId(self.neu.len() as u32);
        self.neu.push(neu.clone());
        self.neu_id.insert(neu, id);
        id
    }
    pub fn pos(&self, id: PosId) -> &Pos {
        &self.pos[id.0 as usize]
    }
    pub fn neg(&self, id: NegId) -> &Neg {
        &self.neg[id.0 as usize]
    }
    pub fn neu(&self, id: NeuId) -> &Neu {
        &self.neu[id.0 as usize]
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// 正側の型。
///
/// lower bound として現れる型を表す。`Bot` は bottom 型であり、エラーや未解決 placeholder ではない。
/// 関数型では引数が負側、戻り値が正側になるよう polarity を明示する。
pub enum Pos {
    Bot,
    Var(TypeVar),
    Con(Vec<String>, Vec<NeuId>),
    Fun {
        arg: NegId,
        arg_eff: NegId,
        ret_eff: PosId,
        ret: PosId,
    },
    Record(Vec<RecordField<PosId>>),
    RecordTailSpread {
        fields: Vec<RecordField<PosId>>,
        tail: PosId,
    },
    RecordHeadSpread {
        tail: PosId,
        fields: Vec<RecordField<PosId>>,
    },
    PolyVariant(Vec<(String, Vec<PosId>)>),
    Tuple(Vec<PosId>),
    /// エフェクト行の lower bound。positive 側は tail を分けず、row item を列として持つ。
    Row(Vec<PosId>),
    /// `stack(T, @S)`。effect subtraction の寿命境界を型構造として持つ。
    Stack {
        inner: PosId,
        weight: StackWeight,
    },
    /// 旧 `pop(T, #id)` 糖衣。新しい lowering では `Stack` を使う。
    NonSubtract(PosId, SubtractId),
    Union(PosId, PosId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// 負側の型。
///
/// upper bound として現れる型を表す。`Top` は top 型であり、曖昧さの fallback ではない。
/// 関数型では引数が正側、戻り値が負側になるよう polarity を反転して持つ。
pub enum Neg {
    Top,
    Bot,
    Var(TypeVar),
    Con(Vec<String>, Vec<NeuId>),
    Fun {
        arg: PosId,
        arg_eff: PosId,
        ret_eff: NegId,
        ret: NegId,
    },
    Record(Vec<RecordField<NegId>>),
    PolyVariant(Vec<(String, Vec<NegId>)>),
    Tuple(Vec<NegId>),
    /// エフェクト行。items は要求する具体部分、tail は残差を受ける負側 row。
    Row(Vec<NegId>, NegId),
    /// `stack(T, @S)`。effect subtraction の寿命境界を型構造として持つ。
    Stack {
        inner: NegId,
        weight: StackWeight,
    },
    Intersection(NegId, NegId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// 正負の上下界を挟んだ中立型。
///
/// `Neu::Bounds(lower, var, upper)` は、変数を中心に下界と上界を sandwich として持つ形。
/// finalize / scheme 化で極性をまたぐ情報を残すために使う。
pub enum Neu {
    Bounds(PosId, TypeVar, NegId),
    Con(Vec<String>, Vec<NeuId>),
    Fun {
        arg: NeuId,
        arg_eff: NeuId,
        ret_eff: NeuId,
        ret: NeuId,
    },
    Record(Vec<RecordField<NeuId>>),
    PolyVariant(Vec<(String, Vec<NeuId>)>),
    Tuple(Vec<NeuId>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// record field の共通表現。
///
/// 値の polarity だけを型引数で差し替え、field 名と optional flag の扱いを揃える。
pub struct RecordField<T> {
    pub name: String,
    pub value: T,
    pub optional: bool,
}
