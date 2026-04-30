use crate::ids::{NegId, PosId, TypeVar};
use crate::symbols::{Name, Path};

pub mod arena;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Variance {
    Invariant,
    Covariant,
    Contravariant,
}

/// エフェクト行の中のひとつのエフェクト。
/// 型引数は (pos側の型変数, neg側の型変数) のペア。
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EffectAtom {
    pub path: Path,
    pub args: Vec<(TypeVar, TypeVar)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecordField<T> {
    pub name: Name,
    pub value: T,
    pub optional: bool,
}

impl<T> RecordField<T> {
    pub fn required(name: Name, value: T) -> Self {
        Self {
            name,
            value,
            optional: false,
        }
    }

    pub fn optional(name: Name, value: T) -> Self {
        Self {
            name,
            value,
            optional: true,
        }
    }
}

/// 正側の型（下界・生産側）
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Pos {
    Bot,
    Var(TypeVar),
    Atom(EffectAtom),
    Forall(Vec<TypeVar>, PosId),
    Con(Path, Vec<(PosId, NegId)>),
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
    PolyVariant(Vec<(Name, Vec<PosId>)>),
    Tuple(Vec<PosId>),
    /// エフェクト行。items は既知の具体部分、tail は残りの正側 row。
    Row(Vec<PosId>, PosId),
    Union(PosId, PosId),
    /// row splice 変数。`[e]` のように行の中で「e が表すエフェクト列をここに展開する」
    /// ことを意味する。Pos::Var とは区別し、constrain_row でのみ特別処理する。
    Raw(TypeVar),
}

/// 負側の型（上界・消費側）
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Neg {
    Top,
    Var(TypeVar),
    Atom(EffectAtom),
    Forall(Vec<TypeVar>, NegId),
    Con(Path, Vec<(PosId, NegId)>),
    Fun {
        arg: PosId,
        arg_eff: PosId,
        ret_eff: NegId,
        ret: NegId,
    },
    Record(Vec<RecordField<NegId>>),
    PolyVariant(Vec<(Name, Vec<NegId>)>),
    Tuple(Vec<NegId>),
    /// エフェクト行。items は要求する具体部分、tail は残差を受ける負側 row。
    Row(Vec<NegId>, NegId),
    Intersection(NegId, NegId),
}

impl Pos {
    /// TypeVar への参照を収集する（arena なしでアクセス可能なバリアントのみ）。
    /// PosId を含むバリアントは arena 経由で再帰する必要があるため、
    /// arena を持つ側（constrain.rs 等）で別途実装すること。
    pub fn direct_free_vars(&self) -> Vec<TypeVar> {
        match self {
            Pos::Bot => vec![],
            Pos::Var(tv) | Pos::Raw(tv) => vec![*tv],
            Pos::Atom(a) => a.collect_free_vars_vec(),
            _ => vec![],
        }
    }
}

impl Neg {
    pub fn direct_free_vars(&self) -> Vec<TypeVar> {
        match self {
            Neg::Top => vec![],
            Neg::Var(tv) => vec![*tv],
            Neg::Atom(a) => a.collect_free_vars_vec(),
            _ => vec![],
        }
    }
}

impl EffectAtom {
    fn collect_free_vars(&self, out: &mut Vec<TypeVar>) {
        for (pos, neg) in &self.args {
            push_unique(out, *pos);
            push_unique(out, *neg);
        }
    }

    fn collect_free_vars_vec(&self) -> Vec<TypeVar> {
        let mut out = Vec::new();
        self.collect_free_vars(&mut out);
        out
    }
}

fn push_unique(out: &mut Vec<TypeVar>, tv: TypeVar) {
    if !out.contains(&tv) {
        out.push(tv);
    }
}
