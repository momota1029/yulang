//! pattern 名を constructor 参照とローカル束縛へ分ける lowering の入口。
//!
//! Yulang の pattern では、同じ surface 名が「constructor 名」と「新しい変数束縛」の両方に
//! 見えることがある。この module では、まず constructor table を `Name + arity` で引き、
//! 見つかれば `Pat::Con` を作る。constructor 名が存在しない bare name だけを新しい
//! `Def::Arg` として束縛する。
//!
//! ここで作る `Def::Arg` は関数引数や pattern binding の局所 def であり、top-level の
//! 相互再帰 component には入れない。body lowering は `PatternBindings` を local scope に
//! 接続して、参照 use-site 側で必要な型制約だけを作る。

use poly::expr::{Arena as PolyArena, Def, DefId, Pat, PatId, RefId};
use rustc_hash::FxHashMap;
use sources::Name;

/// pattern 名 lowering の小さな入口。
///
/// CST の形を読む処理とは分け、ここでは「この名前と payload 個数をどう IR に置くか」だけを扱う。
/// constructor table は module/import 解決が進むほど増える hook で、初期状態では空でよい。
pub struct PatternLowerer<'a> {
    poly: &'a mut PolyArena,
    constructors: &'a ConstructorTable,
    bindings: &'a mut PatternBindings,
}

impl<'a> PatternLowerer<'a> {
    pub fn new(
        poly: &'a mut PolyArena,
        constructors: &'a ConstructorTable,
        bindings: &'a mut PatternBindings,
    ) -> Self {
        Self {
            poly,
            constructors,
            bindings,
        }
    }

    /// surface pattern 名を `Pat::Con` か `Pat::Var` に lower する。
    ///
    /// arity が 0 でも、同じ名前の nullary constructor があれば constructor を優先する。
    /// constructor 名が見つからない bare name だけが変数束縛になる。payload を持つ名前が
    /// constructor として解けない場合は、暗黙に関数的な変数 pattern へ落とさず error にする。
    pub fn lower_name(
        &mut self,
        name: Name,
        payloads: Vec<PatId>,
    ) -> Result<PatternName, PatternNameError> {
        let arity = payloads.len();
        match self.constructors.resolve(&name, arity) {
            ConstructorLookup::Found(entry) => Ok(self.lower_constructor(entry, payloads)),
            ConstructorLookup::Ambiguous(candidates) => {
                Err(PatternNameError::AmbiguousConstructor {
                    name,
                    arity,
                    candidates,
                })
            }
            ConstructorLookup::ArityMismatch { expected } => {
                Err(PatternNameError::ConstructorArityMismatch {
                    name,
                    actual: arity,
                    expected,
                })
            }
            ConstructorLookup::Missing if arity == 0 => Ok(self.lower_binding(name)),
            ConstructorLookup::Missing => Err(PatternNameError::UnknownConstructor { name, arity }),
        }
    }

    fn lower_constructor(&mut self, entry: ConstructorEntry, payloads: Vec<PatId>) -> PatternName {
        let reference = self.poly.add_ref();
        self.poly.resolve_ref(reference, entry.def);
        let pat = self.poly.add_pat(Pat::Con(reference, payloads));
        PatternName::Constructor {
            pat,
            reference,
            target: entry.def,
        }
    }

    fn lower_binding(&mut self, name: Name) -> PatternName {
        let def = self.poly.defs.fresh();
        self.poly.defs.set(def, Def::Arg);
        self.bindings.insert(name, def);
        let pat = self.poly.add_pat(Pat::Var(def));
        PatternName::Binding { pat, def }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// pattern 名 lowering の成功結果。
pub enum PatternName {
    Constructor {
        pat: PatId,
        reference: RefId,
        target: DefId,
    },
    Binding {
        pat: PatId,
        def: DefId,
    },
}

impl PatternName {
    pub fn pat(self) -> PatId {
        match self {
            Self::Constructor { pat, .. } | Self::Binding { pat, .. } => pat,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// pattern 名を constructor として扱おうとして失敗した理由。
pub enum PatternNameError {
    UnknownConstructor {
        name: Name,
        arity: usize,
    },
    ConstructorArityMismatch {
        name: Name,
        actual: usize,
        expected: Vec<usize>,
    },
    AmbiguousConstructor {
        name: Name,
        arity: usize,
        candidates: Vec<ConstructorEntry>,
    },
}

#[derive(Debug, Clone, Default)]
/// pattern で見える constructor の table。
///
/// 実際の中身は enum / error / typeclass 由来の constructor 宣言を解決してから登録する。
/// この table 自体は名前から候補を絞るだけで、型制約や SCC edge は作らない。
pub struct ConstructorTable {
    constructors: FxHashMap<Name, Vec<ConstructorEntry>>,
}

impl ConstructorTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, name: Name, def: DefId, arity: usize) {
        self.constructors
            .entry(name)
            .or_default()
            .push(ConstructorEntry { def, arity });
    }

    pub fn resolve(&self, name: &Name, arity: usize) -> ConstructorLookup {
        let Some(entries) = self.constructors.get(name) else {
            return ConstructorLookup::Missing;
        };
        let matches = entries
            .iter()
            .copied()
            .filter(|entry| entry.arity == arity)
            .collect::<Vec<_>>();

        match matches.as_slice() {
            [entry] => ConstructorLookup::Found(*entry),
            [] => ConstructorLookup::ArityMismatch {
                expected: expected_arities(entries),
            },
            _ => ConstructorLookup::Ambiguous(matches),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// constructor table の1候補。
pub struct ConstructorEntry {
    pub def: DefId,
    pub arity: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// constructor table lookup の結果。
pub enum ConstructorLookup {
    Found(ConstructorEntry),
    Ambiguous(Vec<ConstructorEntry>),
    ArityMismatch { expected: Vec<usize> },
    Missing,
}

#[derive(Debug, Clone, Default)]
/// 1つの pattern が導入したローカル束縛。
///
/// body resolver はこれを local scope として積む。ここでは insertion order と名前別の最新 def だけを
/// 保つので、SCC machine へは何も送らない。
pub struct PatternBindings {
    order: Vec<PatternBinding>,
    by_name: FxHashMap<Name, Vec<DefId>>,
}

impl PatternBindings {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, name: Name, def: DefId) {
        self.by_name.entry(name.clone()).or_default().push(def);
        self.order.push(PatternBinding { name, def });
    }

    pub fn latest(&self, name: &Name) -> Option<DefId> {
        self.by_name.get(name).and_then(|defs| defs.last().copied())
    }

    pub fn bindings(&self) -> &[PatternBinding] {
        &self.order
    }

    pub fn is_empty(&self) -> bool {
        self.order.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// pattern 内で導入された1つのローカル名。
pub struct PatternBinding {
    pub name: Name,
    pub def: DefId,
}

fn expected_arities(entries: &[ConstructorEntry]) -> Vec<usize> {
    let mut arities = Vec::new();
    for entry in entries {
        if !arities.contains(&entry.arity) {
            arities.push(entry.arity);
        }
    }
    arities.sort_unstable();
    arities
}

#[cfg(test)]
mod tests {
    use super::*;
    use poly::expr::Vis;

    fn name(text: &str) -> Name {
        Name(text.into())
    }

    fn constructor_def(poly: &mut PolyArena) -> DefId {
        let def = poly.defs.fresh();
        poly.defs.set(
            def,
            Def::Let {
                vis: Vis::Our,
                scheme: None,
                body: None,
                children: Vec::new(),
            },
        );
        def
    }

    #[test]
    fn bare_name_without_constructor_binds_local_arg() {
        let mut poly = PolyArena::new();
        let constructors = ConstructorTable::new();
        let mut bindings = PatternBindings::new();

        let lowered = {
            let mut lowerer = PatternLowerer::new(&mut poly, &constructors, &mut bindings);
            lowerer.lower_name(name("x"), Vec::new()).unwrap()
        };

        let PatternName::Binding { pat, def } = lowered else {
            panic!("expected binding pattern");
        };
        assert!(matches!(poly.pat(pat), Pat::Var(actual) if *actual == def));
        assert!(matches!(poly.defs.get(def), Some(Def::Arg)));
        assert_eq!(bindings.latest(&name("x")), Some(def));
    }

    #[test]
    fn nullary_constructor_wins_over_variable_binding() {
        let mut poly = PolyArena::new();
        let none = constructor_def(&mut poly);
        let mut constructors = ConstructorTable::new();
        constructors.insert(name("None"), none, 0);
        let mut bindings = PatternBindings::new();

        let lowered = {
            let mut lowerer = PatternLowerer::new(&mut poly, &constructors, &mut bindings);
            lowerer.lower_name(name("None"), Vec::new()).unwrap()
        };

        let PatternName::Constructor {
            pat,
            reference,
            target,
        } = lowered
        else {
            panic!("expected constructor pattern");
        };
        assert_eq!(target, none);
        assert_eq!(poly.ref_target(reference), Some(none));
        assert!(
            matches!(poly.pat(pat), Pat::Con(actual, payloads) if *actual == reference && payloads.is_empty())
        );
        assert!(bindings.is_empty());
    }

    #[test]
    fn constructor_payload_uses_matching_arity() {
        let mut poly = PolyArena::new();
        let some = constructor_def(&mut poly);
        let payload = poly.add_pat(Pat::Wild);
        let mut constructors = ConstructorTable::new();
        constructors.insert(name("Some"), some, 1);
        let mut bindings = PatternBindings::new();

        let lowered = {
            let mut lowerer = PatternLowerer::new(&mut poly, &constructors, &mut bindings);
            lowerer.lower_name(name("Some"), vec![payload]).unwrap()
        };

        let PatternName::Constructor {
            pat,
            reference,
            target,
        } = lowered
        else {
            panic!("expected constructor pattern");
        };
        assert_eq!(target, some);
        assert_eq!(poly.ref_target(reference), Some(some));
        assert!(
            matches!(poly.pat(pat), Pat::Con(actual, payloads) if *actual == reference && payloads == &vec![payload])
        );
        assert!(bindings.is_empty());
    }

    #[test]
    fn payload_name_without_constructor_is_not_variable_binding() {
        let mut poly = PolyArena::new();
        let payload = poly.add_pat(Pat::Wild);
        let constructors = ConstructorTable::new();
        let mut bindings = PatternBindings::new();

        let error = {
            let mut lowerer = PatternLowerer::new(&mut poly, &constructors, &mut bindings);
            lowerer.lower_name(name("Some"), vec![payload]).unwrap_err()
        };

        assert_eq!(
            error,
            PatternNameError::UnknownConstructor {
                name: name("Some"),
                arity: 1
            }
        );
        assert!(bindings.is_empty());
    }

    #[test]
    fn constructor_name_with_wrong_arity_reports_mismatch() {
        let mut poly = PolyArena::new();
        let some = constructor_def(&mut poly);
        let mut constructors = ConstructorTable::new();
        constructors.insert(name("Some"), some, 1);
        let mut bindings = PatternBindings::new();

        let error = {
            let mut lowerer = PatternLowerer::new(&mut poly, &constructors, &mut bindings);
            lowerer.lower_name(name("Some"), Vec::new()).unwrap_err()
        };

        assert_eq!(
            error,
            PatternNameError::ConstructorArityMismatch {
                name: name("Some"),
                actual: 0,
                expected: vec![1],
            }
        );
        assert!(bindings.is_empty());
    }
}
