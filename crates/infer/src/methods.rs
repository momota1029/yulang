//! Method selection candidates.
//!
//! Method lookup is driven by type information, not by the surface method name alone.
//! Lowering records a pending selection, and analysis probes this table only after the
//! receiver has a concrete lower bound or effect information.

use poly::expr::DefId;
use rustc_hash::FxHashMap;

use crate::ModuleId;

#[derive(Debug, Clone, Default)]
pub struct TypeMethodTable {
    value_methods: FxHashMap<TypeMethodKey, Vec<TypeMethodCandidate>>,
    ref_methods: FxHashMap<TypeMethodKey, Vec<TypeMethodCandidate>>,
}

impl TypeMethodTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert_value(
        &mut self,
        receiver: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        insert_method(&mut self.value_methods, receiver, method, def);
    }

    pub fn insert_ref(
        &mut self,
        receiver: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        insert_method(&mut self.ref_methods, receiver, method, def);
    }

    pub fn value_candidates(&self, receiver: &[String], method: &str) -> &[TypeMethodCandidate] {
        candidates(&self.value_methods, receiver, method)
    }

    pub fn ref_candidates(&self, receiver: &[String], method: &str) -> &[TypeMethodCandidate] {
        candidates(&self.ref_methods, receiver, method)
    }

    pub fn is_empty(&self) -> bool {
        self.value_methods.is_empty() && self.ref_methods.is_empty()
    }
}

fn insert_method(
    methods: &mut FxHashMap<TypeMethodKey, Vec<TypeMethodCandidate>>,
    receiver: impl Into<Vec<String>>,
    method: impl Into<String>,
    def: DefId,
) {
    let receiver = receiver.into();
    let method = method.into();
    let key = TypeMethodKey {
        receiver: receiver.clone(),
        method: method.clone(),
    };
    methods.entry(key).or_default().push(TypeMethodCandidate {
        receiver,
        method,
        def,
    });
}

fn candidates<'a>(
    methods: &'a FxHashMap<TypeMethodKey, Vec<TypeMethodCandidate>>,
    receiver: &[String],
    method: &str,
) -> &'a [TypeMethodCandidate] {
    methods
        .get(&TypeMethodKey {
            receiver: receiver.to_vec(),
            method: method.to_string(),
        })
        .map(Vec::as_slice)
        .unwrap_or(&[])
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct TypeMethodKey {
    receiver: Vec<String>,
    method: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeMethodCandidate {
    pub receiver: Vec<String>,
    pub method: String,
    pub def: DefId,
}

#[derive(Debug, Clone, Default)]
pub struct EffectMethodTable {
    methods: FxHashMap<String, Vec<EffectMethodCandidate>>,
}

impl EffectMethodTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(
        &mut self,
        effect: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        let effect = effect.into();
        let method = method.into();
        self.methods
            .entry(method.clone())
            .or_default()
            .push(EffectMethodCandidate {
                effect,
                method,
                def,
            });
    }

    pub fn candidates(&self, method: &str) -> &[EffectMethodCandidate] {
        self.methods.get(method).map(Vec::as_slice).unwrap_or(&[])
    }

    pub fn is_empty(&self) -> bool {
        self.methods.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectMethodCandidate {
    pub effect: Vec<String>,
    pub method: String,
    pub def: DefId,
}

#[derive(Debug, Clone, Default)]
pub struct RoleMethodTable {
    methods: FxHashMap<String, Vec<RoleMethodCandidate>>,
}

impl RoleMethodTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, role: impl Into<Vec<String>>, method: impl Into<String>, def: DefId) {
        let role = role.into();
        let method = method.into();
        self.methods
            .entry(method.clone())
            .or_default()
            .push(RoleMethodCandidate { role, method, def });
    }

    pub fn candidates(&self, method: &str) -> &[RoleMethodCandidate] {
        self.methods.get(method).map(Vec::as_slice).unwrap_or(&[])
    }

    pub fn is_empty(&self) -> bool {
        self.methods.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleMethodCandidate {
    pub role: Vec<String>,
    pub method: String,
    pub def: DefId,
}

#[derive(Debug, Clone, Default)]
pub struct CompanionMethodTable {
    type_methods: FxHashMap<ModuleId, TypeMethodTable>,
    effect_methods: FxHashMap<ModuleId, EffectMethodTable>,
    role_methods: FxHashMap<ModuleId, RoleMethodTable>,
}

impl CompanionMethodTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert_value_type_method(
        &mut self,
        scope: ModuleId,
        receiver: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        self.type_methods
            .entry(scope)
            .or_default()
            .insert_value(receiver, method, def);
    }

    pub fn insert_ref_type_method(
        &mut self,
        scope: ModuleId,
        receiver: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        self.type_methods
            .entry(scope)
            .or_default()
            .insert_ref(receiver, method, def);
    }

    pub fn insert_effect_method(
        &mut self,
        scope: ModuleId,
        effect: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        self.effect_methods
            .entry(scope)
            .or_default()
            .insert(effect, method, def);
    }

    pub fn insert_role_method(
        &mut self,
        scope: ModuleId,
        role: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        self.role_methods
            .entry(scope)
            .or_default()
            .insert(role, method, def);
    }

    pub fn value_type_candidates(
        &self,
        scope: ModuleId,
        receiver: &[String],
        method: &str,
    ) -> &[TypeMethodCandidate] {
        self.type_methods
            .get(&scope)
            .map(|methods| methods.value_candidates(receiver, method))
            .unwrap_or(&[])
    }

    pub fn ref_type_candidates(
        &self,
        scope: ModuleId,
        receiver: &[String],
        method: &str,
    ) -> &[TypeMethodCandidate] {
        self.type_methods
            .get(&scope)
            .map(|methods| methods.ref_candidates(receiver, method))
            .unwrap_or(&[])
    }

    pub fn effect_candidates(&self, scope: ModuleId, method: &str) -> &[EffectMethodCandidate] {
        self.effect_methods
            .get(&scope)
            .map(|methods| methods.candidates(method))
            .unwrap_or(&[])
    }

    pub fn role_candidates(&self, scope: ModuleId, method: &str) -> &[RoleMethodCandidate] {
        self.role_methods
            .get(&scope)
            .map(|methods| methods.candidates(method))
            .unwrap_or(&[])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stores_method_candidates_by_receiver_constructor_and_name() {
        let mut table = TypeMethodTable::new();
        let method = DefId(1);

        table.insert_value(vec!["int".into()], "show", method);

        assert_eq!(
            table.value_candidates(&["int".into()], "show")[0].def,
            method
        );
        assert!(table.value_candidates(&["float".into()], "show").is_empty());
        assert!(table.value_candidates(&["int".into()], "parse").is_empty());
        assert!(table.ref_candidates(&["int".into()], "show").is_empty());
    }

    #[test]
    fn stores_ref_method_candidates_separately() {
        let mut table = TypeMethodTable::new();
        let value_method = DefId(1);
        let ref_method = DefId(2);

        table.insert_value(vec!["str".into()], "lines", value_method);
        table.insert_ref(vec!["str".into()], "lines", ref_method);

        assert_eq!(
            table.value_candidates(&["str".into()], "lines")[0].def,
            value_method
        );
        assert_eq!(
            table.ref_candidates(&["str".into()], "lines")[0].def,
            ref_method
        );
    }

    #[test]
    fn stores_effect_method_candidates_by_name() {
        let mut table = EffectMethodTable::new();
        let method = DefId(1);

        table.insert(vec!["nondet".into()], "choose", method);

        assert_eq!(table.candidates("choose")[0].effect, vec!["nondet"]);
        assert_eq!(table.candidates("choose")[0].def, method);
        assert!(table.candidates("other").is_empty());
    }

    #[test]
    fn stores_role_method_candidates_by_name() {
        let mut table = RoleMethodTable::new();
        let method = DefId(1);

        table.insert(vec!["Display".into()], "display", method);

        assert_eq!(table.candidates("display")[0].role, vec!["Display"]);
        assert_eq!(table.candidates("display")[0].def, method);
        assert!(table.candidates("other").is_empty());
    }

    #[test]
    fn stores_companion_local_method_candidates_by_scope() {
        let mut table = CompanionMethodTable::new();
        let first_scope = ModuleId(1);
        let second_scope = ModuleId(2);
        let first = DefId(3);
        let second = DefId(4);

        table.insert_value_type_method(first_scope, vec!["User".into()], "name", first);
        table.insert_value_type_method(second_scope, vec!["User".into()], "name", second);

        assert_eq!(
            table.value_type_candidates(first_scope, &["User".into()], "name")[0].def,
            first
        );
        assert_eq!(
            table.value_type_candidates(second_scope, &["User".into()], "name")[0].def,
            second
        );
    }
}
