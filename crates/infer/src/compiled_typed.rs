use poly::expr::{Arena as PolyArena, Def, DefId, Vis};
use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, RoleAssociatedType, RolePredicate,
    RolePredicateArg, Scheme, SchemeRecursiveBound, StackWeight, SubtractId, Subtractability,
    TypeArena, TypeVar,
};
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use sources::{Name, Path};

use crate::Arena as InferArena;
use crate::lowering::BodyLowering;
use crate::{
    CompiledNamespaceSurface, CompiledNamespaceValueVisibility, CompiledNamespaceVisibility,
};

#[derive(Clone, Serialize, Deserialize)]
pub struct CompiledTypedSurface {
    pub types: CompiledTypeArena,
    pub values: Vec<CompiledTypedValueScheme>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct CompiledTypeArena {
    pub pos: Vec<Pos>,
    pub neg: Vec<Neg>,
    pub neu: Vec<Neu>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct CompiledTypedValueScheme {
    pub symbol: u32,
    pub scheme: Scheme,
}

pub struct CompiledValueImport {
    pub values: Vec<CompiledImportedValue>,
}

pub struct CompiledImportedValue {
    pub symbol: u32,
    pub def: DefId,
}

pub struct CompiledUnitImport {
    pub values: CompiledValueImport,
    exported_values: FxHashMap<Vec<String>, FxHashMap<String, DefId>>,
}

impl CompiledUnitImport {
    pub fn exported_value_def(&self, module_path: &[String], name: &str) -> Option<DefId> {
        self.exported_values
            .get(module_path)
            .and_then(|values| values.get(name))
            .copied()
    }
}

pub struct CompiledTypedIndex<'a> {
    surface: &'a CompiledTypedSurface,
    values_by_symbol: FxHashMap<u32, usize>,
}

impl<'a> CompiledTypedIndex<'a> {
    pub fn new(surface: &'a CompiledTypedSurface) -> Self {
        Self {
            surface,
            values_by_symbol: surface
                .values
                .iter()
                .enumerate()
                .map(|(index, value)| (value.symbol, index))
                .collect(),
        }
    }

    pub fn value_scheme(&self, symbol: u32) -> Option<&'a Scheme> {
        let index = *self.values_by_symbol.get(&symbol)?;
        Some(&self.surface.values.get(index)?.scheme)
    }
}

impl CompiledTypedSurface {
    pub fn from_lowering(lowering: &BodyLowering, namespace: &CompiledNamespaceSurface) -> Self {
        let mut values = Vec::new();
        for module in &namespace.modules {
            let Some(live_module) = lowering
                .modules
                .module_by_path(&path_from_strings(&module.path))
            else {
                continue;
            };
            for value in module
                .values
                .iter()
                .filter(|value| value.visibility != CompiledNamespaceVisibility::My)
            {
                let name = Name(value.name.clone());
                let Some(def) = lowering
                    .modules
                    .value_decls(live_module, &name)
                    .into_iter()
                    .find(|decl| decl.order.index() == value.order)
                    .map(|decl| decl.def)
                else {
                    continue;
                };
                let Some(Def::Let {
                    vis,
                    scheme: Some(scheme),
                    ..
                }) = lowering.session.poly.defs.get(def)
                else {
                    continue;
                };
                if *vis == Vis::My {
                    continue;
                }
                values.push(CompiledTypedValueScheme {
                    symbol: value.symbol,
                    scheme: scheme.clone(),
                });
            }
        }
        values.sort_by_key(|value| value.symbol);
        Self {
            types: CompiledTypeArena::from_type_arena(lowering.session.infer.constraints().types()),
            values,
        }
    }

    pub fn import_value_defs(
        &self,
        namespace: &CompiledNamespaceSurface,
        poly: &mut PolyArena,
        infer: &mut InferArena,
    ) -> CompiledValueImport {
        let mut type_importer = CompiledTypeImporter::new(&self.types, infer);
        let values = self
            .values
            .iter()
            .filter_map(|value| {
                let visibility = namespace.value_visibility(value.symbol)?;
                let def = poly.defs.fresh();
                poly.defs.set(
                    def,
                    Def::Let {
                        vis: compiled_value_visibility(visibility),
                        scheme: Some(type_importer.import_scheme(&value.scheme)),
                        body: None,
                        children: Vec::new(),
                    },
                );
                Some(CompiledImportedValue {
                    symbol: value.symbol,
                    def,
                })
            })
            .collect();
        CompiledValueImport { values }
    }

    pub fn import_unit(
        &self,
        namespace: &CompiledNamespaceSurface,
        poly: &mut PolyArena,
        infer: &mut InferArena,
    ) -> CompiledUnitImport {
        let values = self.import_value_defs(namespace, poly, infer);
        let value_defs = values
            .values
            .iter()
            .map(|value| (value.symbol, value.def))
            .collect::<FxHashMap<_, _>>();
        let mut exported_values = FxHashMap::default();
        for module in &namespace.modules {
            for value in module
                .values
                .iter()
                .filter(|value| value.visibility != CompiledNamespaceVisibility::My)
            {
                let Some(def) = value_defs.get(&value.symbol).copied() else {
                    continue;
                };
                exported_values
                    .entry(module.path.clone())
                    .or_insert_with(FxHashMap::default)
                    .insert(value.name.clone(), def);
            }
            for value in module
                .imported_values
                .iter()
                .filter(|value| value.visibility != CompiledNamespaceVisibility::My)
            {
                let Some(def) = value_defs.get(&value.symbol).copied() else {
                    continue;
                };
                exported_values
                    .entry(module.path.clone())
                    .or_insert_with(FxHashMap::default)
                    .insert(value.name.clone(), def);
            }
        }
        CompiledUnitImport {
            values,
            exported_values,
        }
    }
}

fn compiled_value_visibility(visibility: CompiledNamespaceValueVisibility) -> Vis {
    match visibility {
        CompiledNamespaceValueVisibility::Pub => Vis::Pub,
        CompiledNamespaceValueVisibility::Our => Vis::Our,
    }
}

impl CompiledTypeArena {
    pub fn from_type_arena(types: &TypeArena) -> Self {
        Self {
            pos: types.pos_nodes().to_vec(),
            neg: types.neg_nodes().to_vec(),
            neu: types.neu_nodes().to_vec(),
        }
    }

    pub fn to_type_arena(&self) -> TypeArena {
        let mut types = TypeArena::new();
        for (index, node) in self.pos.iter().enumerate() {
            let id = types.alloc_pos(node.clone());
            debug_assert_eq!(id.0 as usize, index);
        }
        for (index, node) in self.neg.iter().enumerate() {
            let id = types.alloc_neg(node.clone());
            debug_assert_eq!(id.0 as usize, index);
        }
        for (index, node) in self.neu.iter().enumerate() {
            let id = types.alloc_neu(node.clone());
            debug_assert_eq!(id.0 as usize, index);
        }
        types
    }
}

pub struct CompiledTypeImporter<'a, 'b> {
    source: &'a CompiledTypeArena,
    target: &'b mut InferArena,
    pos: FxHashMap<PosId, PosId>,
    neg: FxHashMap<NegId, NegId>,
    neu: FxHashMap<NeuId, NeuId>,
    vars: FxHashMap<TypeVar, TypeVar>,
    subtracts: FxHashMap<SubtractId, SubtractId>,
}

impl<'a, 'b> CompiledTypeImporter<'a, 'b> {
    pub fn new(source: &'a CompiledTypeArena, target: &'b mut InferArena) -> Self {
        Self {
            source,
            target,
            pos: FxHashMap::default(),
            neg: FxHashMap::default(),
            neu: FxHashMap::default(),
            vars: FxHashMap::default(),
            subtracts: FxHashMap::default(),
        }
    }

    pub fn import_scheme(&mut self, scheme: &Scheme) -> Scheme {
        Scheme {
            quantifiers: scheme
                .quantifiers
                .iter()
                .map(|var| self.map_type_var(*var))
                .collect(),
            role_predicates: scheme
                .role_predicates
                .iter()
                .map(|predicate| self.import_role_predicate(predicate))
                .collect(),
            recursive_bounds: scheme
                .recursive_bounds
                .iter()
                .map(|bound| SchemeRecursiveBound {
                    var: self.map_type_var(bound.var),
                    bounds: self.import_neu_id(bound.bounds),
                })
                .collect(),
            stack_quantifiers: scheme
                .stack_quantifiers
                .iter()
                .map(|id| self.map_subtract_id(*id))
                .collect(),
            predicate: self.import_pos_id(scheme.predicate),
        }
    }

    fn import_pos_id(&mut self, id: PosId) -> PosId {
        if let Some(mapped) = self.pos.get(&id) {
            return *mapped;
        }
        let node = self
            .source
            .pos
            .get(id.0 as usize)
            .unwrap_or_else(|| panic!("compiled positive type id {} is missing", id.0))
            .clone();
        let mapped = self.import_pos(node);
        self.pos.insert(id, mapped);
        mapped
    }

    fn import_neg_id(&mut self, id: NegId) -> NegId {
        if let Some(mapped) = self.neg.get(&id) {
            return *mapped;
        }
        let node = self
            .source
            .neg
            .get(id.0 as usize)
            .unwrap_or_else(|| panic!("compiled negative type id {} is missing", id.0))
            .clone();
        let mapped = self.import_neg(node);
        self.neg.insert(id, mapped);
        mapped
    }

    fn import_neu_id(&mut self, id: NeuId) -> NeuId {
        if let Some(mapped) = self.neu.get(&id) {
            return *mapped;
        }
        let node = self
            .source
            .neu
            .get(id.0 as usize)
            .unwrap_or_else(|| panic!("compiled neutral type id {} is missing", id.0))
            .clone();
        let mapped = self.import_neu(node);
        self.neu.insert(id, mapped);
        mapped
    }

    fn import_pos(&mut self, pos: Pos) -> PosId {
        let mapped = match pos {
            Pos::Bot => Pos::Bot,
            Pos::Var(var) => Pos::Var(self.map_type_var(var)),
            Pos::Con(path, args) => Pos::Con(path, self.import_neu_ids(args)),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => Pos::Fun {
                arg: self.import_neg_id(arg),
                arg_eff: self.import_neg_id(arg_eff),
                ret_eff: self.import_pos_id(ret_eff),
                ret: self.import_pos_id(ret),
            },
            Pos::Record(fields) => {
                Pos::Record(self.import_record_fields(fields, Self::import_pos_id))
            }
            Pos::RecordTailSpread { fields, tail } => Pos::RecordTailSpread {
                fields: self.import_record_fields(fields, Self::import_pos_id),
                tail: self.import_pos_id(tail),
            },
            Pos::RecordHeadSpread { tail, fields } => Pos::RecordHeadSpread {
                tail: self.import_pos_id(tail),
                fields: self.import_record_fields(fields, Self::import_pos_id),
            },
            Pos::PolyVariant(variants) => Pos::PolyVariant(
                variants
                    .into_iter()
                    .map(|(name, payloads)| (name, self.import_pos_ids(payloads)))
                    .collect(),
            ),
            Pos::Tuple(items) => Pos::Tuple(self.import_pos_ids(items)),
            Pos::Row(items) => Pos::Row(self.import_pos_ids(items)),
            Pos::Stack { inner, weight } => Pos::Stack {
                inner: self.import_pos_id(inner),
                weight: self.import_stack_weight(&weight),
            },
            Pos::NonSubtract(inner, weight) => {
                Pos::NonSubtract(self.import_pos_id(inner), self.import_stack_weight(&weight))
            }
            Pos::Union(left, right) => {
                Pos::Union(self.import_pos_id(left), self.import_pos_id(right))
            }
        };
        self.target.alloc_pos(mapped)
    }

    fn import_neg(&mut self, neg: Neg) -> NegId {
        let mapped = match neg {
            Neg::Top => Neg::Top,
            Neg::Bot => Neg::Bot,
            Neg::Var(var) => Neg::Var(self.map_type_var(var)),
            Neg::Con(path, args) => Neg::Con(path, self.import_neu_ids(args)),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => Neg::Fun {
                arg: self.import_pos_id(arg),
                arg_eff: self.import_pos_id(arg_eff),
                ret_eff: self.import_neg_id(ret_eff),
                ret: self.import_neg_id(ret),
            },
            Neg::Record(fields) => {
                Neg::Record(self.import_record_fields(fields, Self::import_neg_id))
            }
            Neg::PolyVariant(variants) => Neg::PolyVariant(
                variants
                    .into_iter()
                    .map(|(name, payloads)| (name, self.import_neg_ids(payloads)))
                    .collect(),
            ),
            Neg::Tuple(items) => Neg::Tuple(self.import_neg_ids(items)),
            Neg::Row(items, tail) => Neg::Row(self.import_neg_ids(items), self.import_neg_id(tail)),
            Neg::Stack { inner, weight } => Neg::Stack {
                inner: self.import_neg_id(inner),
                weight: self.import_stack_weight(&weight),
            },
            Neg::Intersection(left, right) => {
                Neg::Intersection(self.import_neg_id(left), self.import_neg_id(right))
            }
        };
        self.target.alloc_neg(mapped)
    }

    fn import_neu(&mut self, neu: Neu) -> NeuId {
        let mapped = match neu {
            Neu::Bounds(lower, upper) => {
                Neu::Bounds(self.import_pos_id(lower), self.import_neg_id(upper))
            }
            Neu::Con(path, args) => Neu::Con(path, self.import_neu_ids(args)),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => Neu::Fun {
                arg: self.import_neu_id(arg),
                arg_eff: self.import_neu_id(arg_eff),
                ret_eff: self.import_neu_id(ret_eff),
                ret: self.import_neu_id(ret),
            },
            Neu::Record(fields) => {
                Neu::Record(self.import_record_fields(fields, Self::import_neu_id))
            }
            Neu::PolyVariant(variants) => Neu::PolyVariant(
                variants
                    .into_iter()
                    .map(|(name, payloads)| (name, self.import_neu_ids(payloads)))
                    .collect(),
            ),
            Neu::Tuple(items) => Neu::Tuple(self.import_neu_ids(items)),
        };
        self.target.alloc_neu(mapped)
    }

    fn import_role_predicate(&mut self, predicate: &RolePredicate) -> RolePredicate {
        RolePredicate {
            role: predicate.role.clone(),
            inputs: predicate
                .inputs
                .iter()
                .map(|input| match input {
                    RolePredicateArg::Covariant(id) => {
                        RolePredicateArg::Covariant(self.import_pos_id(*id))
                    }
                    RolePredicateArg::Contravariant(id) => {
                        RolePredicateArg::Contravariant(self.import_neg_id(*id))
                    }
                    RolePredicateArg::Invariant(id) => {
                        RolePredicateArg::Invariant(self.import_neu_id(*id))
                    }
                })
                .collect(),
            associated: predicate
                .associated
                .iter()
                .map(|associated| RoleAssociatedType {
                    name: associated.name.clone(),
                    value: self.import_neu_id(associated.value),
                })
                .collect(),
        }
    }

    fn import_stack_weight(&mut self, weight: &StackWeight) -> StackWeight {
        let mut out = StackWeight::filter(self.import_subtractability(weight.filter_set()));
        for entry in weight.entries() {
            if entry.pops > 0 {
                out = out.compose(&StackWeight::pops(
                    self.map_subtract_id(entry.id),
                    entry.pops,
                ));
            }
            for floor in &entry.floor {
                out = out.compose(&StackWeight::floor(
                    self.map_subtract_id(entry.id),
                    self.import_subtractability(floor),
                ));
            }
            for stack in &entry.stack {
                out = out.compose(&StackWeight::push(
                    self.map_subtract_id(entry.id),
                    self.import_subtractability(stack),
                ));
            }
        }
        out
    }

    fn import_subtractability(&mut self, subtractability: &Subtractability) -> Subtractability {
        match subtractability {
            Subtractability::Empty => Subtractability::Empty,
            Subtractability::All => Subtractability::All,
            Subtractability::AllExcept(path, args) => {
                Subtractability::AllExcept(path.clone(), self.import_neu_ids(args.clone()))
            }
            Subtractability::AllExceptMany(families) => Subtractability::AllExceptMany(
                families
                    .iter()
                    .map(|(path, args)| (path.clone(), self.import_neu_ids(args.clone())))
                    .collect(),
            ),
            Subtractability::Set(path, args) => {
                Subtractability::Set(path.clone(), self.import_neu_ids(args.clone()))
            }
            Subtractability::SetMany(families) => Subtractability::SetMany(
                families
                    .iter()
                    .map(|(path, args)| (path.clone(), self.import_neu_ids(args.clone())))
                    .collect(),
            ),
        }
    }

    fn import_record_fields<T: Copy, U>(
        &mut self,
        fields: Vec<RecordField<T>>,
        import: fn(&mut Self, T) -> U,
    ) -> Vec<RecordField<U>> {
        fields
            .into_iter()
            .map(|field| RecordField {
                name: field.name,
                value: import(self, field.value),
                optional: field.optional,
            })
            .collect()
    }

    fn import_pos_ids(&mut self, ids: Vec<PosId>) -> Vec<PosId> {
        ids.into_iter().map(|id| self.import_pos_id(id)).collect()
    }

    fn import_neg_ids(&mut self, ids: Vec<NegId>) -> Vec<NegId> {
        ids.into_iter().map(|id| self.import_neg_id(id)).collect()
    }

    fn import_neu_ids(&mut self, ids: Vec<NeuId>) -> Vec<NeuId> {
        ids.into_iter().map(|id| self.import_neu_id(id)).collect()
    }

    fn map_type_var(&mut self, var: TypeVar) -> TypeVar {
        *self
            .vars
            .entry(var)
            .or_insert_with(|| self.target.fresh_type_var())
    }

    fn map_subtract_id(&mut self, id: SubtractId) -> SubtractId {
        *self
            .subtracts
            .entry(id)
            .or_insert_with(|| self.target.fresh_subtract_id())
    }
}

fn path_from_strings(path: &[String]) -> Path {
    Path {
        segments: path.iter().cloned().map(Name).collect(),
    }
}

#[cfg(test)]
mod tests {
    use sources::SourceFile;

    use crate::lowering::lower_loaded_files;

    use super::*;

    #[test]
    fn typed_surface_records_exported_value_schemes_by_namespace_symbol() {
        let loaded = sources::load(vec![
            source(&[], "mod ops;\npub use ops::*\n"),
            source(&["ops"], "pub id x = x\npub x = 42\nmy hidden = 0\n"),
        ]);
        let lowering = lower_loaded_files(&loaded).unwrap();
        let namespace = CompiledNamespaceSurface::from_module_table(&lowering.modules);
        let typed = CompiledTypedSurface::from_lowering(&lowering, &namespace);
        let ops_path = vec!["ops".to_string()];
        let ops = namespace
            .modules
            .iter()
            .find(|module| module.path == ops_path)
            .unwrap();
        let x = ops.values.iter().find(|value| value.name == "x").unwrap();
        let id = ops.values.iter().find(|value| value.name == "id").unwrap();
        let hidden = ops
            .values
            .iter()
            .find(|value| value.name == "hidden")
            .unwrap();

        assert!(typed.values.iter().any(|value| value.symbol == x.symbol));
        assert!(
            !typed
                .values
                .iter()
                .any(|value| value.symbol == hidden.symbol)
        );

        let index = CompiledTypedIndex::new(&typed);
        assert!(index.value_scheme(x.symbol).is_some());
        assert!(index.value_scheme(hidden.symbol).is_none());

        let imported = {
            let source_scheme = index.value_scheme(id.symbol).unwrap();
            let mut target = crate::Arena::new();
            let mut importer = CompiledTypeImporter::new(&typed.types, &mut target);
            let imported = importer.import_scheme(source_scheme);
            let fresh_after_import = target.fresh_type_var();

            assert!(!source_scheme.quantifiers.is_empty());
            assert_ne!(imported.quantifiers, source_scheme.quantifiers);
            assert!(!imported.quantifiers.contains(&fresh_after_import));
            imported
        };
        assert_eq!(
            imported.quantifiers.len(),
            index.value_scheme(id.symbol).unwrap().quantifiers.len()
        );

        let mut poly = PolyArena::new();
        let mut infer = crate::Arena::new();
        let imported_unit = typed.import_unit(&namespace, &mut poly, &mut infer);
        let imported_id = imported_unit.exported_value_def(&ops_path, "id").unwrap();
        assert_eq!(
            imported_unit.exported_value_def(&[], "id"),
            Some(imported_id)
        );
        assert_eq!(imported_unit.exported_value_def(&ops_path, "hidden"), None);
        let Some(Def::Let {
            vis: Vis::Pub,
            scheme: Some(imported_scheme),
            body: None,
            ..
        }) = poly.defs.get(imported_id)
        else {
            panic!("expected imported public bodyless let with a scheme");
        };
        assert_eq!(
            imported_scheme.quantifiers.len(),
            index.value_scheme(id.symbol).unwrap().quantifiers.len()
        );

        let restored_types = typed.types.to_type_arena();
        assert_eq!(
            restored_types.node_len(),
            lowering.session.infer.constraints().types().node_len()
        );
    }

    fn source(module: &[&str], text: &str) -> SourceFile {
        SourceFile {
            module_path: Path {
                segments: module
                    .iter()
                    .map(|segment| Name((*segment).to_string()))
                    .collect(),
            },
            source: text.to_string(),
        }
    }
}
