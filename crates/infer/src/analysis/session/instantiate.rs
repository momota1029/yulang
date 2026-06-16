use super::*;

impl AnalysisSession {
    pub(super) fn constrain_open_use(&mut self, target_root: TypeVar, use_value: TypeVar) {
        let target_pos = self.infer.alloc_pos(Pos::Var(target_root));
        let use_neg = self.infer.alloc_neg(Neg::Var(use_value));
        self.infer.subtype(target_pos, use_neg);
    }

    pub(super) fn quantify_component(&mut self, component: &[DefId], roots: &[TypeVar]) {
        let mut generalized = Vec::with_capacity(component.len());
        for (def, root) in component.iter().copied().zip(roots.iter().copied()) {
            let scheme = self.generalize_root_with_prepasses(def, root);
            self.collect_role_impl_member_prerequisites(def, &scheme);
            generalized.push((def, scheme));
        }

        for (def, scheme) in &generalized {
            self.schemes.insert(*def, scheme.clone());
        }

        for (def, scheme) in generalized {
            let ancestors = self.scheme_ancestors(def);
            let ancestors = ancestors.iter().collect::<Vec<_>>();
            let finalized = finalize_generalized_compact_root_with_ancestors(
                &mut self.poly.typ,
                self.infer.constraints(),
                &scheme,
                &ancestors,
            );
            self.trace_scheme(def, &finalized.scheme);
            self.set_def_scheme(def, finalized.scheme);
        }
    }

    pub(super) fn collect_role_impl_member_prerequisites(
        &mut self,
        def: DefId,
        scheme: &GeneralizedCompactRoot,
    ) {
        let Some(impl_def) = self.role_impl_members.get(&def).copied() else {
            return;
        };
        let quantifiers = scheme.quantifiers.iter().copied().collect::<FxHashSet<_>>();
        let mut compact = scheme.compact.clone();
        let mut role_predicates = scheme.role_predicates.clone();
        apply_compact_simplifications_to_root_and_roles(
            &mut compact,
            &mut role_predicates,
            &[CompactSimplification {
                substitutions: scheme.substitutions.clone(),
                sandwiches: scheme.sandwiches.clone(),
            }],
        );
        if let Some(projection) = self.role_impl_member_projections.get(&def) {
            let substitutions = role_impl_member_projection_substitutions(&compact, projection);
            apply_compact_simplifications_to_root_and_roles(
                &mut compact,
                &mut role_predicates,
                &[CompactSimplification {
                    substitutions,
                    sandwiches: Vec::new(),
                }],
            );
        }
        let mut prerequisites = Vec::new();
        for role in &role_predicates {
            let prerequisite = self.finalize_compact_role_constraint(role);
            let vars = prerequisite.raw_vars(self.infer.constraints().types());
            if vars.iter().any(|var| !quantifiers.contains(var)) {
                prerequisites.push(prerequisite);
            }
        }
        self.role_impls
            .extend_prerequisites_for_impl(impl_def, prerequisites);
    }

    /// Copy solved role impl candidates from inference arena types into final poly types.
    pub fn finalize_poly_role_impls(&mut self) {
        let candidates = self
            .role_impls
            .iter()
            .map(|candidate| {
                clone_role_impl_candidate_between_arenas(
                    self.infer.constraints().types(),
                    &mut self.poly.typ,
                    candidate,
                )
            })
            .collect::<Vec<_>>();
        self.poly.role_impls = RoleImplTable::new();
        for candidate in candidates {
            self.poly.role_impls.insert(candidate);
        }
    }

    pub(super) fn instantiate_use(&mut self, parent: DefId, target: DefId, use_value: TypeVar) {
        let Some(scheme) = self.def_scheme(target).cloned() else {
            return;
        };
        self.trace_scheme(target, &scheme);
        let trace = analysis_trace_mode();
        let start = Instant::now();
        if trace == AnalysisTraceMode::Verbose {
            eprintln!(
                "[analysis] instantiate use start: parent={parent:?} target={target:?} use={use_value:?} quantifiers={} roles={} recursive_bounds={} stack_quantifiers={}",
                scheme.quantifiers.len(),
                scheme.role_predicates.len(),
                scheme.recursive_bounds.len(),
                scheme.stack_quantifiers.len()
            );
        }
        let phase = Instant::now();
        let instantiated = instantiate_scheme_with_roles(
            &self.poly.typ,
            &mut self.infer,
            TypeLevel::secondary(),
            &scheme,
        );
        trace_instantiate_phase(
            trace,
            "clone scheme",
            parent,
            target,
            phase.elapsed(),
            start,
        );
        let phase = Instant::now();
        let use_upper = self.infer.alloc_neg(Neg::Var(use_value));
        self.infer.subtype(instantiated.predicate, use_upper);
        trace_instantiate_phase(
            trace,
            "subtype predicate",
            parent,
            target,
            phase.elapsed(),
            start,
        );
        let phase = Instant::now();
        self.insert_instantiated_role_predicates(parent, &instantiated.role_predicates);
        trace_instantiate_phase(
            trace,
            "insert roles",
            parent,
            target,
            phase.elapsed(),
            start,
        );
    }

    pub(super) fn trace_scheme(&self, target: DefId, scheme: &Scheme) {
        if !trace_scheme_requested(target) {
            return;
        }
        eprintln!(
            "[analysis] scheme {target:?}: {}",
            poly::dump::format_scheme(&self.poly.typ, scheme)
        );
        for line in poly::dump::dump_scheme_raw(&self.poly.typ, scheme).lines() {
            eprintln!("[analysis] scheme {target:?} raw: {line}");
        }
    }

    pub(super) fn insert_instantiated_role_predicates(
        &mut self,
        owner: DefId,
        predicates: &[RolePredicate],
    ) {
        for predicate in predicates {
            let constraint = self.role_constraint_from_predicate(predicate);
            self.roles.insert(owner, constraint);
        }
    }

    pub(super) fn role_constraint_from_predicate(
        &mut self,
        predicate: &RolePredicate,
    ) -> RoleConstraint {
        RoleConstraint {
            role: predicate.role.clone(),
            inputs: predicate
                .inputs
                .iter()
                .map(|input| self.role_arg_from_predicate_arg(*input))
                .collect(),
            associated: predicate
                .associated
                .iter()
                .map(|associated| RoleAssociatedConstraint {
                    name: associated.name.clone(),
                    value: self.role_arg_from_neu(associated.value),
                })
                .collect(),
        }
    }

    pub(super) fn role_arg_from_predicate_arg(
        &mut self,
        arg: RolePredicateArg,
    ) -> RoleConstraintArg {
        match arg {
            RolePredicateArg::Covariant(lower) => RoleConstraintArg {
                lower,
                upper: self.infer.alloc_neg(Neg::Top),
            },
            RolePredicateArg::Contravariant(upper) => RoleConstraintArg {
                lower: self.infer.alloc_pos(Pos::Bot),
                upper,
            },
            RolePredicateArg::Invariant(neu) => self.role_arg_from_neu(neu),
        }
    }

    pub(super) fn role_arg_from_neu(&mut self, id: NeuId) -> RoleConstraintArg {
        match self.infer.constraints().types().neu(id).clone() {
            Neu::Bounds(lower, upper) => RoleConstraintArg { lower, upper },
            neu => RoleConstraintArg {
                lower: self.pos_from_neu(neu.clone()),
                upper: self.neg_from_neu(neu),
            },
        }
    }

    pub(super) fn pos_from_neu(&mut self, neu: Neu) -> PosId {
        let pos = match neu {
            Neu::Bounds(lower, _) => return lower,
            Neu::Con(path, args) => Pos::Con(path, args),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => Pos::Fun {
                arg: self.neg_from_neu_id(arg),
                arg_eff: self.neg_from_neu_id(arg_eff),
                ret_eff: self.pos_from_neu_id(ret_eff),
                ret: self.pos_from_neu_id(ret),
            },
            Neu::Record(fields) => Pos::Record(
                fields
                    .into_iter()
                    .map(|field| RecordField {
                        name: field.name,
                        value: self.pos_from_neu_id(field.value),
                        optional: field.optional,
                    })
                    .collect(),
            ),
            Neu::PolyVariant(items) => Pos::PolyVariant(
                items
                    .into_iter()
                    .map(|(name, payloads)| {
                        (
                            name,
                            payloads
                                .into_iter()
                                .map(|payload| self.pos_from_neu_id(payload))
                                .collect(),
                        )
                    })
                    .collect(),
            ),
            Neu::Tuple(items) => Pos::Tuple(
                items
                    .into_iter()
                    .map(|item| self.pos_from_neu_id(item))
                    .collect(),
            ),
        };
        self.infer.alloc_pos(pos)
    }

    pub(super) fn neg_from_neu(&mut self, neu: Neu) -> NegId {
        let neg = match neu {
            Neu::Bounds(_, upper) => return upper,
            Neu::Con(path, args) => Neg::Con(path, args),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => Neg::Fun {
                arg: self.pos_from_neu_id(arg),
                arg_eff: self.pos_from_neu_id(arg_eff),
                ret_eff: self.neg_from_neu_id(ret_eff),
                ret: self.neg_from_neu_id(ret),
            },
            Neu::Record(fields) => Neg::Record(
                fields
                    .into_iter()
                    .map(|field| RecordField {
                        name: field.name,
                        value: self.neg_from_neu_id(field.value),
                        optional: field.optional,
                    })
                    .collect(),
            ),
            Neu::PolyVariant(items) => Neg::PolyVariant(
                items
                    .into_iter()
                    .map(|(name, payloads)| {
                        (
                            name,
                            payloads
                                .into_iter()
                                .map(|payload| self.neg_from_neu_id(payload))
                                .collect(),
                        )
                    })
                    .collect(),
            ),
            Neu::Tuple(items) => Neg::Tuple(
                items
                    .into_iter()
                    .map(|item| self.neg_from_neu_id(item))
                    .collect(),
            ),
        };
        self.infer.alloc_neg(neg)
    }

    pub(super) fn pos_from_neu_id(&mut self, id: NeuId) -> PosId {
        self.pos_from_neu(self.infer.constraints().types().neu(id).clone())
    }

    pub(super) fn neg_from_neu_id(&mut self, id: NeuId) -> NegId {
        self.neg_from_neu(self.infer.constraints().types().neu(id).clone())
    }
}
