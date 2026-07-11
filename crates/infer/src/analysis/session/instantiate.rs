use super::*;

impl AnalysisSession {
    pub(super) fn constrain_open_use(&mut self, target_root: TypeVar, use_value: TypeVar) {
        let target_pos = self.infer.alloc_pos(Pos::Var(target_root));
        let use_neg = self.infer.alloc_neg(Neg::Var(use_value));
        self.infer.subtype(target_pos, use_neg);
    }

    pub(super) fn quantify_component(&mut self, component: &[DefId], roots: &[TypeVar]) {
        let trace = analysis_trace_mode();
        let component_start = Instant::now();
        let mut generalized = Vec::with_capacity(component.len());
        let mut component_metrics = GeneralizeComponentMetrics::default();
        for (def, root) in component.iter().copied().zip(roots.iter().copied()) {
            let phase = Instant::now();
            let (scheme, metrics) = self.generalize_root_with_prepasses_and_metrics(def, root);
            let elapsed = phase.elapsed();
            self.timing.record_generalize_root_summary(def, &metrics);
            component_metrics.add_root(metrics);
            self.timing.record_quantify_generalize(elapsed);
            trace_quantify_phase(trace, "generalize", def, elapsed, component_start);
            let phase = Instant::now();
            self.collect_role_impl_member_prerequisites(def, &scheme);
            let elapsed = phase.elapsed();
            self.timing.record_quantify_prerequisites(elapsed);
            trace_quantify_phase(
                trace,
                "collect role prerequisites",
                def,
                elapsed,
                component_start,
            );
            generalized.push((def, scheme));
        }
        self.timing.record_generalize_component_shape(
            component_metrics.root_compact_nodes,
            component_metrics.root_compact_vars,
            component_metrics.unique_compact_vars.len(),
            component_metrics.compact_iteration_nodes,
            component_metrics.compact_iteration_vars,
            component_metrics.roots_with_restarts,
            component_metrics.max_iterations_per_root,
            component_metrics.max_restarts_per_root,
        );

        for (def, scheme) in &generalized {
            self.schemes.insert(*def, scheme.clone());
        }

        for (def, scheme) in generalized {
            let phase = Instant::now();
            let ancestors = self.scheme_ancestors_for_current_poly(def);
            let ancestors = ancestors.iter().collect::<Vec<_>>();
            let finalized = finalize_generalized_compact_root_with_ancestors(
                &mut self.poly.typ,
                self.infer.constraints(),
                &scheme,
                &ancestors,
            );
            let elapsed = phase.elapsed();
            self.timing.record_quantify_finalize(elapsed);
            trace_quantify_phase(trace, "finalize", def, elapsed, component_start);
            self.trace_scheme(def, &finalized.scheme);
            self.set_def_scheme(def, finalized.scheme);
        }
        let elapsed = component_start.elapsed();
        if trace != AnalysisTraceMode::Off
            && (trace == AnalysisTraceMode::Verbose || elapsed >= Duration::from_millis(50))
        {
            eprintln!(
                "[analysis] quantify component done: defs={} elapsed={:.3}ms",
                component.len(),
                elapsed.as_secs_f64() * 1000.0
            );
        }
        self.timing.record_quantify(elapsed, component.len());
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

    pub(crate) fn imported_instantiation_witness(
        &mut self,
        target: DefId,
        candidate_role: &[String],
    ) -> Option<crate::CompiledImportInstantiationWitness> {
        let scheme = match self.poly.defs.get(target)? {
            Def::Let {
                scheme: Some(scheme),
                ..
            } => scheme.clone(),
            Def::Mod { .. } | Def::Let { .. } | Def::Arg => return None,
        };
        validate_imported_scheme_for_instantiation(
            &self.poly.typ,
            &scheme,
            &self.imported_boundary,
        )
        .ok()?;

        let first = instantiate_validated_imported_scheme_witness(
            &self.poly.typ,
            &mut self.infer,
            TypeLevel::root(),
            &scheme,
            &self.imported_boundary,
        );
        let second = instantiate_validated_imported_scheme_witness(
            &self.poly.typ,
            &mut self.infer,
            TypeLevel::root(),
            &scheme,
            &self.imported_boundary,
        );
        let first_scheme = first.as_scheme();
        let second_scheme = second.as_scheme();
        let boundary_binders = self
            .imported_boundary
            .bounds()
            .iter()
            .map(|bound| bound.var)
            .collect::<Vec<_>>();
        let boundary = crate::interface_oracle::BoundaryInterface {
            binders: &boundary_binders,
            bounds: self.imported_boundary.bounds(),
        };
        let first_inventory = crate::interface_oracle::scan_scheme_closure(
            self.infer.constraints().types(),
            &first_scheme,
            boundary,
        )
        .ok()?;
        let second_inventory = crate::interface_oracle::scan_scheme_closure(
            self.infer.constraints().types(),
            &second_scheme,
            boundary,
        )
        .ok()?;
        let first_view = crate::interface_oracle::SchemeAlphaView::from_scheme(
            self.infer.constraints().types(),
            &first_scheme,
            boundary,
        )
        .ok()?;
        let second_view = crate::interface_oracle::SchemeAlphaView::from_scheme(
            self.infer.constraints().types(),
            &second_scheme,
            boundary,
        )
        .ok()?;

        let source_candidate = self.poly.role_impls.candidates(candidate_role).first()?;
        let imported_candidate = self.role_impls.candidates(candidate_role).first()?;
        let mut source_candidate_head = source_candidate
            .as_constraint()
            .raw_vars(&self.poly.typ)
            .into_iter()
            .collect::<Vec<_>>();
        source_candidate_head.sort_by_key(|var| var.0);
        let mut imported_candidate_head = imported_candidate
            .as_constraint()
            .raw_vars(self.infer.constraints().types())
            .into_iter()
            .collect::<Vec<_>>();
        imported_candidate_head.sort_by_key(|var| var.0);
        let boundary_set = boundary_binders.iter().copied().collect::<FxHashSet<_>>();
        let mut imported_candidate_boundary = imported_candidate
            .prerequisites
            .iter()
            .flat_map(|prerequisite| {
                prerequisite
                    .raw_vars(self.infer.constraints().types())
                    .into_iter()
            })
            .filter(|var| boundary_set.contains(var))
            .collect::<Vec<_>>();
        imported_candidate_boundary.sort_by_key(|var| var.0);
        imported_candidate_boundary.dedup();

        Some(crate::CompiledImportInstantiationWitness {
            first_view,
            second_view,
            first_quantified: first_inventory.quantified,
            second_quantified: second_inventory.quantified,
            first_recursive: first_inventory.recursive,
            second_recursive: second_inventory.recursive,
            first_boundary: first_inventory.boundary,
            second_boundary: second_inventory.boundary,
            source_candidate_head,
            imported_candidate_head,
            imported_candidate_boundary,
        })
    }

    #[cfg(test)]
    pub(in crate::analysis) fn instantiate_use(
        &mut self,
        parent: DefId,
        target: DefId,
        use_value: TypeVar,
    ) {
        self.instantiate_use_batch(&[SccInstantiateUse {
            parent,
            target,
            use_value,
        }]);
    }

    pub(in crate::analysis) fn instantiate_use_batch(&mut self, uses: &[SccInstantiateUse]) {
        let batch_start = Instant::now();
        let mut instantiated_count = 0usize;
        let mut direct_lower_predicates = Vec::new();
        let mut subtype_predicates = Vec::new();
        for use_site in uses {
            if self.prepare_instantiated_use(
                *use_site,
                &mut direct_lower_predicates,
                &mut subtype_predicates,
            ) {
                instantiated_count += 1;
            }
        }
        let phase = Instant::now();
        if !direct_lower_predicates.is_empty() {
            self.infer
                .constrain_pos_to_var_direct_many(direct_lower_predicates);
        }
        if !subtype_predicates.is_empty() {
            self.infer.subtypes(subtype_predicates);
        }
        self.timing
            .record_instantiate_subtype_predicate(phase.elapsed());
        self.timing
            .record_instantiate_batch(batch_start.elapsed(), instantiated_count);
    }

    fn prepare_instantiated_use(
        &mut self,
        use_site: SccInstantiateUse,
        direct_lower_predicates: &mut Vec<(PosId, TypeVar)>,
        subtype_predicates: &mut Vec<(PosId, NegId)>,
    ) -> bool {
        let SccInstantiateUse {
            parent,
            target,
            use_value,
        } = use_site;
        let Some(Def::Let {
            scheme: Some(scheme),
            ..
        }) = self.poly.defs.get(target)
        else {
            return false;
        };
        self.trace_scheme(target, scheme);
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
        let instantiated = if self.imported_scheme_defs.contains(&target) {
            let validation = if let Some(validation) = self.imported_scheme_validations.get(&target)
            {
                validation.clone()
            } else {
                let validation = validate_imported_scheme_for_instantiation(
                    &self.poly.typ,
                    scheme,
                    &self.imported_boundary,
                );
                self.imported_scheme_validations
                    .insert(target, validation.clone());
                validation
            };
            if let Err(error) = validation {
                self.imported_scheme_instantiation_failures.push(
                    ImportedSchemeInstantiationFailure {
                        parent,
                        target,
                        error,
                    },
                );
                return false;
            }
            instantiate_validated_imported_scheme_with_roles(
                &self.poly.typ,
                &mut self.infer,
                TypeLevel::secondary(),
                scheme,
                &self.imported_boundary,
            )
        } else {
            instantiate_scheme_with_roles(
                &self.poly.typ,
                &mut self.infer,
                TypeLevel::secondary(),
                scheme,
            )
        };
        let elapsed = phase.elapsed();
        self.timing.record_instantiate_clone_scheme(elapsed);
        trace_instantiate_phase(trace, "clone scheme", parent, target, elapsed, start);
        let predicate_shape = match self.infer.constraints().types().pos(instantiated.predicate) {
            Pos::Var(_) => InstantiatePredicateShape::Var,
            Pos::Stack { .. } => InstantiatePredicateShape::Stack,
            Pos::NonSubtract(_, _) => InstantiatePredicateShape::NonSubtract,
            Pos::Fun { .. } => InstantiatePredicateShape::Fun,
            Pos::Con(_, _) => InstantiatePredicateShape::Con,
            Pos::Bot
            | Pos::Record(_)
            | Pos::RecordTailSpread { .. }
            | Pos::RecordHeadSpread { .. }
            | Pos::PolyVariant(_)
            | Pos::Tuple(_)
            | Pos::Row(_)
            | Pos::Union(_, _) => InstantiatePredicateShape::Other,
        };
        self.timing
            .record_instantiate_predicate_shape(predicate_shape);
        if instantiate_predicate_can_add_lower_directly(
            self.infer.constraints().types().pos(instantiated.predicate),
        ) {
            self.timing.record_instantiate_direct_lower_predicate();
            direct_lower_predicates.push((instantiated.predicate, use_value));
        } else {
            let use_upper = self.infer.alloc_neg(Neg::Var(use_value));
            subtype_predicates.push((instantiated.predicate, use_upper));
        }
        let phase = Instant::now();
        self.insert_instantiated_role_predicates(parent, &instantiated.role_predicates);
        let elapsed = phase.elapsed();
        self.timing.record_instantiate_insert_roles(elapsed);
        trace_instantiate_phase(trace, "insert roles", parent, target, elapsed, start);
        trace_instantiate_phase(
            trace,
            "prepare instantiation",
            parent,
            target,
            start.elapsed(),
            start,
        );
        true
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

fn instantiate_predicate_can_add_lower_directly(pos: &Pos) -> bool {
    matches!(
        pos,
        Pos::Con(_, _)
            | Pos::Fun { .. }
            | Pos::Record(_)
            | Pos::RecordTailSpread { .. }
            | Pos::RecordHeadSpread { .. }
            | Pos::PolyVariant(_)
            | Pos::Tuple(_)
            | Pos::Row(_)
    )
}

fn trace_quantify_phase(
    trace: AnalysisTraceMode,
    phase: &str,
    def: DefId,
    elapsed: Duration,
    start: Instant,
) {
    if trace == AnalysisTraceMode::Off {
        return;
    }
    if trace == AnalysisTraceMode::Verbose || elapsed >= Duration::from_millis(50) {
        eprintln!(
            "[analysis] quantify {phase}: def={def:?} elapsed={:.3}ms total={:.3}ms",
            elapsed.as_secs_f64() * 1000.0,
            start.elapsed().as_secs_f64() * 1000.0
        );
    }
}
