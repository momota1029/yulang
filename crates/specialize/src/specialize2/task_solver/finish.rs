use super::*;

impl<'a> TaskSolver<'a> {
    pub(super) fn finish(mut self) -> Result<SolvedTask, SpecializeError> {
        self.graph.solve_role_demands()?;
        let solution = self.graph.solve_slots()?;
        let mut resolver = TypeResolver::new(&self.graph, &solution);
        let mut exprs = HashMap::new();
        // Monomorphization only needs concrete types at emitted boundaries and at
        // recursive demand edges. Slots that are not reachable from those uses may
        // stay undetermined; they are solver-local evidence, not mono output.
        for (expr, ty) in &self.exprs {
            let actual_slots = type_slot_refs(&ty.actual);
            let consumer_slots = ty.consumer.as_ref().map(type_slot_refs).unwrap_or_default();
            let Some(actual) = self.resolve_expr_actual(&mut resolver, *expr, ty)? else {
                continue;
            };
            let consumer = self.resolve_expr_consumer(&mut resolver, ty)?;
            exprs.insert(
                *expr,
                SolvedExprType {
                    actual,
                    consumer,
                    actual_slots,
                    consumer_slots,
                },
            );
        }
        let ref_signatures = self
            .ref_uses
            .iter()
            .map(|use_| {
                let ty = match self
                    .exprs
                    .get(&use_.expr)
                    .and_then(|ty| ty.consumer.as_ref())
                {
                    Some(consumer) => {
                        self.resolve_signature_type(&mut resolver, consumer, TypeSlotKind::Value)?
                    }
                    None => {
                        self.resolve_signature_type(&mut resolver, &use_.ty, TypeSlotKind::Value)?
                    }
                };
                Ok((use_.expr, ty))
            })
            .collect::<Result<HashMap<_, _>, SpecializeError>>()?;
        let select_signatures = self
            .select_uses
            .iter()
            .map(|use_| {
                let ty = match self
                    .exprs
                    .get(&use_.expr)
                    .and_then(|ty| ty.consumer.as_ref())
                {
                    Some(consumer) => self.resolve_signature_type_with_context(
                        &mut resolver,
                        &use_.ty,
                        consumer,
                        TypeSlotKind::Value,
                    )?,
                    None => {
                        self.resolve_signature_type(&mut resolver, &use_.ty, TypeSlotKind::Value)?
                    }
                };
                Ok((use_.expr, ty))
            })
            .collect::<Result<HashMap<_, _>, SpecializeError>>()?;
        let pat_ref_signatures = self
            .pat_ref_uses
            .iter()
            .map(|use_| {
                let ty =
                    self.resolve_signature_type(&mut resolver, &use_.ty, TypeSlotKind::Value)?;
                Ok((use_.pat, ty))
            })
            .collect::<Result<HashMap<_, _>, SpecializeError>>()?;
        let mut typeclass_resolutions = HashMap::new();
        for use_ in &self.typeclass_uses {
            let signature = match self
                .exprs
                .get(&use_.expr)
                .and_then(|ty| ty.consumer.as_ref())
            {
                Some(consumer) => self.resolve_signature_type_with_context(
                    &mut resolver,
                    &use_.method_ty,
                    consumer,
                    TypeSlotKind::Value,
                )?,
                None => self.resolve_signature_type(
                    &mut resolver,
                    &use_.method_ty,
                    TypeSlotKind::Value,
                )?,
            };
            let implementation = self.resolve_typeclass_use(use_.expr, use_.member, &signature)?;
            typeclass_resolutions.insert(
                use_.expr,
                TypeclassResolution {
                    implementation,
                    signature,
                },
            );
        }
        let runtime_evidence_graph = RuntimeEvidenceGraph::from_type_graph(&self.graph);
        Ok(SolvedTask {
            exprs,
            ref_signatures,
            select_signatures,
            typeclass_resolutions,
            pat_ref_signatures,
            raw_thunk_computations: self.raw_thunk_computations,
            runtime_evidence_graph,
        })
    }

    pub(super) fn resolve_expr_actual(
        &self,
        resolver: &mut TypeResolver<'_, '_>,
        expr: poly_expr::ExprId,
        ty: &ExprType,
    ) -> Result<Option<Type>, SpecializeError> {
        if self.expr_is_defined_ref(expr)
            && let Some(consumer) = &ty.consumer
        {
            return match resolver.resolve(consumer) {
                Ok(actual) => Ok(Some(close_resolved_runtime_surface(
                    actual,
                    TypeSlotKind::Value,
                ))),
                Err(SpecializeError::UndeterminedTypeSlot { .. }) => self
                    .resolve_partial_output_type(resolver, consumer, TypeSlotKind::Value)
                    .map(Some),
                Err(error) => Err(error),
            };
        }
        if self.required_exprs.contains(&expr) {
            return match resolver.resolve(&ty.actual) {
                Ok(actual) => Ok(Some(close_resolved_runtime_surface(
                    actual,
                    TypeSlotKind::Value,
                ))),
                Err(SpecializeError::UndeterminedTypeSlot { .. }) => self
                    .resolve_partial_output_type(resolver, &ty.actual, TypeSlotKind::Value)
                    .map(Some),
                Err(error) => Err(error),
            };
        }
        match match &ty.consumer {
            Some(consumer) => resolver.resolve_with_context(&ty.actual, consumer),
            None => resolver.resolve(&ty.actual),
        } {
            Ok(actual) => Ok(Some(close_resolved_runtime_surface(
                actual,
                TypeSlotKind::Value,
            ))),
            Err(SpecializeError::UndeterminedTypeSlot { .. }) if ty.consumer.is_some() => self
                .resolve_partial_output_type(resolver, &ty.actual, TypeSlotKind::Value)
                .map(Some),
            Err(SpecializeError::UndeterminedTypeSlot { .. })
                if self.discarded_exprs.contains(&expr) =>
            {
                self.resolve_partial_output_type(resolver, &ty.actual, TypeSlotKind::Value)
                    .map(Some)
            }
            Err(SpecializeError::UndeterminedTypeSlot { .. })
                if self.expr_can_omit_concrete_type(expr) =>
            {
                match &ty.consumer {
                    Some(consumer) => match resolver.resolve(consumer) {
                        Ok(consumer) => Ok(Some(close_resolved_runtime_surface(
                            consumer,
                            TypeSlotKind::Value,
                        ))),
                        Err(SpecializeError::UndeterminedTypeSlot { .. }) => Ok(None),
                        Err(error) => Err(error),
                    },
                    None => Ok(None),
                }
            }
            Err(SpecializeError::UndeterminedTypeSlot { .. }) => Ok(None),
            Err(error) => Err(error),
        }
    }

    pub(super) fn expr_is_defined_ref(&self, expr: poly_expr::ExprId) -> bool {
        let poly_expr::Expr::Var(ref_id) = self.arena.expr(expr) else {
            return false;
        };
        let Some(def) = self.arena.ref_target(*ref_id) else {
            return false;
        };
        matches!(
            self.arena.defs.get(def),
            Some(poly_expr::Def::Let { body: Some(_), .. })
        )
    }

    pub(super) fn resolve_expr_consumer(
        &self,
        resolver: &mut TypeResolver<'_, '_>,
        ty: &ExprType,
    ) -> Result<Option<Type>, SpecializeError> {
        let Some(consumer) = &ty.consumer else {
            return Ok(None);
        };
        match resolver.resolve(consumer) {
            Ok(consumer) => Ok(Some(close_resolved_runtime_surface(
                consumer,
                TypeSlotKind::Value,
            ))),
            Err(SpecializeError::UndeterminedTypeSlot { .. }) => self
                .resolve_partial_output_type(resolver, consumer, TypeSlotKind::Value)
                .map(Some),
            Err(error) => Err(error),
        }
    }

    pub(super) fn resolve_signature_type(
        &self,
        resolver: &mut TypeResolver<'_, '_>,
        ty: &Type,
        context: TypeSlotKind,
    ) -> Result<Type, SpecializeError> {
        match resolver.resolve(ty) {
            Ok(ty) => Ok(close_resolved_inference_surface(ty, context)),
            Err(SpecializeError::UndeterminedTypeSlot { .. }) => {
                self.resolve_partial_signature_type(resolver, ty, context)
            }
            Err(error) => Err(error),
        }
    }

    pub(super) fn resolve_signature_type_with_context(
        &self,
        resolver: &mut TypeResolver<'_, '_>,
        ty: &Type,
        consumer: &Type,
        context: TypeSlotKind,
    ) -> Result<Type, SpecializeError> {
        match resolver.resolve_with_context(ty, consumer) {
            Ok(ty) => Ok(close_resolved_inference_surface(ty, context)),
            Err(SpecializeError::UndeterminedTypeSlot { .. }) => {
                self.resolve_partial_signature_type(resolver, ty, context)
            }
            Err(error) => Err(error),
        }
    }

    pub(super) fn resolve_partial_output_type(
        &self,
        resolver: &mut TypeResolver<'_, '_>,
        ty: &Type,
        context: TypeSlotKind,
    ) -> Result<Type, SpecializeError> {
        let partial = resolver
            .resolve_partial_candidate(ty, true)?
            .unwrap_or_else(|| ty.clone());
        Ok(close_resolved_runtime_surface(partial, context))
    }

    pub(super) fn resolve_partial_signature_type(
        &self,
        resolver: &mut TypeResolver<'_, '_>,
        ty: &Type,
        context: TypeSlotKind,
    ) -> Result<Type, SpecializeError> {
        let partial = resolver
            .resolve_partial_candidate(ty, true)?
            .unwrap_or_else(|| ty.clone());
        Ok(close_resolved_inference_surface(partial, context))
    }

    pub(super) fn expr_can_omit_concrete_type(&self, expr: poly_expr::ExprId) -> bool {
        let poly_expr::Expr::Var(ref_id) = self.arena.expr(expr) else {
            return false;
        };
        let Some(def) = self.arena.ref_target(*ref_id) else {
            return false;
        };
        matches!(
            self.arena.defs.get(def),
            Some(poly_expr::Def::Arg) | Some(poly_expr::Def::Let { body: None, .. })
        )
    }

    pub(super) fn resolve_typeclass_use(
        &self,
        expr: poly_expr::ExprId,
        member: poly_expr::DefId,
        signature: &Type,
    ) -> Result<poly_expr::DefId, SpecializeError> {
        let Some(poly_expr::Def::Let {
            body,
            scheme: Some(scheme),
            ..
        }) = self.arena.defs.get(member)
        else {
            return Err(SpecializeError::MissingScheme {
                def: convert_def(member),
            });
        };
        let predicates = types::role_predicates_for_scheme_signature(
            self.arena,
            member,
            scheme,
            Some(signature),
        )?;
        let mut implementations = Vec::new();
        let mut matched_candidate_count = 0usize;
        for predicate in &predicates {
            let Some(input_types) = exact_role_input_types(predicate) else {
                continue;
            };
            for candidate in self.arena.role_impls.candidates(&predicate.role) {
                if roles::candidate_application(&self.arena.typ, predicate, candidate, &input_types)
                    .is_none()
                {
                    continue;
                }
                matched_candidate_count += 1;
                for method in &candidate.methods {
                    if method.requirement == member
                        && !implementations.contains(&method.implementation)
                    {
                        implementations.push(method.implementation);
                    }
                }
            }
        }
        match implementations.as_slice() {
            [implementation] => Ok(*implementation),
            [] if body.is_some() && matched_candidate_count > 0 => Ok(member),
            [] => Err(SpecializeError::UnresolvedTypeclassMethod {
                expr: expr.0,
                member: convert_def(member),
                receiver: signature.clone(),
            }),
            _ => Err(SpecializeError::AmbiguousTypeclassMethod {
                expr: expr.0,
                member: convert_def(member),
                receiver: signature.clone(),
                candidates: implementations.into_iter().map(convert_def).collect(),
            }),
        }
    }

    pub(super) fn instantiate_def_scheme(
        &mut self,
        def: poly_expr::DefId,
    ) -> Result<Type, SpecializeError> {
        let Some(poly_expr::Def::Let {
            scheme: Some(scheme),
            ..
        }) = self.arena.defs.get(def)
        else {
            return Err(SpecializeError::MissingScheme {
                def: convert_def(def),
            });
        };
        self.instantiate_scheme(def, scheme)
    }

    pub(super) fn instantiate_scheme(
        &mut self,
        def: poly_expr::DefId,
        scheme: &poly::types::Scheme,
    ) -> Result<Type, SpecializeError> {
        let instantiated = types::instantiate_principal_scheme_for_inference_with_fresh_and_roles(
            self.arena,
            def,
            scheme,
            |kind| match kind {
                types::SchemeQuantifierKind::Value => self.graph.fresh_value(),
                types::SchemeQuantifierKind::Effect => self.graph.fresh_effect(),
            },
        )?;
        self.graph.add_role_demands(instantiated.role_predicates);
        self.graph
            .constrain_recursive_bounds(instantiated.recursive_bounds)?;
        Ok(instantiated.ty)
    }

    #[track_caller]
    pub(super) fn join_effects(
        &mut self,
        effects: impl IntoIterator<Item = Type>,
    ) -> Result<Type, SpecializeError> {
        let effects = effects
            .into_iter()
            .filter(|effect| !effect.is_pure_effect())
            .collect::<Vec<_>>();
        match effects.as_slice() {
            [] => Ok(Type::pure_effect()),
            [single] => Ok(single.clone()),
            _ => {
                let effect = self.graph.fresh_effect();
                for item in effects {
                    self.graph.constrain_subtype(item, effect.clone())?;
                }
                Ok(effect)
            }
        }
    }

    pub(super) fn runtime_shape(&self, effect: Type, value: Type) -> Result<Type, SpecializeError> {
        Ok(types::runtime_shape(effect, value))
    }

    pub(super) fn primitive_type(&mut self, op: poly_expr::PrimitiveOp) -> Type {
        use poly_expr::PrimitiveOp;
        match op {
            PrimitiveOp::YadaYada => Type::Never,
            PrimitiveOp::BoolNot => unary_type(bool_type(), bool_type()),
            PrimitiveOp::BoolEq => binary_type(bool_type(), bool_type()),
            PrimitiveOp::ListEmpty => {
                let item = self.graph.fresh_value();
                unary_type(Type::unit(), list_type(item))
            }
            PrimitiveOp::ListSingleton => {
                let item = self.graph.fresh_value();
                unary_type(item.clone(), list_type(item))
            }
            PrimitiveOp::ListLen => {
                let item = self.graph.fresh_value();
                unary_type(list_type(item), int_type())
            }
            PrimitiveOp::ListMerge => {
                let item = self.graph.fresh_value();
                let list = list_type(item);
                function_type(vec![list.clone(), list.clone()], list)
            }
            PrimitiveOp::ListIndex => {
                let item = self.graph.fresh_value();
                function_type(vec![list_type(item.clone()), int_type()], item)
            }
            PrimitiveOp::ListIndexRange => {
                let item = self.graph.fresh_value();
                let list = list_type(item);
                function_type(vec![list.clone(), range_type()], list)
            }
            PrimitiveOp::ListSplice => {
                let item = self.graph.fresh_value();
                let list = list_type(item);
                function_type(vec![list.clone(), range_type(), list.clone()], list)
            }
            PrimitiveOp::ListIndexRangeRaw => {
                let item = self.graph.fresh_value();
                let list = list_type(item);
                function_type(vec![list.clone(), int_type(), int_type()], list)
            }
            PrimitiveOp::ListSpliceRaw => {
                let item = self.graph.fresh_value();
                let list = list_type(item);
                function_type(
                    vec![list.clone(), int_type(), int_type(), list.clone()],
                    list,
                )
            }
            PrimitiveOp::ListViewRaw => {
                let item = self.graph.fresh_value();
                unary_type(list_type(item.clone()), list_view_type(item))
            }
            PrimitiveOp::StringLen | PrimitiveOp::StringLineCount => {
                unary_type(str_type(), int_type())
            }
            PrimitiveOp::StringIndex => function_type(vec![str_type(), int_type()], char_type()),
            PrimitiveOp::StringIndexRange => {
                function_type(vec![str_type(), range_type()], str_type())
            }
            PrimitiveOp::StringSplice => {
                function_type(vec![str_type(), range_type(), str_type()], str_type())
            }
            PrimitiveOp::StringIndexRangeRaw => {
                function_type(vec![str_type(), int_type(), int_type()], str_type())
            }
            PrimitiveOp::StringSpliceRaw => function_type(
                vec![str_type(), int_type(), int_type(), str_type()],
                str_type(),
            ),
            PrimitiveOp::StringLineRange => {
                function_type(vec![str_type(), int_type()], range_type())
            }
            PrimitiveOp::IntAdd
            | PrimitiveOp::IntSub
            | PrimitiveOp::IntMul
            | PrimitiveOp::IntDiv
            | PrimitiveOp::IntMod => binary_type(int_type(), int_type()),
            PrimitiveOp::IntEq
            | PrimitiveOp::IntLt
            | PrimitiveOp::IntLe
            | PrimitiveOp::IntGt
            | PrimitiveOp::IntGe => binary_type(int_type(), bool_type()),
            PrimitiveOp::FloatAdd
            | PrimitiveOp::FloatSub
            | PrimitiveOp::FloatMul
            | PrimitiveOp::FloatDiv => binary_type(float_type(), float_type()),
            PrimitiveOp::FloatEq
            | PrimitiveOp::FloatLt
            | PrimitiveOp::FloatLe
            | PrimitiveOp::FloatGt
            | PrimitiveOp::FloatGe => binary_type(float_type(), bool_type()),
            PrimitiveOp::StringEq => binary_type(str_type(), bool_type()),
            PrimitiveOp::StringConcat => binary_type(str_type(), str_type()),
            PrimitiveOp::StringToBytes => unary_type(str_type(), bytes_type()),
            PrimitiveOp::CharEq => binary_type(char_type(), bool_type()),
            PrimitiveOp::CharToString => unary_type(char_type(), str_type()),
            PrimitiveOp::CharIsWhitespace
            | PrimitiveOp::CharIsPunctuation
            | PrimitiveOp::CharIsWord => unary_type(char_type(), bool_type()),
            PrimitiveOp::BytesLen => unary_type(bytes_type(), int_type()),
            PrimitiveOp::BytesEq => binary_type(bytes_type(), bool_type()),
            PrimitiveOp::BytesConcat => binary_type(bytes_type(), bytes_type()),
            PrimitiveOp::BytesIndex => function_type(vec![bytes_type(), int_type()], int_type()),
            PrimitiveOp::BytesIndexRange => {
                function_type(vec![bytes_type(), range_type()], bytes_type())
            }
            PrimitiveOp::BytesToUtf8Raw => {
                unary_type(bytes_type(), Type::Tuple(vec![str_type(), int_type()]))
            }
            PrimitiveOp::BytesToPath => unary_type(bytes_type(), path_type()),
            PrimitiveOp::PathToBytes => unary_type(path_type(), bytes_type()),
            PrimitiveOp::IntToString | PrimitiveOp::IntToHex | PrimitiveOp::IntToUpperHex => {
                unary_type(int_type(), str_type())
            }
            PrimitiveOp::IntToFloat => unary_type(int_type(), float_type()),
            PrimitiveOp::FloatToString => unary_type(float_type(), str_type()),
            PrimitiveOp::BoolToString => unary_type(bool_type(), str_type()),
        }
    }
}

fn type_slot_refs(ty: &Type) -> Vec<u32> {
    let mut slots = Vec::new();
    collect_type_slot_refs(ty, &mut slots);
    slots.sort_unstable();
    slots.dedup();
    slots
}

fn collect_type_slot_refs(ty: &Type, out: &mut Vec<u32>) {
    match ty {
        Type::OpenVar(slot) => out.push(*slot),
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            collect_type_slot_refs(arg, out);
            collect_type_slot_refs(arg_effect, out);
            collect_type_slot_refs(ret_effect, out);
            collect_type_slot_refs(ret, out);
        }
        Type::Thunk { effect, value } => {
            collect_type_slot_refs(effect, out);
            collect_type_slot_refs(value, out);
        }
        Type::Record(fields) => {
            for field in fields {
                collect_type_slot_refs(&field.value, out);
            }
        }
        Type::PolyVariant(variants) => {
            for variant in variants {
                for payload in &variant.payloads {
                    collect_type_slot_refs(payload, out);
                }
            }
        }
        Type::Tuple(items) | Type::EffectRow(items) => {
            for item in items {
                collect_type_slot_refs(item, out);
            }
        }
        Type::Stack { inner, .. } => collect_type_slot_refs(inner, out),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            collect_type_slot_refs(left, out);
            collect_type_slot_refs(right, out);
        }
        Type::Con { args, .. } => {
            for arg in args {
                collect_type_slot_refs(arg, out);
            }
        }
        Type::Any | Type::Never => {}
    }
}
