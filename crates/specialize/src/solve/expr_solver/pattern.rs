use super::*;

impl<'a> ExprTypeSolver<'a> {
    pub(super) fn record_type(
        &mut self,
        fields: &[(String, poly_expr::ExprId)],
        spread: &poly_expr::RecordSpread<poly_expr::ExprId>,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        let expected_fields = match &expected {
            Some(Type::Record(fields)) => Some(fields.as_slice()),
            _ => None,
        };
        let mut typed_fields = Vec::with_capacity(fields.len());
        for (name, value) in fields {
            let field_expected = expected_fields
                .and_then(|fields| record_field_type(fields, name))
                .map(|field| field.value.clone());
            typed_fields.push(TypeField {
                name: name.clone(),
                value: self.expr(*value, field_expected)?,
                optional: false,
            });
        }

        match spread {
            poly_expr::RecordSpread::None => Ok(Type::Record(typed_fields)),
            poly_expr::RecordSpread::Head(expr) => {
                let spread = self.expr(*expr, None)?;
                Ok(match spread {
                    Type::Record(spread_fields) => {
                        Type::Record(join_record_fields(spread_fields, typed_fields))
                    }
                    _ => expected.unwrap_or_else(|| self.fresh_value_slot()),
                })
            }
            poly_expr::RecordSpread::Tail(expr) => {
                let spread = self.expr(*expr, None)?;
                Ok(match spread {
                    Type::Record(spread_fields) => {
                        Type::Record(join_record_fields(typed_fields, spread_fields))
                    }
                    _ => expected.unwrap_or_else(|| self.fresh_value_slot()),
                })
            }
        }
    }

    pub(super) fn poly_variant_type(
        &mut self,
        tag: &str,
        payloads: &[poly_expr::ExprId],
        expected: Option<&Type>,
    ) -> Result<Type, SpecializeError> {
        let expected_variant = match expected {
            Some(Type::PolyVariant(variants)) => variants
                .iter()
                .find(|variant| variant.name == tag && variant.payloads.len() == payloads.len()),
            _ => None,
        };
        let mut typed_payloads = Vec::with_capacity(payloads.len());
        for (index, payload) in payloads.iter().enumerate() {
            let payload_expected =
                expected_variant.and_then(|variant| variant.payloads.get(index).cloned());
            typed_payloads.push(self.expr(*payload, payload_expected)?);
        }
        Ok(Type::PolyVariant(vec![TypeVariant {
            name: tag.to_string(),
            payloads: typed_payloads,
        }]))
    }

    pub(super) fn select_type(
        &mut self,
        base: poly_expr::ExprId,
        select: poly_expr::SelectId,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        let select = self.arena.select(select);
        match select.resolution {
            Some(poly_expr::SelectResolution::RecordField) => {
                self.record_select_type(base, &select.name, expected)
            }
            Some(poly_expr::SelectResolution::Method { def }) => {
                self.method_select_type(base, def, expected, MethodDemandMode::Emit)
            }
            Some(poly_expr::SelectResolution::TypeclassMethod { member }) => self
                .method_select_type(
                    base,
                    member,
                    expected,
                    MethodDemandMode::DeferWithoutExpected,
                ),
            None => {
                self.expr(base, None)?;
                Ok(expected.unwrap_or_else(|| self.fresh_value_slot()))
            }
        }
    }

    pub(super) fn record_select_type(
        &mut self,
        base: poly_expr::ExprId,
        name: &str,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        let base_ty = self.expr(base, None)?;
        if let Type::Record(fields) = &base_ty
            && let Some(field) = record_field_type(fields, name)
        {
            return Ok(field.value.clone());
        }

        let field_ty = expected.unwrap_or_else(|| self.fresh_value_slot());
        self.expr(
            base,
            Some(Type::Record(vec![TypeField {
                name: name.to_string(),
                value: field_ty.clone(),
                optional: false,
            }])),
        )?;
        Ok(field_ty)
    }

    pub(super) fn method_select_type(
        &mut self,
        base: poly_expr::ExprId,
        def: poly_expr::DefId,
        expected: Option<Type>,
        demand_mode: MethodDemandMode,
    ) -> Result<Type, SpecializeError> {
        let Some(poly_expr::Def::Let {
            scheme: Some(scheme),
            ..
        }) = self.arena.defs.get(def)
        else {
            self.expr(base, None)?;
            return Ok(self.fresh_value_slot());
        };
        let method_ty = match expected.as_ref() {
            Some(expected) => {
                let expected = self.selected_method_scheme_expected(expected.clone());
                self.instantiate_scheme_with_expected(def, scheme, &expected)?
            }
            None if demand_mode == MethodDemandMode::DeferWithoutExpected => {
                self.instantiate_scheme_type_only(def, scheme)?
            }
            None => self.instantiate_scheme(def, scheme)?,
        };
        let Some((receiver_ty, result_ty)) = function_runtime_parts(&method_ty) else {
            self.expr(base, None)?;
            return Ok(self.fresh_value_slot());
        };
        self.expr(base, Some(receiver_ty))?;
        Ok(result_ty)
    }

    pub(super) fn selected_method_scheme_expected(&mut self, selected: Type) -> Type {
        types::pure_function_type(self.fresh_value_slot(), selected)
    }

    pub(super) fn bind_pat(
        &mut self,
        pat: poly_expr::PatId,
        ty: Type,
    ) -> Result<(), SpecializeError> {
        use poly_expr::Pat as PolyPat;
        match self.arena.pat(pat) {
            PolyPat::Wild => {}
            PolyPat::Lit(lit) => {
                let lit_ty = lit_type(lit);
                self.graph.constrain_subtype(lit_ty.clone(), ty.clone())?;
                self.graph.constrain_subtype(ty, lit_ty)?;
            }
            PolyPat::Var(def) => {
                if def.0 == 711 {
                    eprintln!("bind target def={def:?} ty={ty:?}");
                }
                self.local_types.insert(*def, ty);
            }
            PolyPat::As(inner, def) => {
                if def.0 == 711 {
                    eprintln!("bind target as def={def:?} ty={ty:?}");
                }
                self.local_types.insert(*def, ty.clone());
                self.bind_pat(*inner, ty)?;
            }
            PolyPat::Tuple(items) => {
                if let Type::Tuple(item_types) = ty {
                    for (item, item_ty) in items.iter().zip(item_types) {
                        self.bind_pat(*item, item_ty)?;
                    }
                }
            }
            PolyPat::List {
                prefix,
                spread,
                suffix,
            } => {
                self.bind_list_pat(prefix, *spread, suffix, ty)?;
            }
            PolyPat::Record { fields, spread } => {
                self.bind_record_pat(fields, spread, ty)?;
            }
            PolyPat::Con(ref_id, payloads) => {
                self.bind_constructor_pat(*ref_id, payloads, ty)?;
            }
            PolyPat::PolyVariant(tag, payloads) => {
                if let Type::PolyVariant(variants) = ty {
                    match variants.iter().find(|variant| variant.name == *tag) {
                        Some(variant) => {
                            for (payload, payload_ty) in payloads.iter().zip(&variant.payloads) {
                                self.bind_pat(*payload, payload_ty.clone())?;
                            }
                        }
                        None => {
                            for payload in payloads {
                                self.bind_pat(*payload, Type::Never)?;
                            }
                        }
                    }
                }
            }
            PolyPat::Or(left, right) => {
                self.bind_pat(*left, ty.clone())?;
                self.bind_pat(*right, ty)?;
            }
            PolyPat::Ref(ref_id) => {
                self.bind_ref_pat(*ref_id, ty)?;
            }
        }
        Ok(())
    }

    pub(super) fn bind_list_pat(
        &mut self,
        prefix: &[poly_expr::PatId],
        spread: Option<poly_expr::PatId>,
        suffix: &[poly_expr::PatId],
        ty: Type,
    ) -> Result<(), SpecializeError> {
        let item_ty = list_item_type(&ty).unwrap_or_else(|| self.fresh_value_slot());
        for item in prefix.iter().chain(suffix) {
            self.bind_pat(*item, item_ty.clone())?;
        }
        if let Some(spread) = spread {
            self.bind_pat(spread, ty)?;
        }
        Ok(())
    }

    pub(super) fn bind_record_pat(
        &mut self,
        fields: &[poly_expr::RecordPatField],
        spread: &poly_expr::RecordSpread<poly_expr::DefId>,
        ty: Type,
    ) -> Result<(), SpecializeError> {
        let Type::Record(record_fields) = ty else {
            for field in fields {
                let field_ty = self.record_pattern_default_type(field, None)?;
                self.bind_pat(field.pat, field_ty)?;
            }
            if let Some(def) = record_spread_def(spread) {
                let spread_ty = self.fresh_value_slot();
                self.local_types.insert(def, spread_ty);
            }
            return Ok(());
        };

        for field in fields {
            let expected =
                record_field_type(&record_fields, &field.name).map(|field| field.value.clone());
            let field_ty = self.record_pattern_default_type(field, expected)?;
            self.bind_pat(field.pat, field_ty)?;
        }
        if let Some(def) = record_spread_def(spread) {
            let captured = record_fields
                .into_iter()
                .filter(|field| !fields.iter().any(|pattern| pattern.name == field.name))
                .collect::<Vec<_>>();
            self.local_types.insert(def, Type::Record(captured));
        }
        Ok(())
    }

    pub(super) fn record_pattern_default_type(
        &mut self,
        field: &poly_expr::RecordPatField,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        let Some(default) = field.default else {
            return Ok(expected.unwrap_or_else(|| self.fresh_value_slot()));
        };
        let expected = expected.unwrap_or_else(|| self.fresh_value_slot());
        let actual = self.expr(default, Some(expected.clone()))?;
        self.graph.constrain_subtype(actual.clone(), expected)?;
        Ok(actual)
    }

    pub(super) fn constrain_pat_defaults(
        &mut self,
        pat: poly_expr::PatId,
        ty: Type,
    ) -> Result<(), SpecializeError> {
        use poly_expr::Pat as PolyPat;
        match self.arena.pat(pat) {
            PolyPat::Wild | PolyPat::Lit(_) | PolyPat::Ref(_) => {}
            PolyPat::Var(def) => {
                if def.0 == 711 {
                    eprintln!("default-bind target def={def:?} ty={ty:?}");
                }
                self.local_types.insert(*def, ty);
            }
            PolyPat::As(inner, def) => {
                if def.0 == 711 {
                    eprintln!("default-bind target as def={def:?} ty={ty:?}");
                }
                self.local_types.insert(*def, ty.clone());
                self.constrain_pat_defaults(*inner, ty)?;
            }
            PolyPat::Tuple(items) => {
                if let Type::Tuple(item_types) = ty {
                    for (item, item_ty) in items.iter().zip(item_types) {
                        self.constrain_pat_defaults(*item, item_ty)?;
                    }
                }
            }
            PolyPat::List {
                prefix,
                spread,
                suffix,
            } => {
                let item_ty = list_item_type(&ty).unwrap_or_else(|| self.fresh_value_slot());
                for item in prefix.iter().chain(suffix) {
                    self.constrain_pat_defaults(*item, item_ty.clone())?;
                }
                if let Some(spread) = spread {
                    self.constrain_pat_defaults(*spread, ty)?;
                }
            }
            PolyPat::Record { fields, spread } => {
                self.constrain_record_pat_defaults(fields, spread, ty)?;
            }
            PolyPat::PolyVariant(tag, payloads) => {
                if let Type::PolyVariant(variants) = ty
                    && let Some(variant) = variants.iter().find(|variant| {
                        variant.name == *tag && variant.payloads.len() == payloads.len()
                    })
                {
                    for (payload, payload_ty) in payloads.iter().zip(&variant.payloads) {
                        self.constrain_pat_defaults(*payload, payload_ty.clone())?;
                    }
                }
            }
            PolyPat::Con(_, payloads) => {
                for payload in payloads {
                    let payload_ty = self.fresh_value_slot();
                    self.constrain_pat_defaults(*payload, payload_ty)?;
                }
            }
            PolyPat::Or(left, right) => {
                self.constrain_pat_defaults(*left, ty.clone())?;
                self.constrain_pat_defaults(*right, ty)?;
            }
        }
        Ok(())
    }

    pub(super) fn constrain_record_pat_defaults(
        &mut self,
        fields: &[poly_expr::RecordPatField],
        spread: &poly_expr::RecordSpread<poly_expr::DefId>,
        ty: Type,
    ) -> Result<(), SpecializeError> {
        let Type::Record(record_fields) = ty else {
            for field in fields {
                let field_ty = self.fresh_value_slot();
                self.constrain_default_expr(field.default, field_ty.clone())?;
                self.constrain_pat_defaults(field.pat, field_ty)?;
            }
            if let Some(def) = record_spread_def(spread) {
                let spread_ty = self.fresh_value_slot();
                self.local_types.insert(def, spread_ty);
            }
            return Ok(());
        };

        for field in fields {
            let field_ty = record_field_type(&record_fields, &field.name)
                .map(|field| field.value.clone())
                .unwrap_or_else(|| self.fresh_value_slot());
            self.constrain_default_expr(field.default, field_ty.clone())?;
            self.constrain_pat_defaults(field.pat, field_ty)?;
        }
        if let Some(def) = record_spread_def(spread) {
            let captured = record_fields
                .into_iter()
                .filter(|field| !fields.iter().any(|pattern| pattern.name == field.name))
                .collect::<Vec<_>>();
            self.local_types.insert(def, Type::Record(captured));
        }
        Ok(())
    }

    pub(super) fn constrain_default_expr(
        &mut self,
        default: Option<poly_expr::ExprId>,
        expected: Type,
    ) -> Result<(), SpecializeError> {
        let Some(default) = default else {
            return Ok(());
        };
        let actual = self.infer_expr(default, Some(expected.clone()))?;
        self.constrain_expr_boundary(actual, expected)
    }

    pub(super) fn bind_constructor_pat(
        &mut self,
        ref_id: poly_expr::RefId,
        payloads: &[poly_expr::PatId],
        scrutinee_ty: Type,
    ) -> Result<(), SpecializeError> {
        let Some(def) = self.arena.ref_target(ref_id) else {
            return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
        };
        let Some(poly_expr::Def::Let {
            scheme: Some(scheme),
            ..
        }) = self.arena.defs.get(def)
        else {
            return Ok(());
        };
        let constructor_ty = self.instantiate_scheme(def, scheme)?;
        let Some((payload_tys, owner_ty)) = split_function_spine(constructor_ty, payloads.len())
        else {
            return Ok(());
        };
        self.graph
            .constrain_subtype(owner_ty.clone(), scrutinee_ty.clone())?;
        self.graph.constrain_subtype(scrutinee_ty, owner_ty)?;
        for (payload, payload_ty) in payloads.iter().zip(payload_tys) {
            self.bind_pat(*payload, payload_ty)?;
        }
        Ok(())
    }

    pub(super) fn bind_ref_pat(
        &mut self,
        ref_id: poly_expr::RefId,
        scrutinee_ty: Type,
    ) -> Result<(), SpecializeError> {
        let Some(def) = self.arena.ref_target(ref_id) else {
            return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
        };
        if let Some(ref_ty) = self.local_types.get(&def).cloned() {
            self.graph
                .constrain_subtype(ref_ty.clone(), scrutinee_ty.clone())?;
            self.graph.constrain_subtype(scrutinee_ty, ref_ty)?;
            return Ok(());
        }
        match self.arena.defs.get(def) {
            Some(poly_expr::Def::Let {
                scheme: Some(scheme),
                ..
            }) => {
                let ref_ty = self.instantiate_scheme(def, scheme)?;
                self.graph
                    .constrain_subtype(ref_ty.clone(), scrutinee_ty.clone())?;
                self.graph.constrain_subtype(scrutinee_ty, ref_ty)
            }
            Some(poly_expr::Def::Arg) | Some(poly_expr::Def::Let { body: None, .. }) => Ok(()),
            _ => Ok(()),
        }
    }
}
