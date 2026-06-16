use super::*;

impl<'a> ExprTypeSolver<'a> {
    pub(super) fn var_type(
        &mut self,
        ref_id: poly_expr::RefId,
        expected: Option<&Type>,
    ) -> Result<Type, SpecializeError> {
        let Some(def) = self.arena.ref_target(ref_id) else {
            return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
        };
        if let Some(local_ty) = self.local_types.get(&def).cloned() {
            if def.0 == 711 {
                eprintln!("var target local def={def:?} ty={local_ty:?}");
            }
            return Ok(local_ty);
        }
        if let Some(active_ty) = self.constraining_def_types.get(&def).cloned() {
            if def.0 == 711 {
                eprintln!("var target active def={def:?} ty={active_ty:?}");
            }
            return Ok(active_ty);
        }
        match self.arena.defs.get(def) {
            Some(poly_expr::Def::Let {
                scheme: Some(scheme),
                body,
                ..
            }) => {
                let ty = match expected {
                    Some(expected) => {
                        self.instantiate_scheme_with_expected(def, scheme, expected)?
                    }
                    None => self.instantiate_scheme(def, scheme)?,
                };
                if let Some(body) = body {
                    self.constrain_instantiated_def_body(def, *body, ty.clone())?;
                }
                Ok(ty)
            }
            Some(poly_expr::Def::Arg) | Some(poly_expr::Def::Let { body: None, .. }) => {
                Ok(self.fresh_value_slot())
            }
            Some(poly_expr::Def::Let { scheme: None, .. }) => Err(SpecializeError::MissingScheme {
                def: convert_def(def),
            }),
            Some(other) => Err(SpecializeError::UnsupportedDefKind {
                def: convert_def(def),
                kind: def_kind(other),
            }),
            None => Err(SpecializeError::MissingDef {
                def: convert_def(def),
            }),
        }
    }

    pub(super) fn constrain_instantiated_def_body(
        &mut self,
        def: poly_expr::DefId,
        body: poly_expr::ExprId,
        ty: Type,
    ) -> Result<(), SpecializeError> {
        if self.constraining_def_types.contains_key(&def) {
            return Ok(());
        }

        let local_types = self.local_types.clone();
        let plan = std::mem::take(&mut self.plan);
        self.constraining_def_types.insert(def, ty.clone());
        let result = self.expr(body, Some(ty)).map(|_| ());
        self.constraining_def_types.remove(&def);
        self.local_types = local_types;
        self.plan = plan;
        result
    }

    pub(super) fn instantiate_scheme(
        &mut self,
        def: poly_expr::DefId,
        scheme: &poly::types::Scheme,
    ) -> Result<Type, SpecializeError> {
        let mut slots = Vec::new();
        let instantiated =
            types::instantiate_scheme_with_fresh_and_roles(self.arena, def, scheme, |kind| {
                let slot = match kind {
                    types::SchemeQuantifierKind::Value => self.fresh_value_slot(),
                    types::SchemeQuantifierKind::Effect => self.fresh_effect_slot(),
                };
                slots.push(slot.clone());
                slot
            })?;
        for slot in slots {
            if let Type::OpenVar(slot) = slot {
                self.graph.ensure_slot(slot)?;
            }
        }
        self.graph.add_role_demands(instantiated.role_predicates);
        self.graph
            .constrain_recursive_bounds(instantiated.recursive_bounds)?;
        Ok(instantiated.ty)
    }

    pub(super) fn instantiate_monomorphic_scheme(
        &mut self,
        def: poly_expr::DefId,
        scheme: &poly::types::Scheme,
    ) -> Result<Type, SpecializeError> {
        let instantiated = types::instantiate_monomorphic_scheme_with_fresh_and_roles(
            self.arena,
            def,
            scheme,
            |kind| match kind {
                types::SchemeQuantifierKind::Value => self.fresh_value_slot(),
                types::SchemeQuantifierKind::Effect => self.fresh_effect_slot(),
            },
        )?;
        self.graph.add_role_demands(instantiated.role_predicates);
        self.graph
            .constrain_recursive_bounds(instantiated.recursive_bounds)?;
        Ok(instantiated.ty)
    }

    pub(super) fn instantiate_scheme_with_expected(
        &mut self,
        def: poly_expr::DefId,
        scheme: &poly::types::Scheme,
        expected: &Type,
    ) -> Result<Type, SpecializeError> {
        let instantiated = types::instantiate_scheme_with_expected_fresh_and_roles(
            self.arena,
            def,
            scheme,
            expected,
            |kind| match kind {
                types::SchemeQuantifierKind::Value => self.fresh_value_slot(),
                types::SchemeQuantifierKind::Effect => self.fresh_effect_slot(),
            },
        )?;
        self.graph.add_role_demands(instantiated.role_predicates);
        self.graph
            .constrain_recursive_bounds(instantiated.recursive_bounds)?;
        Ok(instantiated.ty)
    }

    pub(super) fn instantiate_scheme_type_only(
        &mut self,
        def: poly_expr::DefId,
        scheme: &poly::types::Scheme,
    ) -> Result<Type, SpecializeError> {
        let instantiated =
            types::instantiate_scheme_with_fresh_and_roles(self.arena, def, scheme, |kind| {
                match kind {
                    types::SchemeQuantifierKind::Value => self.fresh_value_slot(),
                    types::SchemeQuantifierKind::Effect => self.fresh_effect_slot(),
                }
            })?;
        self.graph
            .constrain_recursive_bounds(instantiated.recursive_bounds)?;
        Ok(instantiated.ty)
    }

    pub(super) fn fresh_value_slot(&mut self) -> Type {
        self.graph.fresh_slot(TypeSlotKind::Value)
    }

    pub(super) fn fresh_effect_slot(&mut self) -> Type {
        self.graph.fresh_slot(TypeSlotKind::Effect)
    }

    pub(super) fn primitive_type(
        &mut self,
        op: poly_expr::PrimitiveOp,
        expected: Option<&Type>,
    ) -> Type {
        if let Some(expected) = expected {
            return self.primitive_type_from_expected(op, expected);
        }

        use poly_expr::PrimitiveOp;
        match op {
            PrimitiveOp::YadaYada => Type::Never,
            PrimitiveOp::BoolNot => unary_type(bool_type(), bool_type()),
            PrimitiveOp::BoolEq => binary_type(bool_type(), bool_type()),
            PrimitiveOp::ListEmpty => {
                let item = self.fresh_value_slot();
                unary_type(Type::unit(), list_type(item))
            }
            PrimitiveOp::ListSingleton => {
                let item = self.fresh_value_slot();
                unary_type(item.clone(), list_type(item))
            }
            PrimitiveOp::ListLen => {
                let item = self.fresh_value_slot();
                unary_type(list_type(item), int_type())
            }
            PrimitiveOp::ListMerge => {
                let item = self.fresh_value_slot();
                let list = list_type(item);
                function_type(vec![list.clone(), list.clone()], list)
            }
            PrimitiveOp::ListIndex => {
                let item = self.fresh_value_slot();
                function_type(vec![list_type(item.clone()), int_type()], item)
            }
            PrimitiveOp::ListIndexRange => {
                let item = self.fresh_value_slot();
                let list = list_type(item);
                function_type(vec![list.clone(), range_type()], list)
            }
            PrimitiveOp::ListSplice => {
                let item = self.fresh_value_slot();
                let list = list_type(item);
                function_type(vec![list.clone(), range_type(), list.clone()], list)
            }
            PrimitiveOp::ListIndexRangeRaw => {
                let item = self.fresh_value_slot();
                let list = list_type(item);
                function_type(vec![list.clone(), int_type(), int_type()], list)
            }
            PrimitiveOp::ListSpliceRaw => {
                let item = self.fresh_value_slot();
                let list = list_type(item);
                function_type(
                    vec![list.clone(), int_type(), int_type(), list.clone()],
                    list,
                )
            }
            PrimitiveOp::ListViewRaw => {
                let item = self.fresh_value_slot();
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

    pub(super) fn primitive_type_from_expected(
        &mut self,
        op: poly_expr::PrimitiveOp,
        expected: &Type,
    ) -> Type {
        let _ = op;
        expected.clone()
    }
}
