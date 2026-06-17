use super::*;

impl<'a> Runtime<'a> {
    pub(super) fn bind_pat(&mut self, pat: Pat, value: Value, env: CapturedEnv) -> BindResult<'a> {
        if pattern_observes_value(&pat) && value_is_thunk_like(&value) {
            let forced = self.force_thunk(value)?;
            return self.continue_value_as_bind(
                forced,
                env,
                Rc::new(move |runtime, value, env| runtime.bind_pat(pat.clone(), value, env)),
            );
        }

        let (view, markers) = value_view(&value);
        match pat {
            Pat::Wild => bind_done(true, env),
            Pat::Lit(lit) => bind_done(value_equivalent(&value, &Value::from(&lit)), env),
            Pat::Tuple(pats) => {
                let Value::Tuple(values) = view else {
                    return bind_done(false, env);
                };
                if pats.len() != values.len() {
                    return bind_done(false, env);
                }
                let entries = pats
                    .into_iter()
                    .zip(values)
                    .map(|(pat, value)| (pat, mark_value(value.clone(), &markers)))
                    .collect();
                self.bind_pat_sequence(entries, env)
            }
            Pat::List {
                prefix,
                spread,
                suffix,
            } => {
                let Value::List(items) = view else {
                    return bind_done(false, env);
                };
                self.bind_list_pat(
                    prefix,
                    spread.map(|pat| *pat),
                    suffix,
                    items.clone(),
                    markers,
                    env,
                )
            }
            Pat::Record { fields, spread } => {
                let Value::Record(record_fields) = view else {
                    return bind_done(false, env);
                };
                self.bind_record_pat(
                    fields,
                    spread,
                    record_fields.clone(),
                    markers,
                    HashSet::new(),
                    env,
                )
            }
            Pat::PolyVariant(tag, payload_pats) => {
                let Value::PolyVariant {
                    tag: value_tag,
                    payloads,
                } = view
                else {
                    return bind_done(false, env);
                };
                if tag != *value_tag || payload_pats.len() != payloads.len() {
                    return bind_done(false, env);
                }
                let entries = payload_pats
                    .into_iter()
                    .zip(payloads)
                    .map(|(pat, value)| (pat, mark_value(value.clone(), &markers)))
                    .collect();
                self.bind_pat_sequence(entries, env)
            }
            Pat::Con(def, payload_pats) => {
                let Value::DataConstructor {
                    def: value_def,
                    payloads,
                } = view
                else {
                    return bind_done(false, env);
                };
                if def != *value_def || payload_pats.len() != payloads.len() {
                    return bind_done(false, env);
                }
                let entries = payload_pats
                    .into_iter()
                    .zip(payloads)
                    .map(|(pat, value)| (pat, mark_value(value.clone(), &markers)))
                    .collect();
                self.bind_pat_sequence(entries, env)
            }
            Pat::Ref(instance) => {
                let expected = self.eval_instance(instance)?;
                bind_done(value_equivalent(&value, &expected), env)
            }
            Pat::Var(def) => {
                let mut env = env;
                env.insert(def, value);
                bind_done(true, env)
            }
            Pat::Or(left, right) => {
                let value_for_right = value.clone();
                let env_for_right = env.clone();
                let right = *right;
                let left = self.bind_pat(*left, value, env)?;
                self.continue_bind_result(
                    left,
                    Rc::new(move |runtime, matched, left_env| {
                        if matched {
                            return bind_done(true, left_env);
                        }
                        runtime.bind_pat(
                            right.clone(),
                            value_for_right.clone(),
                            env_for_right.clone(),
                        )
                    }),
                )
            }
            Pat::As(pat, def) => {
                let alias_value = value.clone();
                let bound = self.bind_pat(*pat, value, env)?;
                self.continue_bind_result(
                    bound,
                    Rc::new(move |_, matched, mut env| {
                        if !matched {
                            return bind_done(false, env);
                        }
                        env.insert(def, alias_value.clone());
                        bind_done(true, env)
                    }),
                )
            }
        }
    }

    pub(super) fn bind_list_pat(
        &mut self,
        prefix: Vec<Pat>,
        spread: Option<Pat>,
        suffix: Vec<Pat>,
        items: ListTree<Rc<Value>>,
        markers: Vec<ValueMarker>,
        env: CapturedEnv,
    ) -> BindResult<'a> {
        let prefix_len = prefix.len();
        let min_len = prefix.len() + suffix.len();
        if items.len() < min_len || spread.is_none() && items.len() != min_len {
            return bind_done(false, env);
        }

        let mut entries = Vec::new();
        for (index, pat) in prefix.into_iter().enumerate() {
            let Some(item) = items.index(index) else {
                return bind_done(false, env);
            };
            let item = mark_value((*item).clone(), &markers);
            entries.push((pat, item));
        }

        let suffix_start = items.len() - suffix.len();
        for (offset, pat) in suffix.into_iter().enumerate() {
            let Some(item) = items.index(suffix_start + offset) else {
                return bind_done(false, env);
            };
            let item = mark_value((*item).clone(), &markers);
            entries.push((pat, item));
        }

        if let Some(spread) = spread {
            let Some(slice) = items.index_range(prefix_len, suffix_start) else {
                return bind_done(false, env);
            };
            let slice = mark_value(Value::List(slice), &markers);
            entries.push((spread, slice));
        }
        self.bind_pat_sequence(entries, env)
    }

    pub(super) fn bind_pat_sequence(
        &mut self,
        mut entries: Vec<(Pat, Value)>,
        env: CapturedEnv,
    ) -> BindResult<'a> {
        if entries.is_empty() {
            return bind_done(true, env);
        }
        let (pat, value) = entries.remove(0);
        let bound = self.bind_pat(pat, value, env)?;
        self.continue_bind_result(
            bound,
            Rc::new(move |runtime, matched, env| {
                if !matched {
                    return bind_done(false, env);
                }
                runtime.bind_pat_sequence(entries.clone(), env)
            }),
        )
    }

    pub(super) fn bind_record_pat(
        &mut self,
        mut fields: Vec<RecordPatField>,
        spread: RecordSpread<DefId>,
        record_fields: Vec<ValueField>,
        markers: Vec<ValueMarker>,
        used: HashSet<usize>,
        env: CapturedEnv,
    ) -> BindResult<'a> {
        if fields.is_empty() {
            return self.bind_record_spread(spread, record_fields, markers, used, env);
        }

        let RecordPatField { name, pat, default } = fields.remove(0);
        if let Some((index, value_field)) = find_record_field(&record_fields, &name) {
            let mut used = used;
            used.insert(index);
            let value = mark_value(value_field.value.clone(), &markers);
            return self.bind_record_field_value(
                pat,
                value,
                fields,
                spread,
                record_fields,
                markers,
                used,
                env,
            );
        }

        let Some(default) = default else {
            return bind_done(false, env);
        };

        let mut default_env = env.clone();
        let default = self.eval_expr(default, &mut default_env)?;
        self.continue_value_as_bind(
            default,
            env,
            Rc::new(move |runtime, value, env| {
                let value = mark_value(value, &markers);
                runtime.bind_record_field_value(
                    pat.clone(),
                    value,
                    fields.clone(),
                    spread.clone(),
                    record_fields.clone(),
                    markers.clone(),
                    used.clone(),
                    env,
                )
            }),
        )
    }

    pub(super) fn bind_record_field_value(
        &mut self,
        pat: Pat,
        value: Value,
        fields: Vec<RecordPatField>,
        spread: RecordSpread<DefId>,
        record_fields: Vec<ValueField>,
        markers: Vec<ValueMarker>,
        used: HashSet<usize>,
        env: CapturedEnv,
    ) -> BindResult<'a> {
        let bound = self.bind_pat(pat, value, env)?;
        self.continue_bind_result(
            bound,
            Rc::new(move |runtime, matched, env| {
                if !matched {
                    return bind_done(false, env);
                }
                runtime.bind_record_pat(
                    fields.clone(),
                    spread.clone(),
                    record_fields.clone(),
                    markers.clone(),
                    used.clone(),
                    env,
                )
            }),
        )
    }

    pub(super) fn bind_record_spread(
        &mut self,
        spread: RecordSpread<DefId>,
        record_fields: Vec<ValueField>,
        markers: Vec<ValueMarker>,
        used: HashSet<usize>,
        env: CapturedEnv,
    ) -> BindResult<'a> {
        let def = match spread {
            RecordSpread::None => return bind_done(true, env),
            RecordSpread::Head(def) | RecordSpread::Tail(def) => def,
        };
        let captured = record_fields
            .iter()
            .enumerate()
            .filter(|(index, _)| !used.contains(index))
            .map(|(_, field)| ValueField {
                name: field.name.clone(),
                value: mark_value(field.value.clone(), &markers),
            })
            .collect();
        let mut env = env;
        env.insert(def, Value::Record(captured));
        bind_done(true, env)
    }
}
