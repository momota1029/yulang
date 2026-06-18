use super::*;

impl<'a> Runtime<'a> {
    pub(super) fn bind_pat(
        &mut self,
        pat: Pat,
        value: Value,
        env: CapturedEnv,
        then: BindThen,
    ) -> RuntimeResult {
        if pattern_observes_value(&pat) && value_is_thunk_like(&value) {
            let forced = self.force_thunk(value)?;
            self.stats.continue_value_bind_requests +=
                matches!(forced, EvalResult::Request(_)) as u64;
            self.stats.continue_value_bind_values += matches!(forced, EvalResult::Value(_)) as u64;
            return self.continue_with_frame(forced, Frame::BindValue { pat, env, then });
        }

        let (view, markers) = value_view(&value);
        match pat {
            Pat::Wild => self.finish_bind(true, env, then),
            Pat::Lit(lit) => {
                self.finish_bind(value_equivalent(&value, &Value::from(&lit)), env, then)
            }
            Pat::Tuple(pats) => {
                let Value::Tuple(values) = view else {
                    return self.finish_bind(false, env, then);
                };
                if pats.len() != values.len() {
                    return self.finish_bind(false, env, then);
                }
                let entries = pats
                    .into_iter()
                    .zip(values)
                    .map(|(pat, value)| (pat, mark_value(value.clone(), &markers)))
                    .collect();
                self.bind_pat_sequence(entries, env, then)
            }
            Pat::List {
                prefix,
                spread,
                suffix,
            } => {
                let Value::List(items) = view else {
                    return self.finish_bind(false, env, then);
                };
                self.bind_list_pat(
                    prefix,
                    spread.map(|pat| *pat),
                    suffix,
                    items.clone(),
                    markers,
                    env,
                    then,
                )
            }
            Pat::Record { fields, spread } => {
                let Value::Record(record_fields) = view else {
                    return self.finish_bind(false, env, then);
                };
                self.bind_record_pat(
                    fields,
                    spread,
                    record_fields.clone(),
                    markers,
                    HashSet::new(),
                    env,
                    then,
                )
            }
            Pat::PolyVariant(tag, payload_pats) => {
                let Value::PolyVariant {
                    tag: value_tag,
                    payloads,
                } = view
                else {
                    return self.finish_bind(false, env, then);
                };
                if tag != *value_tag || payload_pats.len() != payloads.len() {
                    return self.finish_bind(false, env, then);
                }
                let entries = payload_pats
                    .into_iter()
                    .zip(payloads)
                    .map(|(pat, value)| (pat, mark_value(value.clone(), &markers)))
                    .collect();
                self.bind_pat_sequence(entries, env, then)
            }
            Pat::Con(def, payload_pats) => {
                let Value::DataConstructor {
                    def: value_def,
                    payloads,
                } = view
                else {
                    return self.finish_bind(false, env, then);
                };
                if def != *value_def || payload_pats.len() != payloads.len() {
                    return self.finish_bind(false, env, then);
                }
                let entries = payload_pats
                    .into_iter()
                    .zip(payloads)
                    .map(|(pat, value)| (pat, mark_value(value.clone(), &markers)))
                    .collect();
                self.bind_pat_sequence(entries, env, then)
            }
            Pat::Ref(instance) => {
                let expected = self.eval_instance(instance)?;
                self.finish_bind(value_equivalent(&value, &expected), env, then)
            }
            Pat::Var(def) => {
                let mut env = env;
                env.insert(def, value);
                self.finish_bind(true, env, then)
            }
            Pat::Or(left, right) => {
                let value_for_right = value.clone();
                let env_for_right = env.clone();
                let right = *right;
                self.bind_pat(
                    *left,
                    value,
                    env,
                    BindThen::Or {
                        right,
                        value: value_for_right,
                        env: env_for_right,
                        then: Box::new(then),
                    },
                )
            }
            Pat::As(pat, def) => {
                let alias_value = value.clone();
                self.bind_pat(
                    *pat,
                    value,
                    env,
                    BindThen::As {
                        def,
                        value: alias_value,
                        then: Box::new(then),
                    },
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
        then: BindThen,
    ) -> RuntimeResult {
        let prefix_len = prefix.len();
        let min_len = prefix.len() + suffix.len();
        if items.len() < min_len || spread.is_none() && items.len() != min_len {
            return self.finish_bind(false, env, then);
        }

        let mut entries = Vec::new();
        for (index, pat) in prefix.into_iter().enumerate() {
            let Some(item) = items.index(index) else {
                return self.finish_bind(false, env, then);
            };
            let item = mark_value((*item).clone(), &markers);
            entries.push((pat, item));
        }

        let suffix_start = items.len() - suffix.len();
        for (offset, pat) in suffix.into_iter().enumerate() {
            let Some(item) = items.index(suffix_start + offset) else {
                return self.finish_bind(false, env, then);
            };
            let item = mark_value((*item).clone(), &markers);
            entries.push((pat, item));
        }

        if let Some(spread) = spread {
            let Some(slice) = items.index_range(prefix_len, suffix_start) else {
                return self.finish_bind(false, env, then);
            };
            let slice = mark_value(Value::List(slice), &markers);
            entries.push((spread, slice));
        }
        self.bind_pat_sequence(entries, env, then)
    }

    pub(super) fn bind_pat_sequence(
        &mut self,
        mut entries: Vec<(Pat, Value)>,
        env: CapturedEnv,
        then: BindThen,
    ) -> RuntimeResult {
        if entries.is_empty() {
            return self.finish_bind(true, env, then);
        }
        let (pat, value) = entries.remove(0);
        self.bind_pat(
            pat,
            value,
            env,
            BindThen::Sequence {
                entries,
                then: Box::new(then),
            },
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
        then: BindThen,
    ) -> RuntimeResult {
        if fields.is_empty() {
            return self.bind_record_spread(spread, record_fields, markers, used, env, then);
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
                then,
            );
        }

        let Some(default) = default else {
            return self.finish_bind(false, env, then);
        };

        let mut default_env = env.clone();
        let default = self.eval_expr(default, &mut default_env)?;
        self.continue_with_frame(
            default,
            Frame::BindRecordDefault {
                pat,
                fields,
                spread,
                record_fields,
                markers,
                used,
                env,
                then,
            },
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
        then: BindThen,
    ) -> RuntimeResult {
        self.bind_pat(
            pat,
            value,
            env,
            BindThen::RecordField {
                fields,
                spread,
                record_fields,
                markers,
                used,
                then: Box::new(then),
            },
        )
    }

    pub(super) fn bind_record_spread(
        &mut self,
        spread: RecordSpread<DefId>,
        record_fields: Vec<ValueField>,
        markers: Vec<ValueMarker>,
        used: HashSet<usize>,
        env: CapturedEnv,
        then: BindThen,
    ) -> RuntimeResult {
        let def = match spread {
            RecordSpread::None => return self.finish_bind(true, env, then),
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
        self.finish_bind(true, env, then)
    }
}
