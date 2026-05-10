use super::*;

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct DemandQueue {
    semantics: DemandSemantics,
    queue: std::collections::VecDeque<Demand>,
    seen: std::collections::HashSet<DemandKey>,
    profile: DemandQueueProfile,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct DemandQueueProfile {
    pub attempted: usize,
    pub pushed: usize,
    pub pushed_open: usize,
    pub pushed_closed: usize,
    pub skipped_duplicate: usize,
    pub skipped_covered_by_closed: usize,
}

impl DemandQueue {
    pub(super) fn with_semantics(semantics: DemandSemantics) -> Self {
        Self {
            semantics,
            ..Self::default()
        }
    }

    pub fn push(&mut self, target: core_ir::Path, expected: RuntimeType) -> bool {
        let demand = Demand::new_with_semantics(&self.semantics, target, expected);
        self.push_demand(demand)
    }

    pub fn push_signature(
        &mut self,
        target: core_ir::Path,
        expected: RuntimeType,
        signature: DemandSignature,
    ) -> bool {
        let demand =
            Demand::with_signature_and_semantics(&self.semantics, target, expected, signature);
        self.push_demand(demand)
    }

    fn push_demand(&mut self, demand: Demand) -> bool {
        self.profile.attempted += 1;
        if !demand.key.signature.is_closed()
            && self.seen.iter().any(|key| {
                key.target == demand.target
                    && key.signature.is_closed()
                    && closed_signature_covers_open(&key.signature, &demand.key.signature)
            })
        {
            self.profile.skipped_covered_by_closed += 1;
            return false;
        }
        if !self.seen.insert(demand.key.clone()) {
            self.profile.skipped_duplicate += 1;
            return false;
        }
        if demand.key.signature.is_closed() {
            self.profile.pushed_closed += 1;
        } else {
            self.profile.pushed_open += 1;
        }
        self.profile.pushed += 1;
        self.queue.push_back(demand);
        true
    }

    pub fn pop_front(&mut self) -> Option<Demand> {
        self.queue.pop_front()
    }

    pub fn len(&self) -> usize {
        self.queue.len()
    }

    pub fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }

    pub fn profile(&self) -> DemandQueueProfile {
        self.profile
    }

    pub fn iter(&self) -> impl Iterator<Item = &Demand> {
        self.queue.iter()
    }
}

impl DemandQueueProfile {
    pub fn merge(&mut self, other: Self) {
        self.attempted += other.attempted;
        self.pushed += other.pushed;
        self.pushed_open += other.pushed_open;
        self.pushed_closed += other.pushed_closed;
        self.skipped_duplicate += other.skipped_duplicate;
        self.skipped_covered_by_closed += other.skipped_covered_by_closed;
    }
}

fn closed_signature_covers_open(closed: &DemandSignature, open: &DemandSignature) -> bool {
    match (closed, open) {
        (_, DemandSignature::Ignored | DemandSignature::Hole(_)) => true,
        (DemandSignature::Core(closed), DemandSignature::Core(open)) => {
            closed_core_type_covers_open(closed, open)
        }
        (
            DemandSignature::Fun {
                param: closed_param,
                ret: closed_ret,
            },
            DemandSignature::Fun {
                param: open_param,
                ret: open_ret,
            },
        ) => {
            closed_signature_covers_open(closed_param, open_param)
                && closed_signature_covers_open(closed_ret, open_ret)
        }
        (
            DemandSignature::Thunk {
                effect: closed_effect,
                value: closed_value,
            },
            DemandSignature::Thunk {
                effect: open_effect,
                value: open_value,
            },
        ) => {
            closed_effect_covers_open(closed_effect, open_effect)
                && closed_signature_covers_open(closed_value, open_value)
        }
        _ => false,
    }
}

fn closed_effect_covers_open(closed: &DemandEffect, open: &DemandEffect) -> bool {
    match (closed, open) {
        (_, DemandEffect::Hole(_)) => true,
        (DemandEffect::Empty, DemandEffect::Empty) => true,
        (DemandEffect::Atom(closed), DemandEffect::Atom(open)) => {
            closed_core_type_covers_open(closed, open)
        }
        (DemandEffect::Row(closed), DemandEffect::Row(open)) => {
            closed.len() == open.len()
                && closed
                    .iter()
                    .zip(open)
                    .all(|(closed, open)| closed_effect_covers_open(closed, open))
        }
        _ => false,
    }
}

fn closed_core_type_covers_open(closed: &DemandCoreType, open: &DemandCoreType) -> bool {
    match (closed, open) {
        (_, DemandCoreType::Any | DemandCoreType::Hole(_)) => true,
        (DemandCoreType::Never, DemandCoreType::Never) => true,
        (
            DemandCoreType::Named {
                path: closed_path,
                args: closed_args,
            },
            DemandCoreType::Named {
                path: open_path,
                args: open_args,
            },
        ) => {
            closed_path == open_path
                && closed_args.len() == open_args.len()
                && closed_args
                    .iter()
                    .zip(open_args)
                    .all(|(closed, open)| closed_type_arg_covers_open(closed, open))
        }
        (
            DemandCoreType::Fun {
                param: closed_param,
                param_effect: closed_param_effect,
                ret_effect: closed_ret_effect,
                ret: closed_ret,
            },
            DemandCoreType::Fun {
                param: open_param,
                param_effect: open_param_effect,
                ret_effect: open_ret_effect,
                ret: open_ret,
            },
        ) => {
            closed_core_type_covers_open(closed_param, open_param)
                && closed_effect_covers_open(closed_param_effect, open_param_effect)
                && closed_effect_covers_open(closed_ret_effect, open_ret_effect)
                && closed_core_type_covers_open(closed_ret, open_ret)
        }
        (DemandCoreType::Tuple(closed), DemandCoreType::Tuple(open))
        | (DemandCoreType::Union(closed), DemandCoreType::Union(open))
        | (DemandCoreType::Inter(closed), DemandCoreType::Inter(open)) => {
            closed.len() == open.len()
                && closed
                    .iter()
                    .zip(open)
                    .all(|(closed, open)| closed_core_type_covers_open(closed, open))
        }
        (DemandCoreType::Record(closed), DemandCoreType::Record(open)) => {
            closed.len() == open.len()
                && closed.iter().zip(open).all(|(closed, open)| {
                    closed.name == open.name
                        && closed.optional == open.optional
                        && closed_core_type_covers_open(&closed.value, &open.value)
                })
        }
        (DemandCoreType::Variant(closed), DemandCoreType::Variant(open)) => {
            closed.len() == open.len()
                && closed.iter().zip(open).all(|(closed, open)| {
                    closed.name == open.name
                        && closed.payloads.len() == open.payloads.len()
                        && closed
                            .payloads
                            .iter()
                            .zip(&open.payloads)
                            .all(|(closed, open)| closed_core_type_covers_open(closed, open))
                })
        }
        (DemandCoreType::RowAsValue(closed), DemandCoreType::RowAsValue(open)) => {
            closed.len() == open.len()
                && closed
                    .iter()
                    .zip(open)
                    .all(|(closed, open)| closed_effect_covers_open(closed, open))
        }
        (
            DemandCoreType::Recursive {
                var: closed_var,
                body: closed_body,
            },
            DemandCoreType::Recursive {
                var: open_var,
                body: open_body,
            },
        ) => closed_var == open_var && closed_core_type_covers_open(closed_body, open_body),
        _ => false,
    }
}

fn closed_type_arg_covers_open(closed: &DemandTypeArg, open: &DemandTypeArg) -> bool {
    match (closed, open) {
        (DemandTypeArg::Type(closed), DemandTypeArg::Type(open)) => {
            closed_core_type_covers_open(closed, open)
        }
        (
            DemandTypeArg::Bounds {
                lower: closed_lower,
                upper: closed_upper,
            },
            DemandTypeArg::Bounds {
                lower: open_lower,
                upper: open_upper,
            },
        ) => {
            optional_closed_core_type_covers_open(closed_lower.as_ref(), open_lower.as_ref())
                && optional_closed_core_type_covers_open(
                    closed_upper.as_ref(),
                    open_upper.as_ref(),
                )
        }
        _ => false,
    }
}

fn optional_closed_core_type_covers_open(
    closed: Option<&DemandCoreType>,
    open: Option<&DemandCoreType>,
) -> bool {
    match (closed, open) {
        (_, None) => true,
        (Some(closed), Some(open)) => closed_core_type_covers_open(closed, open),
        (None, Some(_)) => false,
    }
}
