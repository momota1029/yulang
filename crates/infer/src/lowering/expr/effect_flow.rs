//! Lowering-only effect flow facade.
//!
//! This table represents administrative effect sequencing before it is emitted
//! as ordinary constraints. The first slice keeps materialization behavior
//! identical to the old lowering; later slices can replace selected fresh
//! `TypeVar` joins with direct fan-out.

use std::sync::OnceLock;

use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;

use super::super::*;
use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(in crate::lowering) struct EffectFlowId(u32);

#[derive(Default)]
pub(in crate::lowering) struct EffectFlowTable {
    nodes: Vec<EffectFlow>,
    vars: FxHashMap<TypeVar, EffectFlowId>,
    materialized: FxHashSet<TypeVar>,
    recursive_returns: FxHashMap<TypeVar, FxHashSet<SubtractId>>,
}

impl EffectFlowTable {
    pub(in crate::lowering) fn new() -> Self {
        Self::default()
    }

    fn push(&mut self, flow: EffectFlow) -> EffectFlowId {
        let id = EffectFlowId(self.nodes.len() as u32);
        self.nodes.push(flow);
        id
    }

    fn get(&self, id: EffectFlowId) -> EffectFlow {
        self.nodes[id.0 as usize].clone()
    }

    fn bind_var(&mut self, var: TypeVar, flow: EffectFlowId) {
        self.vars.insert(var, flow);
    }

    fn var_flow(&self, var: TypeVar) -> Option<EffectFlowId> {
        self.vars.get(&var).copied()
    }

    fn mark_materialized(&mut self, var: TypeVar) -> bool {
        self.materialized.insert(var)
    }

    fn mark_recursive_return(&mut self, var: TypeVar, skipped_subtracts: FxHashSet<SubtractId>) {
        self.recursive_returns
            .entry(var)
            .or_default()
            .extend(skipped_subtracts);
    }

    fn recursive_return_skipped_subtracts(&self, var: TypeVar) -> Option<&FxHashSet<SubtractId>> {
        self.recursive_returns.get(&var)
    }

    fn hole_producers(&self, id: EffectFlowId) -> Vec<PosId> {
        match &self.nodes[id.0 as usize] {
            EffectFlow::Hole(hole) => hole.producers.clone(),
            _ => Vec::new(),
        }
    }

    fn hole_consumers(&self, id: EffectFlowId) -> Vec<EffectFlowConsumer> {
        match &self.nodes[id.0 as usize] {
            EffectFlow::Hole(hole) => hole.consumers.clone(),
            _ => Vec::new(),
        }
    }

    fn add_hole_producers(&mut self, id: EffectFlowId, producers: Vec<PosId>) {
        let EffectFlow::Hole(hole) = &mut self.nodes[id.0 as usize] else {
            return;
        };
        hole.producers.extend(producers);
    }

    fn add_hole_consumer(&mut self, id: EffectFlowId, consumer: EffectFlowConsumer) {
        let EffectFlow::Hole(hole) = &mut self.nodes[id.0 as usize] else {
            return;
        };
        hole.consumers.push(consumer);
    }

    fn unfilled_hole(&self, id: EffectFlowId) -> bool {
        matches!(&self.nodes[id.0 as usize], EffectFlow::Hole(hole) if hole.producers.is_empty())
    }

    fn remove_hole_var_consumers(&mut self, id: EffectFlowId, target: TypeVar) {
        let EffectFlow::Hole(hole) = &mut self.nodes[id.0 as usize] else {
            return;
        };
        hole.consumers
            .retain(|consumer| !consumer.targets_var(target));
    }
}

#[derive(Clone)]
enum EffectFlow {
    Var(TypeVar),
    Pos(PosId),
    Seq(SmallVec<[EffectFlowId; 4]>),
    Hole(EffectFlowHole),
}

#[derive(Clone, Default)]
struct EffectFlowHole {
    producers: Vec<PosId>,
    consumers: Vec<EffectFlowConsumer>,
}

#[derive(Clone)]
enum EffectFlowConsumer {
    Var(TypeVar),
    Neg(NegId),
    StackNeg {
        weight: StackWeight,
        target: NegId,
    },
    SubtractVar {
        subtracts: Vec<StackWeight>,
        target: TypeVar,
    },
}

impl EffectFlowConsumer {
    fn targets_var(&self, target: TypeVar) -> bool {
        match self {
            Self::Var(var) => *var == target,
            Self::SubtractVar {
                target: consumer_target,
                ..
            } => *consumer_target == target,
            Self::Neg(_) | Self::StackNeg { .. } => false,
        }
    }
}

impl<'a> ExprLowerer<'a> {
    pub(in crate::lowering) fn effect_flow_var(&mut self, effect: TypeVar) -> EffectFlowId {
        if let Some(flow) = self.effect_flows.var_flow(effect) {
            trace_effect_flow(|| format!("var effect={effect:?} existing flow={flow:?}"));
            return flow;
        }
        let flow = self.effect_flows.push(EffectFlow::Var(effect));
        trace_effect_flow(|| format!("var effect={effect:?} flow={flow:?}"));
        flow
    }

    pub(in crate::lowering) fn effect_flow_pos(&mut self, effect: PosId) -> EffectFlowId {
        let flow = self.effect_flows.push(EffectFlow::Pos(effect));
        trace_effect_flow(|| format!("pos effect={effect:?} flow={flow:?}"));
        flow
    }

    pub(in crate::lowering) fn seq_effect_flows(
        &mut self,
        parts: impl IntoIterator<Item = EffectFlowId>,
    ) -> EffectFlowId {
        let parts = parts.into_iter().collect::<SmallVec<[_; 4]>>();
        trace_effect_flow(|| format!("seq parts={parts:?}"));
        self.effect_flows.push(EffectFlow::Seq(parts))
    }

    pub(in crate::lowering) fn fresh_effect_flow_hole(&mut self) -> EffectFlowId {
        self.effect_flows
            .push(EffectFlow::Hole(EffectFlowHole::default()))
    }

    pub(in crate::lowering) fn bind_effect_var_to_flow(
        &mut self,
        effect: TypeVar,
        flow: EffectFlowId,
    ) {
        trace_effect_flow(|| format!("bind effect={effect:?} flow={flow:?}"));
        self.effect_flows.bind_var(effect, flow);
    }

    pub(in crate::lowering) fn mark_recursive_return_effect(
        &mut self,
        effect: TypeVar,
        skipped_subtracts: FxHashSet<SubtractId>,
    ) {
        trace_effect_flow(|| {
            format!("mark recursive return effect={effect:?} skipped={skipped_subtracts:?}")
        });
        self.effect_flows
            .mark_recursive_return(effect, skipped_subtracts);
    }

    pub(in crate::lowering) fn connect_effect_flow_to_var(
        &mut self,
        flow: EffectFlowId,
        target: TypeVar,
    ) {
        self.connect_effect_flow_to_consumer(flow, EffectFlowConsumer::Var(target));
    }

    pub(in crate::lowering) fn connect_effect_var_to_var(
        &mut self,
        source: TypeVar,
        target: TypeVar,
    ) {
        trace_effect_flow(|| format!("connect var source={source:?} target={target:?}"));
        let flow = self.effect_flow_var(source);
        self.connect_effect_flow_to_var(flow, target);
    }

    pub(in crate::lowering) fn connect_effect_flow_to_neg(
        &mut self,
        flow: EffectFlowId,
        target: NegId,
    ) {
        self.connect_effect_flow_to_consumer(flow, EffectFlowConsumer::Neg(target));
    }

    pub(in crate::lowering) fn connect_effect_flow_with_stack_to_neg(
        &mut self,
        flow: EffectFlowId,
        weight: StackWeight,
        target: NegId,
    ) {
        self.connect_effect_flow_to_consumer(flow, EffectFlowConsumer::StackNeg { weight, target });
    }

    pub(in crate::lowering) fn connect_effect_flow_with_subtracts_to_var(
        &mut self,
        flow: EffectFlowId,
        subtracts: &[StackWeight],
        target: TypeVar,
    ) {
        trace_effect_flow(|| {
            format!("connect subtract flow={flow:?} target={target:?} subtracts={subtracts:?}")
        });
        self.connect_effect_flow_to_consumer(
            flow,
            EffectFlowConsumer::SubtractVar {
                subtracts: subtracts.to_vec(),
                target,
            },
        );
    }

    pub(in crate::lowering) fn refresh_effect_flow_subtracts_to_var(
        &mut self,
        flow: EffectFlowId,
        subtracts: &[StackWeight],
        target: TypeVar,
    ) {
        if self.effect_flows.unfilled_hole(flow) {
            self.effect_flows.remove_hole_var_consumers(flow, target);
        }
        self.connect_effect_flow_with_subtracts_to_var(flow, subtracts, target);
    }

    pub(in crate::lowering) fn fill_effect_flow_hole(
        &mut self,
        hole: EffectFlowId,
        source: EffectFlowId,
    ) {
        let producers = self.effect_flow_producers(source);
        let consumers = self.effect_flows.hole_consumers(hole);
        trace_effect_flow(|| {
            format!(
                "fill hole={hole:?} source={source:?} producers={} consumers={}",
                producers.len(),
                consumers.len()
            )
        });
        for producer in producers.iter().copied() {
            for consumer in consumers.iter().cloned() {
                self.emit_effect_flow_producer(producer, consumer);
            }
        }
        self.effect_flows.add_hole_producers(hole, producers);
    }

    pub(in crate::lowering) fn effect_var_to_pos(&mut self, effect: TypeVar) -> PosId {
        trace_effect_flow(|| format!("effect var to pos effect={effect:?}"));
        self.materialize_effect_var(effect);
        self.alloc_pos(Pos::Var(effect))
    }

    pub(in crate::lowering) fn materialize_effect_var(&mut self, effect: TypeVar) -> TypeVar {
        trace_effect_flow(|| format!("materialize effect={effect:?}"));
        let Some(flow) = self.effect_flows.var_flow(effect) else {
            return effect;
        };
        if self.effect_flows.mark_materialized(effect) {
            self.connect_effect_flow_to_var(flow, effect);
        }
        effect
    }

    fn connect_effect_flow_to_consumer(
        &mut self,
        flow: EffectFlowId,
        consumer: EffectFlowConsumer,
    ) {
        match self.effect_flows.get(flow) {
            EffectFlow::Var(source) => {
                let source = self.alloc_pos(Pos::Var(source));
                self.emit_effect_flow_producer(source, consumer);
            }
            EffectFlow::Pos(source) => self.emit_effect_flow_producer(source, consumer),
            EffectFlow::Seq(parts) => {
                for part in parts {
                    self.connect_effect_flow_to_consumer(part, consumer.clone());
                }
            }
            EffectFlow::Hole(_) => {
                let producers = self.effect_flows.hole_producers(flow);
                for producer in producers {
                    self.emit_effect_flow_producer(producer, consumer.clone());
                }
                self.effect_flows.add_hole_consumer(flow, consumer);
            }
        }
    }

    fn effect_flow_producers(&mut self, flow: EffectFlowId) -> Vec<PosId> {
        match self.effect_flows.get(flow) {
            EffectFlow::Var(source) => vec![self.alloc_pos(Pos::Var(source))],
            EffectFlow::Pos(source) => vec![source],
            EffectFlow::Seq(parts) => parts
                .into_iter()
                .flat_map(|part| self.effect_flow_producers(part))
                .collect(),
            EffectFlow::Hole(_) => self.effect_flows.hole_producers(flow),
        }
    }

    fn emit_effect_flow_producer(&mut self, producer: PosId, consumer: EffectFlowConsumer) {
        match consumer {
            EffectFlowConsumer::Var(target) => self.subtype_pos_to_var(producer, target),
            EffectFlowConsumer::Neg(target) => self.session.infer.subtype(producer, target),
            EffectFlowConsumer::StackNeg { weight, target } => {
                let producer = self.alloc_pos(Pos::Stack {
                    inner: producer,
                    weight,
                });
                self.session.infer.subtype(producer, target);
            }
            EffectFlowConsumer::SubtractVar { subtracts, target } => {
                trace_effect_flow(|| {
                    format!(
                        "emit subtract producer={:?} {:?} target={target:?} subtracts={subtracts:?}",
                        producer,
                        self.session.infer.constraints().types().pos(producer)
                    )
                });
                let producer = if let Some((source, subtracts)) =
                    self.recursive_return_subtract_sentinel(producer, target, &subtracts)
                {
                    let ids = stack_weight_pop_ids(&subtracts);
                    self.session
                        .infer
                        .constraints_mut()
                        .mark_var_var_replay_pop_sentinels(source, target, ids);
                    self.wrap_pos_with_subtracts(producer, &subtracts)
                } else {
                    self.wrap_effect_flow_producer_with_subtracts(producer, &subtracts)
                };
                self.subtype_pos_to_var(producer, target);
            }
        }
    }

    fn recursive_return_subtract_sentinel(
        &self,
        producer: PosId,
        target: TypeVar,
        subtracts: &[StackWeight],
    ) -> Option<(TypeVar, Vec<StackWeight>)> {
        let Pos::Var(var) = self
            .session
            .infer
            .constraints()
            .types()
            .pos(producer)
            .clone()
        else {
            return None;
        };
        let skipped = self.effect_flows.recursive_return_skipped_subtracts(var)?;
        let subtracts = subtracts
            .iter()
            .map(|weight| weight.without_ids(|id| skipped.contains(&id)))
            .filter(|weight| !weight.is_empty())
            .collect::<Vec<_>>();
        if subtracts.is_empty() {
            return None;
        }
        trace_effect_flow(|| format!("sentinel recursive return source={var:?} target={target:?}"));
        Some((var, subtracts))
    }

    fn wrap_effect_flow_producer_with_subtracts(
        &mut self,
        producer: PosId,
        subtracts: &[StackWeight],
    ) -> PosId {
        if subtracts.is_empty() {
            return producer;
        }
        match self
            .session
            .infer
            .constraints()
            .types()
            .pos(producer)
            .clone()
        {
            Pos::Stack { .. } => self.wrap_pos_with_subtracts(producer, subtracts),
            Pos::Union(left, right) => {
                let left = self.wrap_effect_flow_producer_with_subtracts(left, subtracts);
                let right = self.wrap_effect_flow_producer_with_subtracts(right, subtracts);
                self.alloc_pos(Pos::Union(left, right))
            }
            Pos::Var(var) => {
                let Some(skipped) = self.effect_flows.recursive_return_skipped_subtracts(var)
                else {
                    return self.wrap_pos_with_subtracts(producer, subtracts);
                };
                let subtracts = subtracts
                    .iter()
                    .map(|weight| weight.without_ids(|id| skipped.contains(&id)))
                    .filter(|weight| !weight.is_empty())
                    .collect::<Vec<_>>();
                self.wrap_pos_with_subtracts(producer, &subtracts)
            }
            _ => self.wrap_pos_with_subtracts(producer, subtracts),
        }
    }
}

pub(in crate::lowering) fn trace_effect_flow(message: impl FnOnce() -> String) {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    if *ENABLED.get_or_init(|| std::env::var("YULANG_TRACE_EFFECT_FLOW").is_ok()) {
        eprintln!("[effect-flow] {}", message());
    }
}

fn stack_weight_pop_ids(weights: &[StackWeight]) -> Vec<SubtractId> {
    let mut ids = Vec::new();
    for weight in weights {
        for entry in weight.entries() {
            if entry.pops > 0 && !ids.contains(&entry.id) {
                ids.push(entry.id);
            }
        }
    }
    ids
}
