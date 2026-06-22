//! Lowering-only effect flow facade.
//!
//! This table represents administrative effect sequencing before it is emitted
//! as ordinary constraints. The first slice keeps materialization behavior
//! identical to the old lowering; later slices can replace selected fresh
//! `TypeVar` joins with direct fan-out.

use smallvec::SmallVec;

use super::super::*;
use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(in crate::lowering) struct EffectFlowId(u32);

#[derive(Default)]
pub(in crate::lowering) struct EffectFlowTable {
    nodes: Vec<EffectFlow>,
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
}

#[derive(Clone)]
enum EffectFlow {
    Var(TypeVar),
    Pos(PosId),
    Seq(SmallVec<[EffectFlowId; 4]>),
}

impl<'a> ExprLowerer<'a> {
    pub(in crate::lowering) fn effect_flow_var(&mut self, effect: TypeVar) -> EffectFlowId {
        self.effect_flows.push(EffectFlow::Var(effect))
    }

    pub(in crate::lowering) fn effect_flow_pos(&mut self, effect: PosId) -> EffectFlowId {
        self.effect_flows.push(EffectFlow::Pos(effect))
    }

    pub(in crate::lowering) fn seq_effect_flows(
        &mut self,
        parts: impl IntoIterator<Item = EffectFlowId>,
    ) -> EffectFlowId {
        let parts = parts.into_iter().collect::<SmallVec<[_; 4]>>();
        self.effect_flows.push(EffectFlow::Seq(parts))
    }

    pub(in crate::lowering) fn connect_effect_flow_to_var(
        &mut self,
        flow: EffectFlowId,
        target: TypeVar,
    ) {
        match self.effect_flows.get(flow) {
            EffectFlow::Var(source) => self.subtype_var_to_var(source, target),
            EffectFlow::Pos(source) => self.subtype_pos_to_var(source, target),
            EffectFlow::Seq(parts) => {
                for part in parts {
                    self.connect_effect_flow_to_var(part, target);
                }
            }
        }
    }
}
