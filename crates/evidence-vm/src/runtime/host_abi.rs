//! Host implementation ABI v0 for evidence-vm.
//!
//! Host operations cross this boundary as owned `BoundaryValue`s and return a
//! `HostOutcome`. The ABI intentionally has no access to perform/resume/eval.

use std::any::Any;

#[derive(Debug, Clone, PartialEq)]
pub enum BoundaryValue {
    Unit,
    Bool(bool),
    Int(i64),
    Float(f64),
    Str(String),
    Bytes(Vec<u8>),
    Tuple(Vec<BoundaryValue>),
    Constructor {
        ctor: CtorRef,
        payloads: Vec<BoundaryValue>,
    },
    HostHandle {
        type_id: u32,
        handle: u64,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CtorRef {
    Label(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum HostOutcome {
    Return(BoundaryValue),
    Suspended,
    HostError(String),
}

pub type HostOpFn = fn(ctx: &mut HostCtx<'_>, payload: &BoundaryValue) -> HostOutcome;

#[derive(Debug, Clone, Copy)]
pub struct HostOpRegistration {
    pub act_id: &'static str,
    pub operation_id: &'static str,
    pub f: HostOpFn,
}

pub struct HostCtx<'a> {
    state: &'a mut dyn Any,
}

impl<'a> HostCtx<'a> {
    pub(crate) fn new(state: &'a mut dyn Any) -> Self {
        Self { state }
    }

    pub fn state_mut<T: 'static>(&mut self) -> Option<&mut T> {
        self.state.downcast_mut::<T>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn host_ctx_exposes_only_registered_state() {
        let mut state = String::from("a");
        let mut ctx = HostCtx::new(&mut state);

        ctx.state_mut::<String>().unwrap().push('b');

        assert_eq!(ctx.state_mut::<String>().unwrap(), "ab");
        assert!(ctx.state_mut::<usize>().is_none());
    }
}
