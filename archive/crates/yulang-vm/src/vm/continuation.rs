use super::trace::trace_handle_event;
use super::*;

impl VmContinuation {
    pub(super) fn new_with_lookup(guard_stack: GuardStack, lookup_stack: GuardStack) -> Self {
        Self {
            frames: Vec::new(),
            guard_stack,
            lookup_stack,
            blocked_ids: Vec::new(),
        }
    }

    pub(super) fn inside_handle(mut self, id: u64) -> Self {
        if let Some(index) = self
            .frames
            .iter()
            .rposition(|frame| frame_handle_id(frame) == Some(id))
        {
            trace_handle_event("inside_handle.remove", id, &self.frames);
            self.frames.remove(index);
        } else {
            trace_handle_event("inside_handle.clear", id, &self.frames);
            self.frames.clear();
        }
        self
    }

    pub(super) fn outside_handle(mut self, id: u64) -> Self {
        if let Some(index) = self
            .frames
            .iter()
            .rposition(|frame| frame_handle_id(frame) == Some(id))
        {
            if let Some((guard_stack, lookup_stack)) = frame_handle_stacks(&self.frames[index]) {
                self.guard_stack = guard_stack.clone();
                self.lookup_stack = lookup_stack.clone();
            }
            trace_handle_event("outside_handle.truncate", id, &self.frames);
            self.frames.truncate(index);
        } else {
            trace_handle_event("outside_handle.clear", id, &self.frames);
            self.frames.clear();
        }
        self
    }
}

fn frame_handle_id(frame: &Frame) -> Option<u64> {
    match frame {
        Frame::Handle { id, .. } => Some(*id),
        _ => None,
    }
}

fn frame_handle_stacks(frame: &Frame) -> Option<(&GuardStack, &GuardStack)> {
    match frame {
        Frame::Handle {
            guard_stack,
            lookup_stack,
            ..
        } => Some((guard_stack, lookup_stack)),
        _ => None,
    }
}
