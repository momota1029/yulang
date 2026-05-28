use super::*;

impl VmContinuation {
    pub(super) fn new(guard_stack: GuardStack) -> Self {
        Self {
            frames: Vec::new(),
            guard_stack,
            blocked_ids: Vec::new(),
        }
    }

    pub(super) fn inside_handle(mut self, id: u64) -> Self {
        if let Some(index) = self
            .frames
            .iter()
            .rposition(|frame| frame_handle_id(frame) == Some(id))
        {
            self.frames.remove(index);
        } else {
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
            if let Some(guard_stack) = frame_handle_guard_stack(&self.frames[index]) {
                self.guard_stack = guard_stack.clone();
            }
            self.frames.truncate(index);
        } else {
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

fn frame_handle_guard_stack(frame: &Frame) -> Option<&GuardStack> {
    match frame {
        Frame::Handle { guard_stack, .. } => Some(guard_stack),
        _ => None,
    }
}
