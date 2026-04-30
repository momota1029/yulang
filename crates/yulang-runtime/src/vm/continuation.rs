use super::*;

impl VmContinuation {
    pub(super) fn new(guard_stack: GuardStack) -> Self {
        Self {
            frames: Vec::new(),
            guard_stack,
        }
    }

    pub(super) fn inside_handle(mut self, id: u64) -> Self {
        if let Some(index) = self
            .frames
            .iter()
            .position(|frame| matches!(frame, Frame::Handle { id: current, .. } if *current == id))
        {
            self.frames.drain(..=index);
        } else {
            self.frames.clear();
        }
        self
    }

    pub(super) fn outside_handle(mut self, id: u64) -> Self {
        if let Some(index) = self
            .frames
            .iter()
            .position(|frame| matches!(frame, Frame::Handle { id: current, .. } if *current == id))
        {
            if let Frame::Handle { guard_stack, .. } = &self.frames[index] {
                self.guard_stack = guard_stack.clone();
            }
            self.frames.truncate(index);
        } else {
            self.frames.clear();
        }
        self
    }
}
