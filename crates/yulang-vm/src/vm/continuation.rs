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
            if let Some(guard_stack) = frame_handle_guard_stack(&self.frames[index]) {
                self.guard_stack = guard_stack.clone();
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

fn trace_handle_event(tag: &str, id: u64, frames: &[Frame]) {
    if !super::interpreter::handle_trace_enabled() {
        return;
    }
    let handle_ids: Vec<u64> = frames.iter().filter_map(|f| frame_handle_id(f)).collect();
    let line = format!(
        "HANDLE_TRACE {tag} target_id={id} frames_len={} handle_ids={:?}",
        frames.len(),
        handle_ids
    );
    super::interpreter::HANDLE_TRACE_BUFFER.with(|cell| cell.borrow_mut().push(line));
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
