use super::*;

const PERSISTENT_VECTOR_CHUNK: usize = 32;

impl<T> Default for PersistentVector<T> {
    fn default() -> Self {
        Self { len: 0, tail: None }
    }
}

impl<T: Clone> PersistentVector<T> {
    pub(super) fn push(&self, item: T) -> Self {
        if let Some(tail) = &self.tail
            && tail.items.len() < PERSISTENT_VECTOR_CHUNK
        {
            let mut items = tail.items.iter().cloned().collect::<Vec<_>>();
            items.push(item);
            return Self {
                len: self.len + 1,
                tail: Some(Rc::new(PersistentVectorChunk {
                    items: Rc::from(items.into_boxed_slice()),
                    parent: tail.parent.clone(),
                })),
            };
        }

        Self {
            len: self.len + 1,
            tail: Some(Rc::new(PersistentVectorChunk {
                items: Rc::from(vec![item].into_boxed_slice()),
                parent: self.tail.clone(),
            })),
        }
    }

    pub(super) fn last(&self) -> Option<&T> {
        self.tail.as_ref().and_then(|chunk| chunk.items.last())
    }

    pub(super) fn any_chunk_newest(&self, mut f: impl FnMut(&[T]) -> bool) -> bool {
        let mut cursor = self.tail.as_ref();
        while let Some(chunk) = cursor {
            if f(&chunk.items) {
                return true;
            }
            cursor = chunk.parent.as_ref();
        }
        false
    }

    pub(super) fn find_map_newest<R>(&self, mut f: impl FnMut(&[T]) -> Option<R>) -> Option<R> {
        let mut cursor = self.tail.as_ref();
        while let Some(chunk) = cursor {
            if let Some(value) = f(&chunk.items) {
                return Some(value);
            }
            cursor = chunk.parent.as_ref();
        }
        None
    }

    fn items_oldest(&self) -> Vec<T> {
        let mut chunks = Vec::new();
        let mut cursor = self.tail.as_ref();
        while let Some(chunk) = cursor {
            chunks.push(chunk.clone());
            cursor = chunk.parent.as_ref();
        }
        let mut out = Vec::with_capacity(self.len);
        for chunk in chunks.into_iter().rev() {
            out.extend(chunk.items.iter().cloned());
        }
        out
    }
}

impl GuardStack {
    pub(super) fn push(&self, entry: GuardEntry) -> Self {
        Self(self.0.push(entry))
    }

    pub(super) fn peek(&self) -> Option<u64> {
        self.0.last().map(|entry| entry.id)
    }

    pub(super) fn contains(&self, id: u64) -> bool {
        self.0
            .any_chunk_newest(|chunk| chunk.binary_search_by_key(&id, |entry| entry.id).is_ok())
    }

    pub(super) fn find_var(&self, var: EffectIdVar) -> Option<u64> {
        self.0.find_map_newest(|chunk| {
            chunk
                .iter()
                .rev()
                .find(|entry| entry.var == var)
                .map(|entry| entry.id)
        })
    }

    pub(super) fn overlay_newer(&self, newer: &Self) -> Self {
        newer
            .0
            .items_oldest()
            .into_iter()
            .fold(self.clone(), |stack, entry| {
                if stack.find_var(entry.var).is_some() {
                    stack
                } else {
                    stack.push(entry)
                }
            })
    }
}

#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn mark_request(request: VmRequest, thunk: &VmThunk) -> VmRequest {
    mark_request_with_blocked(request, &thunk.blocked)
}

pub(super) fn mark_request_with_blocked(
    mut request: VmRequest,
    blocked_effects: &[BlockedEffect],
) -> VmRequest {
    for blocked in blocked_effects {
        if effect_is_allowed(&blocked.allowed, &request.effect) {
            continue;
        }
        let has_live_blocker = request_has_live_blocker(&request);
        add_request_blocker(&mut request, blocked.guard_id, !has_live_blocker);
    }
    request
}

pub(super) fn mark_request_with_active_blocked(
    mut request: VmRequest,
    blocked_effects: &[BlockedEffect],
) -> VmRequest {
    for blocked in blocked_effects.iter().rev() {
        if effect_is_allowed(&blocked.allowed, &request.effect) {
            continue;
        }
        let has_live_blocker = request_has_live_blocker(&request);
        add_request_blocker(&mut request, blocked.guard_id, !has_live_blocker);
    }
    request
}

pub(super) fn request_is_blocked_by_stack(request: &VmRequest, stack: &GuardStack) -> bool {
    request
        .blocked_id
        .is_some_and(|blocked| stack.contains(blocked))
        || request
            .continuation
            .blocked_ids
            .iter()
            .any(|blocked| stack.contains(*blocked))
}

fn add_request_blocker(request: &mut VmRequest, guard_id: u64, replace_primary: bool) {
    if replace_primary {
        if let Some(previous) = request.blocked_id
            && previous != guard_id
            && !request.continuation.blocked_ids.contains(&previous)
        {
            request.continuation.blocked_ids.push(previous);
        }
        request.blocked_id = Some(guard_id);
    } else if request.blocked_id != Some(guard_id)
        && !request.continuation.blocked_ids.contains(&guard_id)
    {
        request.continuation.blocked_ids.push(guard_id);
    }
}

fn request_has_live_blocker(request: &VmRequest) -> bool {
    request_blocker_is_live(request, request.blocked_id)
        || request
            .continuation
            .blocked_ids
            .iter()
            .any(|blocked| request_blocker_is_live(request, Some(*blocked)))
}

fn request_blocker_is_live(request: &VmRequest, blocked: Option<u64>) -> bool {
    blocked.is_some_and(|blocked| {
        request.continuation.guard_stack.contains(blocked)
            || request.continuation.frames.iter().any(|frame| match frame {
                Frame::Handle { guard_stack, .. } => guard_stack.contains(blocked),
                Frame::HandleGuard {
                    handler_guard_stack,
                    ..
                } => handler_guard_stack.contains(blocked),
                _ => false,
            })
    })
}

pub(super) fn push_frame(mut request: VmRequest, frame: Frame) -> VmRequest {
    request.continuation.frames.insert(0, frame);
    request
}

pub(super) fn prepend_frames(continuation: &mut VmContinuation, mut frames: Vec<Frame>) {
    frames.append(&mut continuation.frames);
    continuation.frames = frames;
}

pub(super) fn effect_is_allowed(allowed: &typed_ir::Type, effect: &typed_ir::Path) -> bool {
    match allowed {
        typed_ir::Type::Any => true,
        typed_ir::Type::Never => false,
        typed_ir::Type::Named { path, .. } => effect_path_matches_allowed(path, effect),
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(|item| effect_is_allowed(item, effect))
                || matches!(tail.as_ref(), typed_ir::Type::Any)
        }
        _ => false,
    }
}

pub(super) fn effect_path_matches_allowed(
    allowed: &typed_ir::Path,
    effect: &typed_ir::Path,
) -> bool {
    if effect.segments.starts_with(&allowed.segments) {
        return true;
    }
    if allowed.segments.len() > 1
        && effect.segments.len() == allowed.segments.len()
        && effect.segments[..effect.segments.len() - 1]
            == allowed.segments[..allowed.segments.len() - 1]
        && effect_segment_matches_allowed(
            &allowed.segments[allowed.segments.len() - 1],
            &effect.segments[effect.segments.len() - 1],
        )
    {
        return true;
    }
    effect
        .segments
        .iter()
        .enumerate()
        .skip(1)
        .any(|(index, _)| effect.segments[index..].starts_with(&allowed.segments))
}

pub(super) fn effect_operation_path_matches(
    handled: &typed_ir::Path,
    requested: &typed_ir::Path,
) -> bool {
    if handled.segments.is_empty() || requested.segments.is_empty() {
        return handled == requested;
    }
    effect_path_matches_allowed(handled, requested)
        || (handled.segments.len() == requested.segments.len()
            && handled.segments.len() > 1
            && handled.segments[..handled.segments.len() - 1]
                == requested.segments[..requested.segments.len() - 1]
            && effect_segment_matches_allowed(
                &handled.segments[handled.segments.len() - 1],
                &requested.segments[requested.segments.len() - 1],
            ))
}

fn effect_segment_matches_allowed(allowed: &typed_ir::Name, effect: &typed_ir::Name) -> bool {
    allowed == effect
        || effect
            .0
            .strip_suffix("#effect")
            .is_some_and(|base| base == allowed.0)
}

pub(super) fn is_float_type(ty: &typed_ir::Type) -> bool {
    matches!(ty, typed_ir::Type::Named { path, args } if args.is_empty() && path == &standard_float_path())
}

pub(super) fn is_path_type(ty: &typed_ir::Type) -> bool {
    matches!(ty, typed_ir::Type::Named { path, args } if args.is_empty() && path == &standard_path_path())
}

fn standard_float_path() -> typed_ir::Path {
    typed_ir::Path::from_name(typed_ir::Name("float".to_string()))
}

fn standard_path_path() -> typed_ir::Path {
    typed_ir::Path::new(vec![
        typed_ir::Name("std".to_string()),
        typed_ir::Name("path".to_string()),
        typed_ir::Name("path".to_string()),
    ])
}
