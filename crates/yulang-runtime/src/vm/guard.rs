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
}

pub(super) fn mark_request(mut request: VmRequest, thunk: &VmThunk) -> VmRequest {
    for blocked in &thunk.blocked {
        if effect_is_allowed(&blocked.allowed, &request.effect) {
            continue;
        }
        if request
            .blocked_id
            .is_some_and(|blocked| request.continuation.guard_stack.contains(blocked))
        {
            continue;
        }
        request.blocked_id = Some(blocked.guard_id);
    }
    request
}

pub(super) fn push_frame(mut request: VmRequest, frame: Frame) -> VmRequest {
    request.continuation.frames.insert(0, frame);
    request
}

pub(super) fn prepend_frames(continuation: &mut VmContinuation, mut frames: Vec<Frame>) {
    frames.append(&mut continuation.frames);
    continuation.frames = frames;
}

pub(super) fn effect_is_allowed(allowed: &core_ir::Type, effect: &core_ir::Path) -> bool {
    match allowed {
        core_ir::Type::Any => true,
        core_ir::Type::Never => false,
        core_ir::Type::Named { path, .. } => effect_path_matches_allowed(path, effect),
        core_ir::Type::Row { items, tail } => {
            items.iter().any(|item| effect_is_allowed(item, effect))
                || matches!(tail.as_ref(), core_ir::Type::Any)
        }
        _ => false,
    }
}

pub(super) fn effect_path_matches_allowed(allowed: &core_ir::Path, effect: &core_ir::Path) -> bool {
    if effect.segments.starts_with(&allowed.segments) {
        return true;
    }
    allowed.segments.split_last().is_some_and(|(_, namespace)| {
        !namespace.is_empty() && effect.segments.starts_with(namespace)
    })
}

pub(super) fn is_float_type(ty: &core_ir::Type) -> bool {
    matches!(ty, core_ir::Type::Named { path, args } if args.is_empty() && path.segments.last().is_some_and(|name| name.0 == "float"))
}
