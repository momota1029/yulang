use std::collections::HashMap;

use super::*;

#[derive(Debug, Clone, Default)]
pub(super) struct ScopeState {
    frames: Vec<ScopeFrame>,
    handler_frames: Vec<ScopeHandlerFrame>,
    add_markers: Vec<ScopeAddMarker>,
    all_path_add_marker_count: usize,
    own_path_add_markers: HashMap<u32, Vec<usize>>,
    foreign_path_add_marker_count: usize,
    foreign_path_add_markers: HashMap<u32, Vec<usize>>,
}

impl ScopeState {
    pub(super) fn new() -> Self {
        Self::default()
    }

    pub(super) fn push_frame(&mut self, id: GuardId) {
        self.frames.push(ScopeFrame { id });
    }

    pub(super) fn push_handler_frame(
        &mut self,
        frame_index: usize,
        id: GuardId,
        handler_key: InternedPathPrefix,
    ) {
        self.handler_frames.push(ScopeHandlerFrame {
            frame_index,
            id,
            handler_key,
        });
    }

    pub(super) fn push_add_marker(&mut self, marker: ActiveAddIdMarker) {
        let index = self.add_markers.len();
        let entry_except = self.entry_except(marker.entry_frame_len);
        self.push_add_marker_index(index, &marker.marker);
        self.add_markers.push(ScopeAddMarker {
            marker: marker.marker,
            entry_frame_len: marker.entry_frame_len,
            entry_except,
        });
    }

    pub(super) fn truncate(
        &mut self,
        frame_len: usize,
        handler_frame_len: usize,
        add_id_len: usize,
    ) {
        self.frames.truncate(frame_len);
        self.handler_frames.truncate(handler_frame_len);
        while self.add_markers.len() > add_id_len {
            let index = self.add_markers.len() - 1;
            let marker = self.add_markers.pop().expect("checked add marker").marker;
            self.pop_add_marker_index(index, &marker);
        }
    }

    pub(super) fn path_candidate_stats(
        &self,
        request_key: &InternedPath,
    ) -> ScopePathCandidateStats {
        let mut own_path_candidates = 0;
        let mut foreign_path_excluded = 0;
        for prefix_id in request_key.prefix_ids.iter() {
            own_path_candidates += self.own_path_add_markers.get(prefix_id).map_or(0, Vec::len);
            foreign_path_excluded += self
                .foreign_path_add_markers
                .get(prefix_id)
                .map_or(0, Vec::len);
        }
        let foreign_path_candidates = self
            .foreign_path_add_marker_count
            .saturating_sub(foreign_path_excluded);
        ScopePathCandidateStats {
            active_add_markers: self.add_markers.len(),
            path_candidates: self.all_path_add_marker_count
                + own_path_candidates
                + foreign_path_candidates,
            all_path_candidates: self.all_path_add_marker_count,
            own_path_candidates,
            foreign_path_candidates,
        }
    }

    pub(super) fn mark_request(&self, request: &Request) -> ScopeRequestMarking {
        let mut marking = ScopeRequestMarking::from_request(request);
        for active_marker in &self.add_markers {
            let marker = &active_marker.marker;
            let path_matches_marker = request.path_key.has_prefix(marker.path_key);
            if (path_matches_marker && !marker.guard_own_path)
                || (!path_matches_marker && !marker.guard_foreign_path)
                || (!marker.carry_after_frame && active_marker.excepts(&marking.guard_ids))
            {
                continue;
            }

            if marker.carry_after_frame && !marking.has_carried_guard(marker.id) {
                let exposed_guard_ids =
                    self.carried_exposed_guard_ids(request, &marking, active_marker);
                marking.guard_ids.push_unique(marker.id);
                marking.carried_guards.push(CarriedGuard {
                    id: marker.id,
                    entry_frame_len: active_marker.entry_frame_len,
                    exposed_guard_ids,
                });
            } else if !marker.carry_after_frame {
                marking.guard_ids.push_unique(marker.id);
            }
        }
        marking
    }

    fn entry_except(&self, entry_frame_len: usize) -> GuardIds {
        self.frames
            .iter()
            .take(entry_frame_len)
            .map(|frame| frame.id)
            .fold(GuardIds::new(), |mut ids, id| {
                ids.push_unique(id);
                ids
            })
    }

    fn carried_exposed_guard_ids(
        &self,
        request: &Request,
        marking: &ScopeRequestMarking,
        active_marker: &ScopeAddMarker,
    ) -> GuardIds {
        let mut ids = active_marker
            .entry_except
            .iter()
            .filter_map(|id| marking.guard_ids.contains(*id).then_some(*id))
            .fold(GuardIds::new(), |mut ids, id| {
                ids.push_unique(id);
                ids
            });
        if active_marker.marker.preserve_own_on_resume {
            self.push_contract_matching_handler_ids(
                request,
                active_marker.entry_frame_len,
                &mut ids,
            );
        }
        if self.exposes_matching_handler_alias(request, active_marker.entry_frame_len, &ids)
            && let Some(handler_id) = self.outermost_matching_handler_id(&request.path_key)
            && !ids.contains(handler_id)
        {
            ids.push_unique(handler_id);
        }
        ids
    }

    fn push_contract_matching_handler_ids(
        &self,
        request: &Request,
        entry_frame_len: usize,
        ids: &mut GuardIds,
    ) {
        for frame in &self.handler_frames {
            if frame.frame_index < entry_frame_len && request.path_key.has_prefix(frame.handler_key)
            {
                ids.push_unique(frame.id);
            }
        }
    }

    fn exposes_matching_handler_alias(
        &self,
        request: &Request,
        entry_frame_len: usize,
        ids: &GuardIds,
    ) -> bool {
        ids.iter().any(|id| {
            self.handler_frames.iter().any(|frame| {
                frame.frame_index < entry_frame_len
                    && frame.id == *id
                    && request.path_key.has_prefix(frame.handler_key)
            })
        })
    }

    fn outermost_matching_handler_id(&self, request_key: &InternedPath) -> Option<GuardId> {
        self.handler_frames
            .iter()
            .find(|frame| request_key.has_prefix(frame.handler_key))
            .map(|frame| frame.id)
    }

    fn push_add_marker_index(&mut self, index: usize, marker: &AddIdMarker) {
        match (marker.guard_own_path, marker.guard_foreign_path) {
            (true, true) => self.all_path_add_marker_count += 1,
            (true, false) => self
                .own_path_add_markers
                .entry(marker.path_key.id)
                .or_default()
                .push(index),
            (false, true) => {
                self.foreign_path_add_marker_count += 1;
                self.foreign_path_add_markers
                    .entry(marker.path_key.id)
                    .or_default()
                    .push(index);
            }
            (false, false) => {}
        }
    }

    fn pop_add_marker_index(&mut self, index: usize, marker: &AddIdMarker) {
        match (marker.guard_own_path, marker.guard_foreign_path) {
            (true, true) => {
                self.all_path_add_marker_count = self
                    .all_path_add_marker_count
                    .checked_sub(1)
                    .expect("all-path add marker index should be balanced");
            }
            (true, false) => {
                pop_marker_index(&mut self.own_path_add_markers, marker.path_key.id, index)
            }
            (false, true) => {
                self.foreign_path_add_marker_count = self
                    .foreign_path_add_marker_count
                    .checked_sub(1)
                    .expect("foreign-path add marker index should be balanced");
                pop_marker_index(
                    &mut self.foreign_path_add_markers,
                    marker.path_key.id,
                    index,
                );
            }
            (false, false) => {}
        }
    }
}

fn pop_marker_index(indexes: &mut HashMap<u32, Vec<usize>>, prefix_id: u32, index: usize) {
    let Some(entries) = indexes.get_mut(&prefix_id) else {
        panic!("path add marker index should contain prefix {prefix_id}");
    };
    let popped = entries
        .pop()
        .expect("path add marker index should not be empty");
    assert_eq!(popped, index, "path add marker index should be LIFO");
    if entries.is_empty() {
        indexes.remove(&prefix_id);
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(super) struct ScopePathCandidateStats {
    pub(super) active_add_markers: usize,
    pub(super) path_candidates: usize,
    pub(super) all_path_candidates: usize,
    pub(super) own_path_candidates: usize,
    pub(super) foreign_path_candidates: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ScopeRequestMarking {
    guard_ids: GuardIds,
    carried_guards: Vec<CarriedGuard>,
}

impl ScopeRequestMarking {
    pub(super) fn from_request(request: &Request) -> Self {
        Self {
            guard_ids: request.guard_ids.clone(),
            carried_guards: request.carried_guards.clone(),
        }
    }

    fn has_carried_guard(&self, id: GuardId) -> bool {
        self.carried_guards.iter().any(|guard| guard.id == id)
    }
}

#[derive(Debug, Clone, Copy)]
struct ScopeFrame {
    id: GuardId,
}

#[derive(Debug, Clone, Copy)]
struct ScopeHandlerFrame {
    frame_index: usize,
    id: GuardId,
    handler_key: InternedPathPrefix,
}

#[derive(Debug, Clone)]
struct ScopeAddMarker {
    marker: AddIdMarker,
    entry_frame_len: usize,
    entry_except: GuardIds,
}

impl ScopeAddMarker {
    fn excepts(&self, request_guard_ids: &GuardIds) -> bool {
        self.entry_except
            .iter()
            .any(|id| request_guard_ids.contains(*id))
    }
}
