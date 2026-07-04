#![allow(dead_code)]
// This module is wired into the runner before the server suspend path exists.
// The branch/cancel APIs are locked by unit tests now and become live when the
// in-process server driver starts creating suspended host branches.

use std::cell::RefCell;
use std::collections::{BTreeMap, VecDeque};
use std::rc::Rc;

use super::host_abi::BoundaryValue;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct RuntimeHostBranchId(u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct RuntimeHostOperationInstanceId {
    branch_id: RuntimeHostBranchId,
    parent_branch_id: Option<RuntimeHostBranchId>,
    seq: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct RuntimeHostBranchSpawn {
    child_branch_id: RuntimeHostBranchId,
    parent_branch_id: RuntimeHostBranchId,
    resume_ordinal: u64,
}

impl RuntimeHostBranchSpawn {
    pub(super) fn child_branch_id(&self) -> RuntimeHostBranchId {
        self.child_branch_id
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RuntimeHostBranchStatus {
    Running,
    Suspended,
    CancelPending,
    Dropped,
    Completed,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RuntimeHostCancelReason {
    ParentExtentClosed,
    HostDisconnected,
    Timeout,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HostResumeTokenId(u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HostResumeError {
    NotSuspended,
    AlreadyConsumed,
    Closed,
    Dropped,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HostSuspendError {
    UnsupportedTier,
    AlreadyIssued,
}

#[derive(Clone)]
pub struct HostResumeToken {
    inner: Rc<RefCell<HostResumeTokenInner>>,
    queue: RuntimeHostSchedulerQueueHandle,
}

#[derive(Debug)]
struct HostResumeTokenInner {
    id: HostResumeTokenId,
    kind: HostResumeTokenKind,
    branch_id: Option<RuntimeHostBranchId>,
    status: HostResumeTokenStatus,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HostResumeTokenKind {
    OneShot,
    MultiShot,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HostResumeTokenStatus {
    Issued,
    Suspended,
    Consumed,
    Closed,
    Dropped,
}

impl HostResumeToken {
    pub fn resume(&self, value: BoundaryValue) -> Result<(), HostResumeError> {
        let event = {
            let mut inner = self.inner.borrow_mut();
            match inner.status {
                HostResumeTokenStatus::Issued => return Err(HostResumeError::NotSuspended),
                HostResumeTokenStatus::Suspended => match inner.kind {
                    HostResumeTokenKind::OneShot => {
                        inner.status = HostResumeTokenStatus::Consumed;
                        RuntimeHostSchedulerQueuedEvent::ResumeOneShot {
                            branch_id: inner
                                .branch_id
                                .expect("suspended one-shot token must have a branch"),
                            token_id: inner.id,
                            value,
                        }
                    }
                    HostResumeTokenKind::MultiShot => {
                        RuntimeHostSchedulerQueuedEvent::ResumeMultiShot {
                            parent_branch_id: inner
                                .branch_id
                                .expect("suspended multi-shot token must have a parent branch"),
                            token_id: inner.id,
                            value,
                        }
                    }
                },
                HostResumeTokenStatus::Consumed => return Err(HostResumeError::AlreadyConsumed),
                HostResumeTokenStatus::Closed => return Err(HostResumeError::Closed),
                HostResumeTokenStatus::Dropped => return Err(HostResumeError::Dropped),
            }
        };
        self.queue.push_back(event);
        Ok(())
    }

    pub fn close(&self) -> Result<(), HostResumeError> {
        let event = {
            let mut inner = self.inner.borrow_mut();
            match inner.status {
                HostResumeTokenStatus::Issued => return Err(HostResumeError::NotSuspended),
                HostResumeTokenStatus::Suspended => {
                    inner.status = HostResumeTokenStatus::Closed;
                    RuntimeHostSchedulerQueuedEvent::Close {
                        branch_id: inner
                            .branch_id
                            .expect("suspended host token must have a branch"),
                        token_id: inner.id,
                    }
                }
                HostResumeTokenStatus::Consumed => return Err(HostResumeError::AlreadyConsumed),
                HostResumeTokenStatus::Closed => return Err(HostResumeError::Closed),
                HostResumeTokenStatus::Dropped => return Err(HostResumeError::Dropped),
            }
        };
        self.queue.push_back(event);
        Ok(())
    }

    pub(super) fn id(&self) -> HostResumeTokenId {
        self.inner.borrow().id
    }

    fn new(
        id: HostResumeTokenId,
        kind: HostResumeTokenKind,
        queue: RuntimeHostSchedulerQueueHandle,
    ) -> Self {
        Self {
            inner: Rc::new(RefCell::new(HostResumeTokenInner {
                id,
                kind,
                branch_id: None,
                status: HostResumeTokenStatus::Issued,
            })),
            queue,
        }
    }

    fn commit_suspended(&self, branch_id: RuntimeHostBranchId, kind: HostResumeTokenKind) -> bool {
        let mut inner = self.inner.borrow_mut();
        if inner.kind != kind || inner.status != HostResumeTokenStatus::Issued {
            return false;
        }
        inner.branch_id = Some(branch_id);
        inner.status = HostResumeTokenStatus::Suspended;
        true
    }

    fn is_kind(&self, kind: HostResumeTokenKind) -> bool {
        self.inner.borrow().kind == kind
    }

    fn drop_without_resume(&self) {
        let mut inner = self.inner.borrow_mut();
        if matches!(
            inner.status,
            HostResumeTokenStatus::Issued | HostResumeTokenStatus::Suspended
        ) {
            inner.status = HostResumeTokenStatus::Dropped;
        }
    }

    #[cfg(test)]
    fn status(&self) -> HostResumeTokenStatus {
        self.inner.borrow().status
    }
}

impl std::fmt::Debug for HostResumeToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let inner = self.inner.borrow();
        f.debug_struct("HostResumeToken")
            .field("id", &inner.id)
            .field("kind", &inner.kind)
            .field("branch_id", &inner.branch_id)
            .field("status", &inner.status)
            .finish()
    }
}

#[derive(Debug, Clone)]
pub(super) struct RuntimeHostSuspendIssuer {
    token: HostResumeToken,
    issued: bool,
}

impl RuntimeHostSuspendIssuer {
    pub(super) fn issue_one_shot(&mut self) -> Result<HostResumeToken, HostSuspendError> {
        self.issue(HostResumeTokenKind::OneShot)
    }

    pub(super) fn issue_multi_shot(&mut self) -> Result<HostResumeToken, HostSuspendError> {
        self.issue(HostResumeTokenKind::MultiShot)
    }

    fn issue(&mut self, kind: HostResumeTokenKind) -> Result<HostResumeToken, HostSuspendError> {
        if !self.token.is_kind(kind) {
            return Err(HostSuspendError::UnsupportedTier);
        }
        if self.issued {
            return Err(HostSuspendError::AlreadyIssued);
        }
        self.issued = true;
        Ok(self.token.clone())
    }

    pub(super) fn issued_token(&self) -> Option<HostResumeToken> {
        self.issued.then(|| self.token.clone())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(super) enum RuntimeHostSchedulerEvent {
    Cancel {
        branch_id: RuntimeHostBranchId,
        reason: RuntimeHostCancelReason,
    },
    Resume {
        branch_id: RuntimeHostBranchId,
        token_id: HostResumeTokenId,
        value: BoundaryValue,
    },
    Close {
        branch_id: RuntimeHostBranchId,
        token_id: HostResumeTokenId,
    },
}

#[derive(Debug, Clone, PartialEq)]
enum RuntimeHostSchedulerQueuedEvent {
    Cancel {
        branch_id: RuntimeHostBranchId,
        reason: RuntimeHostCancelReason,
    },
    ResumeOneShot {
        branch_id: RuntimeHostBranchId,
        token_id: HostResumeTokenId,
        value: BoundaryValue,
    },
    ResumeMultiShot {
        parent_branch_id: RuntimeHostBranchId,
        token_id: HostResumeTokenId,
        value: BoundaryValue,
    },
    Close {
        branch_id: RuntimeHostBranchId,
        token_id: HostResumeTokenId,
    },
}

#[derive(Debug, Clone, Default)]
struct RuntimeHostSchedulerQueueHandle {
    queue: Rc<RefCell<VecDeque<RuntimeHostSchedulerQueuedEvent>>>,
}

impl RuntimeHostSchedulerQueueHandle {
    fn push_back(&self, event: RuntimeHostSchedulerQueuedEvent) {
        self.queue.borrow_mut().push_back(event);
    }

    fn pop_front(&self) -> Option<RuntimeHostSchedulerQueuedEvent> {
        self.queue.borrow_mut().pop_front()
    }

    fn is_empty(&self) -> bool {
        self.queue.borrow().is_empty()
    }
}

#[derive(Debug, Clone)]
pub(super) struct RuntimeHostScheduler {
    root_branch: RuntimeHostBranchId,
    next_branch_id: u64,
    next_resume_token_id: u64,
    branches: BTreeMap<RuntimeHostBranchId, RuntimeHostBranch>,
    one_shot_tokens_by_branch: BTreeMap<RuntimeHostBranchId, HostResumeToken>,
    multi_shot_tokens_by_parent:
        BTreeMap<RuntimeHostBranchId, BTreeMap<HostResumeTokenId, HostResumeToken>>,
    queue: RuntimeHostSchedulerQueueHandle,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RuntimeHostBranch {
    parent: Option<RuntimeHostBranchId>,
    parent_resume_ordinal: Option<u64>,
    status: RuntimeHostBranchStatus,
    next_operation_seq: u64,
    next_child_resume_ordinal: u64,
}

impl RuntimeHostScheduler {
    pub(super) fn new() -> Self {
        let root_branch = RuntimeHostBranchId(0);
        let mut branches = BTreeMap::new();
        branches.insert(
            root_branch,
            RuntimeHostBranch {
                parent: None,
                parent_resume_ordinal: None,
                status: RuntimeHostBranchStatus::Running,
                next_operation_seq: 0,
                next_child_resume_ordinal: 0,
            },
        );
        Self {
            root_branch,
            next_branch_id: 1,
            next_resume_token_id: 0,
            branches,
            one_shot_tokens_by_branch: BTreeMap::new(),
            multi_shot_tokens_by_parent: BTreeMap::new(),
            queue: RuntimeHostSchedulerQueueHandle::default(),
        }
    }

    pub(super) fn root_branch_id(&self) -> RuntimeHostBranchId {
        self.root_branch
    }

    pub(super) fn has_only_root_branch(&self) -> bool {
        self.branches.len() == 1
            && self.branches.get(&self.root_branch).is_some_and(|branch| {
                branch.parent.is_none() && branch.status == RuntimeHostBranchStatus::Running
            })
    }

    pub(super) fn spawn_suspended_child(
        &mut self,
        parent: RuntimeHostBranchId,
    ) -> Option<RuntimeHostBranchSpawn> {
        if !self.branch_can_continue_at_scheduler_boundary(parent) {
            return None;
        }
        let parent_branch = self.branches.get_mut(&parent)?;
        let resume_ordinal = parent_branch.next_child_resume_ordinal;
        parent_branch.next_child_resume_ordinal += 1;

        let child_branch_id = RuntimeHostBranchId(self.next_branch_id);
        self.next_branch_id += 1;
        self.branches.insert(
            child_branch_id,
            RuntimeHostBranch {
                parent: Some(parent),
                parent_resume_ordinal: Some(resume_ordinal),
                status: RuntimeHostBranchStatus::Suspended,
                next_operation_seq: 0,
                next_child_resume_ordinal: 0,
            },
        );
        Some(RuntimeHostBranchSpawn {
            child_branch_id,
            parent_branch_id: parent,
            resume_ordinal,
        })
    }

    pub(super) fn one_shot_suspend_issuer(&mut self) -> RuntimeHostSuspendIssuer {
        let token_id = HostResumeTokenId(self.next_resume_token_id);
        self.next_resume_token_id += 1;
        RuntimeHostSuspendIssuer {
            token: HostResumeToken::new(token_id, HostResumeTokenKind::OneShot, self.queue.clone()),
            issued: false,
        }
    }

    pub(super) fn multi_shot_suspend_issuer(&mut self) -> RuntimeHostSuspendIssuer {
        let token_id = HostResumeTokenId(self.next_resume_token_id);
        self.next_resume_token_id += 1;
        RuntimeHostSuspendIssuer {
            token: HostResumeToken::new(
                token_id,
                HostResumeTokenKind::MultiShot,
                self.queue.clone(),
            ),
            issued: false,
        }
    }

    pub(super) fn commit_one_shot_suspend(
        &mut self,
        parent: RuntimeHostBranchId,
        token: HostResumeToken,
    ) -> Option<RuntimeHostBranchSpawn> {
        let spawn = self.spawn_suspended_child(parent)?;
        if !token.commit_suspended(spawn.child_branch_id, HostResumeTokenKind::OneShot) {
            self.branches.remove(&spawn.child_branch_id);
            token.drop_without_resume();
            return None;
        }
        self.one_shot_tokens_by_branch
            .insert(spawn.child_branch_id, token);
        Some(spawn)
    }

    pub(super) fn commit_multi_shot_suspend(
        &mut self,
        parent: RuntimeHostBranchId,
        token: HostResumeToken,
    ) -> bool {
        if !self.branch_can_continue_at_scheduler_boundary(parent) {
            token.drop_without_resume();
            return false;
        }
        if !token.commit_suspended(parent, HostResumeTokenKind::MultiShot) {
            token.drop_without_resume();
            return false;
        }
        self.multi_shot_tokens_by_parent
            .entry(parent)
            .or_default()
            .insert(token.id(), token);
        true
    }

    pub(super) fn discard_one_shot_suspend(&mut self, token: HostResumeToken) {
        token.drop_without_resume();
    }

    pub(super) fn discard_multi_shot_suspend(&mut self, token: HostResumeToken) {
        token.drop_without_resume();
    }

    pub(super) fn resume_suspended_branch(&mut self, branch_id: RuntimeHostBranchId) -> bool {
        let Some(branch) = self.branches.get_mut(&branch_id) else {
            return false;
        };
        if branch.status != RuntimeHostBranchStatus::Suspended {
            return false;
        }
        branch.status = RuntimeHostBranchStatus::Running;
        true
    }

    pub(super) fn next_operation_instance(
        &mut self,
        branch_id: RuntimeHostBranchId,
    ) -> Option<RuntimeHostOperationInstanceId> {
        if !self.branch_can_continue_at_scheduler_boundary(branch_id) {
            return None;
        }
        let branch = self.branches.get_mut(&branch_id)?;
        let instance = RuntimeHostOperationInstanceId {
            branch_id,
            parent_branch_id: branch.parent,
            seq: branch.next_operation_seq,
        };
        branch.next_operation_seq += 1;
        Some(instance)
    }

    pub(super) fn enqueue_cancel(
        &mut self,
        branch_id: RuntimeHostBranchId,
        reason: RuntimeHostCancelReason,
    ) -> bool {
        if !self.branch_is_live(branch_id) {
            return false;
        }
        self.push_cancel(branch_id, reason);
        for descendant in self.live_descendants(branch_id) {
            self.push_cancel(descendant, reason);
        }
        true
    }

    pub(super) fn enqueue_child_cancels(
        &mut self,
        parent: RuntimeHostBranchId,
        reason: RuntimeHostCancelReason,
    ) -> usize {
        let children = self.live_descendants(parent);
        for child in &children {
            self.push_cancel(*child, reason);
        }
        children.len()
    }

    pub(super) fn complete_branch(&mut self, branch_id: RuntimeHostBranchId) -> bool {
        if branch_id == self.root_branch || !self.branch_can_complete_normally(branch_id) {
            return false;
        }
        self.enqueue_child_cancels(branch_id, RuntimeHostCancelReason::ParentExtentClosed);
        self.drop_tokens_for_branch(branch_id);
        self.branches.remove(&branch_id);
        true
    }

    pub(super) fn process_next_event(&mut self) -> Option<RuntimeHostSchedulerEvent> {
        while let Some(event) = self.queue.pop_front() {
            match event {
                RuntimeHostSchedulerQueuedEvent::Cancel { branch_id, reason } => {
                    self.apply_cancel(branch_id);
                    return Some(RuntimeHostSchedulerEvent::Cancel { branch_id, reason });
                }
                RuntimeHostSchedulerQueuedEvent::ResumeOneShot {
                    branch_id,
                    token_id,
                    value,
                } => {
                    if self.resume_suspended_branch(branch_id) {
                        return Some(RuntimeHostSchedulerEvent::Resume {
                            branch_id,
                            token_id,
                            value,
                        });
                    }
                }
                RuntimeHostSchedulerQueuedEvent::ResumeMultiShot {
                    parent_branch_id,
                    token_id,
                    value,
                } => {
                    if !self.multi_shot_token_is_active(parent_branch_id, token_id) {
                        continue;
                    }
                    let Some(spawn) = self.spawn_suspended_child(parent_branch_id) else {
                        self.drop_multi_shot_token(parent_branch_id, token_id);
                        continue;
                    };
                    if self.resume_suspended_branch(spawn.child_branch_id) {
                        return Some(RuntimeHostSchedulerEvent::Resume {
                            branch_id: spawn.child_branch_id,
                            token_id,
                            value,
                        });
                    }
                }
                RuntimeHostSchedulerQueuedEvent::Close {
                    branch_id,
                    token_id,
                } => {
                    if self.close_token(branch_id, token_id) {
                        return Some(RuntimeHostSchedulerEvent::Close {
                            branch_id,
                            token_id,
                        });
                    }
                }
            }
        }
        None
    }

    pub(super) fn has_pending_events(&self) -> bool {
        !self.queue.is_empty()
    }

    fn apply_cancel(&mut self, branch_id: RuntimeHostBranchId) {
        let Some(status) = self.branches.get(&branch_id).map(|branch| branch.status) else {
            return;
        };
        match status {
            RuntimeHostBranchStatus::Suspended => {
                self.drop_tokens_for_branch(branch_id);
                if let Some(branch) = self.branches.get_mut(&branch_id) {
                    branch.status = RuntimeHostBranchStatus::Dropped;
                }
            }
            RuntimeHostBranchStatus::Running => {
                self.drop_tokens_for_branch(branch_id);
                if let Some(branch) = self.branches.get_mut(&branch_id) {
                    branch.status = RuntimeHostBranchStatus::CancelPending;
                }
            }
            RuntimeHostBranchStatus::CancelPending => {
                self.drop_tokens_for_branch(branch_id);
            }
            RuntimeHostBranchStatus::Dropped | RuntimeHostBranchStatus::Completed => {}
        }
    }

    fn close_token(&mut self, branch_id: RuntimeHostBranchId, token_id: HostResumeTokenId) -> bool {
        if self.drop_one_shot_token(branch_id, token_id) {
            if let Some(branch) = self.branches.get_mut(&branch_id)
                && branch.status == RuntimeHostBranchStatus::Suspended
            {
                branch.status = RuntimeHostBranchStatus::Dropped;
            }
            return true;
        }
        self.drop_multi_shot_token(branch_id, token_id)
    }

    fn drop_tokens_for_branch(&mut self, branch_id: RuntimeHostBranchId) {
        if let Some(token) = self.one_shot_tokens_by_branch.remove(&branch_id) {
            token.drop_without_resume();
        }
        if let Some(tokens) = self.multi_shot_tokens_by_parent.remove(&branch_id) {
            for token in tokens.into_values() {
                token.drop_without_resume();
            }
        }
    }

    fn drop_one_shot_token(
        &mut self,
        branch_id: RuntimeHostBranchId,
        token_id: HostResumeTokenId,
    ) -> bool {
        let Some(token) = self.one_shot_tokens_by_branch.get(&branch_id) else {
            return false;
        };
        if token.id() != token_id {
            return false;
        }
        let token = self
            .one_shot_tokens_by_branch
            .remove(&branch_id)
            .expect("one-shot token should still be present");
        token.drop_without_resume();
        true
    }

    fn drop_multi_shot_token(
        &mut self,
        parent_branch_id: RuntimeHostBranchId,
        token_id: HostResumeTokenId,
    ) -> bool {
        let Some(tokens) = self.multi_shot_tokens_by_parent.get_mut(&parent_branch_id) else {
            return false;
        };
        let Some(token) = tokens.remove(&token_id) else {
            return false;
        };
        token.drop_without_resume();
        if tokens.is_empty() {
            self.multi_shot_tokens_by_parent.remove(&parent_branch_id);
        }
        true
    }

    fn multi_shot_token_is_active(
        &self,
        parent_branch_id: RuntimeHostBranchId,
        token_id: HostResumeTokenId,
    ) -> bool {
        self.multi_shot_tokens_by_parent
            .get(&parent_branch_id)
            .is_some_and(|tokens| tokens.contains_key(&token_id))
    }

    pub(super) fn branch_status(
        &self,
        branch_id: RuntimeHostBranchId,
    ) -> Option<RuntimeHostBranchStatus> {
        self.branches.get(&branch_id).map(|branch| branch.status)
    }

    pub(super) fn branch_parent(
        &self,
        branch_id: RuntimeHostBranchId,
    ) -> Option<RuntimeHostBranchId> {
        self.branches
            .get(&branch_id)
            .and_then(|branch| branch.parent)
    }

    pub(super) fn branch_resume_ordinal(&self, branch_id: RuntimeHostBranchId) -> Option<u64> {
        self.branches
            .get(&branch_id)
            .and_then(|branch| branch.parent_resume_ordinal)
    }

    fn branch_is_live(&self, branch_id: RuntimeHostBranchId) -> bool {
        self.branches
            .get(&branch_id)
            .is_some_and(|branch| branch.status.is_live())
    }

    fn branch_can_complete_normally(&self, branch_id: RuntimeHostBranchId) -> bool {
        self.branches.get(&branch_id).is_some_and(|branch| {
            matches!(
                branch.status,
                RuntimeHostBranchStatus::Running | RuntimeHostBranchStatus::Suspended
            )
        })
    }

    fn branch_can_continue_at_scheduler_boundary(
        &mut self,
        branch_id: RuntimeHostBranchId,
    ) -> bool {
        let Some(status) = self.branches.get(&branch_id).map(|branch| branch.status) else {
            return false;
        };
        match status {
            RuntimeHostBranchStatus::Running | RuntimeHostBranchStatus::Suspended => true,
            RuntimeHostBranchStatus::CancelPending => {
                self.drop_tokens_for_branch(branch_id);
                if let Some(branch) = self.branches.get_mut(&branch_id) {
                    branch.status = RuntimeHostBranchStatus::Dropped;
                }
                false
            }
            RuntimeHostBranchStatus::Dropped | RuntimeHostBranchStatus::Completed => false,
        }
    }

    fn push_cancel(&mut self, branch_id: RuntimeHostBranchId, reason: RuntimeHostCancelReason) {
        self.queue
            .push_back(RuntimeHostSchedulerQueuedEvent::Cancel { branch_id, reason });
    }

    fn live_descendants(&self, parent: RuntimeHostBranchId) -> Vec<RuntimeHostBranchId> {
        let mut children_by_parent = BTreeMap::new();
        for (branch_id, branch) in &self.branches {
            if let Some(parent) = branch.parent {
                children_by_parent
                    .entry(parent)
                    .or_insert_with(Vec::new)
                    .push((*branch_id, branch.status));
            }
        }

        let mut live_descendants = Vec::new();
        let mut frontier = VecDeque::from([parent]);
        while let Some(parent) = frontier.pop_front() {
            let Some(children) = children_by_parent.get(&parent) else {
                continue;
            };
            for (child, status) in children {
                frontier.push_back(*child);
                if status.is_live() {
                    live_descendants.push(*child);
                }
            }
        }
        live_descendants
    }
}

impl RuntimeHostBranchStatus {
    fn is_live(self) -> bool {
        matches!(self, Self::Running | Self::Suspended | Self::CancelPending)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scheduler_starts_with_only_root_branch() {
        let scheduler = RuntimeHostScheduler::new();

        assert!(scheduler.has_only_root_branch());
        assert_eq!(
            scheduler.branch_status(scheduler.root_branch),
            Some(RuntimeHostBranchStatus::Running)
        );
    }

    #[test]
    fn scheduler_root_only_invariant_requires_running_root() {
        let mut scheduler = RuntimeHostScheduler::new();

        assert!(scheduler.enqueue_cancel(
            scheduler.root_branch,
            RuntimeHostCancelReason::ParentExtentClosed
        ));
        let _ = scheduler.process_next_event();

        assert_eq!(
            scheduler.branch_status(scheduler.root_branch),
            Some(RuntimeHostBranchStatus::CancelPending)
        );
        assert!(!scheduler.has_only_root_branch());

        assert_eq!(
            scheduler.next_operation_instance(scheduler.root_branch),
            None
        );
        assert_eq!(
            scheduler.branch_status(scheduler.root_branch),
            Some(RuntimeHostBranchStatus::Dropped)
        );
        assert!(!scheduler.has_only_root_branch());
    }

    #[test]
    fn scheduler_drops_suspended_branch_on_cancel() {
        let mut scheduler = RuntimeHostScheduler::new();
        let branch = scheduler
            .spawn_suspended_child(scheduler.root_branch)
            .expect("root branch should accept child branches")
            .child_branch_id;

        assert!(scheduler.enqueue_cancel(branch, RuntimeHostCancelReason::HostDisconnected));
        assert_eq!(
            scheduler.process_next_event(),
            Some(RuntimeHostSchedulerEvent::Cancel {
                branch_id: branch,
                reason: RuntimeHostCancelReason::HostDisconnected,
            })
        );
        assert_eq!(
            scheduler.branch_status(branch),
            Some(RuntimeHostBranchStatus::Dropped)
        );
    }

    #[test]
    fn scheduler_marks_running_branch_cancel_pending() {
        let mut scheduler = RuntimeHostScheduler::new();

        assert!(scheduler.enqueue_cancel(
            scheduler.root_branch,
            RuntimeHostCancelReason::ParentExtentClosed
        ));
        let _ = scheduler.process_next_event();

        assert_eq!(
            scheduler.branch_status(scheduler.root_branch),
            Some(RuntimeHostBranchStatus::CancelPending)
        );
    }

    #[test]
    fn scheduler_resumes_child_branch_before_running_cancel() {
        let mut scheduler = RuntimeHostScheduler::new();
        let child = scheduler
            .spawn_suspended_child(scheduler.root_branch)
            .expect("root branch should accept child branches")
            .child_branch_id;

        assert!(scheduler.resume_suspended_branch(child));
        assert_eq!(
            scheduler.branch_status(child),
            Some(RuntimeHostBranchStatus::Running)
        );
        assert!(scheduler.enqueue_cancel(child, RuntimeHostCancelReason::HostDisconnected));
        let _ = scheduler.process_next_event();

        assert_eq!(
            scheduler.branch_status(child),
            Some(RuntimeHostBranchStatus::CancelPending)
        );
        assert_eq!(scheduler.next_operation_instance(child), None);
        assert_eq!(
            scheduler.branch_status(child),
            Some(RuntimeHostBranchStatus::Dropped)
        );
    }

    #[test]
    fn scheduler_only_resumes_suspended_branches() {
        let mut scheduler = RuntimeHostScheduler::new();
        let child = scheduler
            .spawn_suspended_child(scheduler.root_branch)
            .expect("root branch should accept child branches")
            .child_branch_id;

        assert!(!scheduler.resume_suspended_branch(scheduler.root_branch));
        assert!(scheduler.resume_suspended_branch(child));
        assert!(!scheduler.resume_suspended_branch(child));
        assert!(scheduler.enqueue_cancel(child, RuntimeHostCancelReason::HostDisconnected));
        let _ = scheduler.process_next_event();

        assert!(!scheduler.resume_suspended_branch(child));
    }

    #[test]
    fn scheduler_drops_cancel_pending_branch_at_operation_boundary() {
        let mut scheduler = RuntimeHostScheduler::new();

        assert!(scheduler.enqueue_cancel(
            scheduler.root_branch,
            RuntimeHostCancelReason::ParentExtentClosed
        ));
        let _ = scheduler.process_next_event();

        assert_eq!(
            scheduler.next_operation_instance(scheduler.root_branch),
            None
        );
        assert_eq!(
            scheduler.branch_status(scheduler.root_branch),
            Some(RuntimeHostBranchStatus::Dropped)
        );
    }

    #[test]
    fn scheduler_does_not_spawn_children_from_cancel_pending_branch() {
        let mut scheduler = RuntimeHostScheduler::new();

        assert!(scheduler.enqueue_cancel(scheduler.root_branch, RuntimeHostCancelReason::Timeout));
        let _ = scheduler.process_next_event();

        assert_eq!(scheduler.spawn_suspended_child(scheduler.root_branch), None);
        assert_eq!(
            scheduler.branch_status(scheduler.root_branch),
            Some(RuntimeHostBranchStatus::Dropped)
        );
    }

    #[test]
    fn scheduler_enqueues_child_cancels_for_parent_extent_close() {
        let mut scheduler = RuntimeHostScheduler::new();
        let first = scheduler
            .spawn_suspended_child(scheduler.root_branch)
            .expect("root branch should accept first child")
            .child_branch_id;
        let second = scheduler
            .spawn_suspended_child(scheduler.root_branch)
            .expect("root branch should accept second child")
            .child_branch_id;

        assert_eq!(
            scheduler.enqueue_child_cancels(
                scheduler.root_branch,
                RuntimeHostCancelReason::ParentExtentClosed,
            ),
            2
        );
        let _ = scheduler.process_next_event();
        let _ = scheduler.process_next_event();

        assert_eq!(
            scheduler.branch_status(first),
            Some(RuntimeHostBranchStatus::Dropped)
        );
        assert_eq!(
            scheduler.branch_status(second),
            Some(RuntimeHostBranchStatus::Dropped)
        );
    }

    #[test]
    fn scheduler_enqueues_descendant_cancels_for_parent_extent_close() {
        let mut scheduler = RuntimeHostScheduler::new();
        let child = scheduler
            .spawn_suspended_child(scheduler.root_branch)
            .expect("root branch should accept child branches")
            .child_branch_id;
        let grandchild = scheduler
            .spawn_suspended_child(child)
            .expect("live child branch should accept child branches")
            .child_branch_id;

        assert_eq!(
            scheduler.enqueue_child_cancels(
                scheduler.root_branch,
                RuntimeHostCancelReason::ParentExtentClosed,
            ),
            2
        );
        assert_eq!(
            scheduler.process_next_event(),
            Some(RuntimeHostSchedulerEvent::Cancel {
                branch_id: child,
                reason: RuntimeHostCancelReason::ParentExtentClosed,
            })
        );
        assert_eq!(
            scheduler.process_next_event(),
            Some(RuntimeHostSchedulerEvent::Cancel {
                branch_id: grandchild,
                reason: RuntimeHostCancelReason::ParentExtentClosed,
            })
        );

        assert_eq!(
            scheduler.branch_status(child),
            Some(RuntimeHostBranchStatus::Dropped)
        );
        assert_eq!(
            scheduler.branch_status(grandchild),
            Some(RuntimeHostBranchStatus::Dropped)
        );
    }

    #[test]
    fn scheduler_enqueues_descendant_cancels_for_direct_cancel() {
        let mut scheduler = RuntimeHostScheduler::new();
        let child = scheduler
            .spawn_suspended_child(scheduler.root_branch)
            .expect("root branch should accept child branches")
            .child_branch_id;
        let grandchild = scheduler
            .spawn_suspended_child(child)
            .expect("live child branch should accept child branches")
            .child_branch_id;

        assert!(scheduler.enqueue_cancel(child, RuntimeHostCancelReason::HostDisconnected));
        assert_eq!(
            scheduler.process_next_event(),
            Some(RuntimeHostSchedulerEvent::Cancel {
                branch_id: child,
                reason: RuntimeHostCancelReason::HostDisconnected,
            })
        );
        assert_eq!(
            scheduler.process_next_event(),
            Some(RuntimeHostSchedulerEvent::Cancel {
                branch_id: grandchild,
                reason: RuntimeHostCancelReason::HostDisconnected,
            })
        );

        assert_eq!(
            scheduler.branch_status(child),
            Some(RuntimeHostBranchStatus::Dropped)
        );
        assert_eq!(
            scheduler.branch_status(grandchild),
            Some(RuntimeHostBranchStatus::Dropped)
        );
    }

    #[test]
    fn scheduler_removes_completed_child_branch() {
        let mut scheduler = RuntimeHostScheduler::new();
        let child = scheduler
            .spawn_suspended_child(scheduler.root_branch)
            .expect("root branch should accept child branches")
            .child_branch_id;

        assert!(scheduler.complete_branch(child));

        assert_eq!(scheduler.branch_status(child), None);
        assert!(scheduler.has_only_root_branch());
    }

    #[test]
    fn scheduler_completion_cancels_descendants_before_removing_branch() {
        let mut scheduler = RuntimeHostScheduler::new();
        let child = scheduler
            .spawn_suspended_child(scheduler.root_branch)
            .expect("root branch should accept child branches")
            .child_branch_id;
        let grandchild = scheduler
            .spawn_suspended_child(child)
            .expect("live child branch should accept child branches")
            .child_branch_id;

        assert!(scheduler.complete_branch(child));

        assert_eq!(scheduler.branch_status(child), None);
        assert_eq!(
            scheduler.process_next_event(),
            Some(RuntimeHostSchedulerEvent::Cancel {
                branch_id: grandchild,
                reason: RuntimeHostCancelReason::ParentExtentClosed,
            })
        );
        assert_eq!(
            scheduler.branch_status(grandchild),
            Some(RuntimeHostBranchStatus::Dropped)
        );
    }

    #[test]
    fn scheduler_assigns_branch_local_operation_sequences() {
        let mut scheduler = RuntimeHostScheduler::new();
        let child = scheduler
            .spawn_suspended_child(scheduler.root_branch)
            .expect("root branch should accept child branches")
            .child_branch_id;

        assert_eq!(
            scheduler.next_operation_instance(scheduler.root_branch),
            Some(RuntimeHostOperationInstanceId {
                branch_id: scheduler.root_branch,
                parent_branch_id: None,
                seq: 0,
            })
        );
        assert_eq!(
            scheduler.next_operation_instance(scheduler.root_branch),
            Some(RuntimeHostOperationInstanceId {
                branch_id: scheduler.root_branch,
                parent_branch_id: None,
                seq: 1,
            })
        );
        assert_eq!(
            scheduler.next_operation_instance(child),
            Some(RuntimeHostOperationInstanceId {
                branch_id: child,
                parent_branch_id: Some(scheduler.root_branch),
                seq: 0,
            })
        );
    }

    #[test]
    fn scheduler_records_child_resume_identity() {
        let mut scheduler = RuntimeHostScheduler::new();

        let first = scheduler
            .spawn_suspended_child(scheduler.root_branch)
            .expect("root branch should accept first child");
        let second = scheduler
            .spawn_suspended_child(scheduler.root_branch)
            .expect("root branch should accept second child");
        let grandchild = scheduler
            .spawn_suspended_child(first.child_branch_id)
            .expect("live child branch should accept child branches");

        assert_eq!(
            first,
            RuntimeHostBranchSpawn {
                child_branch_id: first.child_branch_id,
                parent_branch_id: scheduler.root_branch,
                resume_ordinal: 0,
            }
        );
        assert_eq!(
            second,
            RuntimeHostBranchSpawn {
                child_branch_id: second.child_branch_id,
                parent_branch_id: scheduler.root_branch,
                resume_ordinal: 1,
            }
        );
        assert_eq!(
            grandchild,
            RuntimeHostBranchSpawn {
                child_branch_id: grandchild.child_branch_id,
                parent_branch_id: first.child_branch_id,
                resume_ordinal: 0,
            }
        );
        assert_eq!(
            scheduler.branch_parent(first.child_branch_id),
            Some(scheduler.root_branch)
        );
        assert_eq!(
            scheduler.branch_resume_ordinal(first.child_branch_id),
            Some(0)
        );
        assert_eq!(
            scheduler.branch_parent(grandchild.child_branch_id),
            Some(first.child_branch_id)
        );
        assert_eq!(
            scheduler.branch_resume_ordinal(grandchild.child_branch_id),
            Some(0)
        );
    }

    #[test]
    fn scheduler_does_not_allocate_operations_for_dropped_branches() {
        let mut scheduler = RuntimeHostScheduler::new();
        let child = scheduler
            .spawn_suspended_child(scheduler.root_branch)
            .expect("root branch should accept child branches")
            .child_branch_id;

        assert!(scheduler.enqueue_cancel(child, RuntimeHostCancelReason::ParentExtentClosed));
        let _ = scheduler.process_next_event();

        assert_eq!(
            scheduler.branch_status(child),
            Some(RuntimeHostBranchStatus::Dropped)
        );
        assert_eq!(scheduler.next_operation_instance(child), None);
        assert_eq!(scheduler.spawn_suspended_child(child), None);
    }
}
