#![allow(dead_code)]
// This module is wired into the runner before the server suspend path exists.
// The branch/cancel APIs are locked by unit tests now and become live when the
// in-process server driver starts creating suspended host branches.

use std::collections::{BTreeMap, VecDeque};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct RuntimeHostBranchId(u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct RuntimeHostOperationInstanceId {
    branch_id: RuntimeHostBranchId,
    seq: u64,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RuntimeHostSchedulerEvent {
    Cancel {
        branch_id: RuntimeHostBranchId,
        reason: RuntimeHostCancelReason,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct RuntimeHostScheduler {
    root_branch: RuntimeHostBranchId,
    next_branch_id: u64,
    branches: BTreeMap<RuntimeHostBranchId, RuntimeHostBranch>,
    queue: VecDeque<RuntimeHostSchedulerEvent>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RuntimeHostBranch {
    parent: Option<RuntimeHostBranchId>,
    status: RuntimeHostBranchStatus,
    next_operation_seq: u64,
}

impl RuntimeHostScheduler {
    pub(super) fn new() -> Self {
        let root_branch = RuntimeHostBranchId(0);
        let mut branches = BTreeMap::new();
        branches.insert(
            root_branch,
            RuntimeHostBranch {
                parent: None,
                status: RuntimeHostBranchStatus::Running,
                next_operation_seq: 0,
            },
        );
        Self {
            root_branch,
            next_branch_id: 1,
            branches,
            queue: VecDeque::new(),
        }
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
    ) -> Option<RuntimeHostBranchId> {
        if !self.branch_can_continue_at_scheduler_boundary(parent) {
            return None;
        }
        let branch_id = RuntimeHostBranchId(self.next_branch_id);
        self.next_branch_id += 1;
        self.branches.insert(
            branch_id,
            RuntimeHostBranch {
                parent: Some(parent),
                status: RuntimeHostBranchStatus::Suspended,
                next_operation_seq: 0,
            },
        );
        Some(branch_id)
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
        self.branches.remove(&branch_id);
        true
    }

    pub(super) fn process_next_event(&mut self) -> Option<RuntimeHostSchedulerEvent> {
        let event = self.queue.pop_front()?;
        match event {
            RuntimeHostSchedulerEvent::Cancel { branch_id, .. } => {
                if let Some(branch) = self.branches.get_mut(&branch_id) {
                    branch.status = match branch.status {
                        RuntimeHostBranchStatus::Suspended => RuntimeHostBranchStatus::Dropped,
                        RuntimeHostBranchStatus::Running => RuntimeHostBranchStatus::CancelPending,
                        other => other,
                    };
                }
            }
        }
        Some(event)
    }

    pub(super) fn branch_status(
        &self,
        branch_id: RuntimeHostBranchId,
    ) -> Option<RuntimeHostBranchStatus> {
        self.branches.get(&branch_id).map(|branch| branch.status)
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
        let Some(branch) = self.branches.get_mut(&branch_id) else {
            return false;
        };
        match branch.status {
            RuntimeHostBranchStatus::Running | RuntimeHostBranchStatus::Suspended => true,
            RuntimeHostBranchStatus::CancelPending => {
                branch.status = RuntimeHostBranchStatus::Dropped;
                false
            }
            RuntimeHostBranchStatus::Dropped | RuntimeHostBranchStatus::Completed => false,
        }
    }

    fn push_cancel(&mut self, branch_id: RuntimeHostBranchId, reason: RuntimeHostCancelReason) {
        self.queue
            .push_back(RuntimeHostSchedulerEvent::Cancel { branch_id, reason });
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
            .expect("root branch should accept child branches");

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
            .expect("root branch should accept child branches");

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
            .expect("root branch should accept child branches");

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
            .expect("root branch should accept first child");
        let second = scheduler
            .spawn_suspended_child(scheduler.root_branch)
            .expect("root branch should accept second child");

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
            .expect("root branch should accept child branches");
        let grandchild = scheduler
            .spawn_suspended_child(child)
            .expect("live child branch should accept child branches");

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
            .expect("root branch should accept child branches");
        let grandchild = scheduler
            .spawn_suspended_child(child)
            .expect("live child branch should accept child branches");

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
            .expect("root branch should accept child branches");

        assert!(scheduler.complete_branch(child));

        assert_eq!(scheduler.branch_status(child), None);
        assert!(scheduler.has_only_root_branch());
    }

    #[test]
    fn scheduler_completion_cancels_descendants_before_removing_branch() {
        let mut scheduler = RuntimeHostScheduler::new();
        let child = scheduler
            .spawn_suspended_child(scheduler.root_branch)
            .expect("root branch should accept child branches");
        let grandchild = scheduler
            .spawn_suspended_child(child)
            .expect("live child branch should accept child branches");

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
            .expect("root branch should accept child branches");

        assert_eq!(
            scheduler.next_operation_instance(scheduler.root_branch),
            Some(RuntimeHostOperationInstanceId {
                branch_id: scheduler.root_branch,
                seq: 0,
            })
        );
        assert_eq!(
            scheduler.next_operation_instance(scheduler.root_branch),
            Some(RuntimeHostOperationInstanceId {
                branch_id: scheduler.root_branch,
                seq: 1,
            })
        );
        assert_eq!(
            scheduler.next_operation_instance(child),
            Some(RuntimeHostOperationInstanceId {
                branch_id: child,
                seq: 0,
            })
        );
    }

    #[test]
    fn scheduler_does_not_allocate_operations_for_dropped_branches() {
        let mut scheduler = RuntimeHostScheduler::new();
        let child = scheduler
            .spawn_suspended_child(scheduler.root_branch)
            .expect("root branch should accept child branches");

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
