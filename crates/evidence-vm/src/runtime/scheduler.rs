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
        self.branches.len() == 1 && self.branches.contains_key(&self.root_branch)
    }

    pub(super) fn spawn_suspended_child(
        &mut self,
        parent: RuntimeHostBranchId,
    ) -> Option<RuntimeHostBranchId> {
        if !self.branch_is_live(parent) {
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

    pub(super) fn next_operation_instance(
        &mut self,
        branch_id: RuntimeHostBranchId,
    ) -> Option<RuntimeHostOperationInstanceId> {
        let branch = self.branches.get_mut(&branch_id)?;
        if !branch.status.is_live() {
            return None;
        }
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
        self.queue
            .push_back(RuntimeHostSchedulerEvent::Cancel { branch_id, reason });
        true
    }

    pub(super) fn enqueue_child_cancels(
        &mut self,
        parent: RuntimeHostBranchId,
        reason: RuntimeHostCancelReason,
    ) -> usize {
        let children = self
            .branches
            .iter()
            .filter_map(|(branch_id, branch)| {
                (branch.parent == Some(parent) && branch.status.is_live()).then_some(*branch_id)
            })
            .collect::<Vec<_>>();
        for child in &children {
            self.queue.push_back(RuntimeHostSchedulerEvent::Cancel {
                branch_id: *child,
                reason,
            });
        }
        children.len()
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
}
