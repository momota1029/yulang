Independent read-only review: 631f0fdc, first five modules.
No major scope mismatch. Missing body is vacuous semantically but rejected by Ready/check.
run_step assumes Ready; initial progress also assumes nonempty facts. Fixed-table settle/Acc
need not wait for validation. Actual requests are membership-equivalent, not list-equal.
EqualOutputs indices are fixed-schema positions; changing/reordering a table does not yet
preserve key meaning. Legacy history and current versioned whole-source connection remain distinct.
No independent rebuild. Reviewer checked code unchanged from the named commit.
