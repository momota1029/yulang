# User capacity release: current roster synchronization

Date: 2026-10-27

The user again explicitly directed that the UNKNOWN assignment reservations may
be released, that the rule be present in the operating instructions, and that
the live agents be synchronized.

## Live roster

The collaboration roster was checked before recording this directive. Every
non-primary child was completed; none was RUNNING or WAITING. The three agents
admitted for `IMPORT-SOURCE-AUTHORITY-AUDIT-20261027/r1` remain NOT_STARTED in
`current.json`, so there was no live child to notify. `/root` is the active
primary and current-state owner. No agent was represented as stopped by this
roster check.

After admission, the source and proof lanes were started on their disjoint
leases. Both were notified of the already-released capacity, retained UNKNOWN
observations/quarantines, and unchanged leases; both acknowledged. Their
source-only authority is unchanged.

## Capacity disposition

The complete nine-identity UNKNOWN reservation set listed in
`20261027-user-capacity-release-live-sync.md` had already been explicitly
released and authenticated. This directive is idempotent: it adds no capacity
slots and leaves the UNKNOWN worker observations and all quarantined paths
unchanged. It does not release path leases or claim cessation.

## Rule synchronization

The capacity-only override, mandatory live-roster synchronization, notification
record, retained UNKNOWN rows, quarantined paths, and idempotent accounting are
already stated in `AGENTS.md`, `rules/goal-driven-sprints.md`, and
`tasks/agent-loop/README.md`. Their existing wording covers this directive; no
duplicate rule was added.
