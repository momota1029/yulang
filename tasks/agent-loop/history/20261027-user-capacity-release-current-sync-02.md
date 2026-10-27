# User-directed capacity release reaffirmation and live-agent sync

Date: 2026-10-27
Authority: explicit current-user instruction to release the UNKNOWN reservations, add the rule, and synchronize active agents.

## Live-roster synchronization

At the directive, `/root/provider_source_proof` was the only RUNNING non-primary agent. It was notified that all non-primary UNKNOWN assignment reservations are released idempotently, while UNKNOWN observations and quarantined historical paths remain; its active proof lease and sole-verifier assignment are unchanged. The agent acknowledged this disposition. All other listed children were terminal.

## Capacity disposition

The user targeted the UNKNOWN assignment reservations represented in `current.json`. All nine reservations were already released by the earlier user-directed receipt `tasks/agent-loop/history/20261027-user-capacity-release.md` (SHA-256 `7d30faa71449af50c50539307b3a11d062735b64d522eac93656467ff94968a8`). This reaffirmation is idempotent: no additional capacity is counted. Worker observations remain UNKNOWN and historical path quarantines remain in force. No cessation or path-lease release is claimed.

## Rule

The explicit live-user release rule already existed in `AGENTS.md`, `rules/goal-driven-sprints.md`, and `tasks/agent-loop/README.md`; it now states directly that an explicit release overrides stale reservation accounting in `current.json`, while changing capacity accounting only.
