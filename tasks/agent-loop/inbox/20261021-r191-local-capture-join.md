# R191 result — local Capture/Replay source join audit

Status: RESULT, provisional source/native readback only.
Contract SHA-256: `f880b1c46580e020eca0bea3d830569cdf50b5e49392ed38d202e3e5a3565121`.
Baseline HEAD: `0ed00cea392d7f20c6f54f7ed2dc72415532a65e`.
Readback: `notes/theory/2026-10-21-r191-local-capture-join.md`.

The actual local bridge and relay calls, resolved local identities, route
occurrences, direct source relation, both Replay inputs, and local Capture maps
were read from the existing current-worktree observations. The module-only
`source_provider_observation` rejected local callees. The lower-level join is
enough to reconstruct this candidate run but not a complete proof receipt:
there is no exposed Replay-child completion receipt, and Capture snapshots
retain nonzero coverage gaps. The candidate missing-suffix interpretation is
still unverified against every emitted native fiber.

Disposable readback under `target/r191-readback/` was removed after hashing.
Checks: custom offline `cargo run` completed; `python3 tools/agent_sprint.py
check` and `git diff --check` passed. No production source or tests changed.
Original parent/A/B/source-native/production remain OPEN. Primary stopped after
300s; 300s of the 600s cap remain unspent with no carryover. No independent
review was available.
