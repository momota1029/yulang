# R270 current-state compaction: resolved frozen leases

Date: 2026-11-02. This archive preserves the exact records of ten historic
FROZEN paths removed from `current.json` while admitting R270. No worker or
path with UNKNOWN or QUARANTINED status is removed, released or relabeled.
All listed files remain at their existing locations and were hashed as recorded
below. Existing R262 archive receipt
`tasks/agent-loop/history/20261102-r262-overlap-reconciliation.md` remains the
predecessor (`bc0675bbc15362ffd7c38ea4e22bf5105936badff1c9c2617005fbe8b6ec9165`).

| Archived path | Prior state | SHA-256 |
|---|---|---|
| `tasks/agent-loop/history/effect-permission-selected-native-app-20261102-r161-outcome.md` | FROZEN | `52be1ebc2c4ff0022508b6346bc590cf3a272d3fc2952cdf90ac399044a394d0` |
| `tasks/agent-loop/history/effect-permission-native-composite-licensing-20261102-r162-outcome.md` | FROZEN | `48b1d209f1b4fa0e162d3a3ca031feaa13e1e3e5d170b218dad9a009ff4bf5f9` |
| `tasks/agent-loop/inbox/effect-permission-formal-prestate-r169-source.md` | FROZEN | `83b73f52a0b4526d51c8ea03683788accb8f2c48a2b58a74eb01c8c3fcf48eea` |
| `tasks/agent-loop/history/effect-permission-formal-prestate-r169-outcome.md` | FROZEN | `d5ee5b9c86af85bd72982ebba863de2a516c5f318e186107860c6f6df2916559` |
| `tasks/agent-loop/history/20261102-primary-read-boundary-incident-machine.md` | FROZEN | `2ec2af923ae029e68592b5a1167b78a951627127b825cd358e30f2a14b234f36` |
| `notes/theory/2026-11-01-abstract-inference-model-r199.md` | FROZEN | `33d0cd52fbbf07d7916804f8b8961c102b53cc1cf5e9260ac15d83de9f295aa0` |
| `tasks/agent-loop/inbox/abstract-source-inference-model-r209.md` | FROZEN | `c6edf5e4490511b86837391dec73e16ca35737c2d90f5b95eb4a1d390ba0711a` |
| `tasks/agent-loop/history/20261102-resolved-lease-archive-r210-r212.md` | FROZEN | `0890c95e1a3c88b628bb4b5e1c787fabc207963770eb6773981c6998c2420703` |
| `tasks/agent-loop/history/20261102-fixed-inference-model-r213-outcome.md` | FROZEN | `5c4ada6c740926181d42251178326596bc10f95e6b05a340ab28417b48f6d725` |
| `tasks/agent-loop/history/20261102-r269-r3-admission.md` | FROZEN | `b1aa0e8d029171d9da4c24886161c41f13ab7ae5dca74456e6daac7c5b5887ed` |

These frozen records have durable content hashes and remain available for
lookup; the current active lease table retains the R270 packet, R269 reviewed
dependencies and every unresolved, held or quarantined path. This action is
state compaction only and changes no semantic, source, proof or production
authority.
