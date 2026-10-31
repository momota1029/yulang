# R97 admission — Rust effect-permission observer repair

Sprint contract: `tasks/agent-loop/sprints/effect-permission-rust-observer-repair-20261101-r97.md`.
The exact contract bytes are the admitted authority for the diagnostic-only
repair and verification envelope.

Dispatcher: `/root/r85_boundary_dispatch`, final recommendation accepted after
the user steered the active Rust/Lean goal to analyze and push Rust work. The
dispatcher found a safe diagnostic-only repair: restore the protected
nonrecursive test and eliminate constructor-ID assumptions on sibling paths.
The original existing-target-only verification restriction was amended after
resource inspection: `/dev/shm` is an existing 16 GiB tmpfs with 16 GiB free,
host memory reports 26 GiB available, and swap was unused. The branch filesystem
has no usable yu-solver target (`tools/target` is empty). No new persistent
target, cache, worktree, or project copy is authorized. A temporary tmpfs target
is conditional on actual write/execute access and any required sandbox review;
there is no persistent-storage fallback.

The currently changed runtime files remain quarantined and outside this packet.
No solver semantics, source scope, A/B quantifiers, expected outputs, or
production permissions change. The effect hygiene, source/native, parent Lean,
principality, termination, and production gates remain open.
