# R182 activation — App syntax and inference owner map

State: admitted by Luna; worker launches require fresh acknowledgements before
their assignment rows become RUNNING. Baseline: `yulang3` at
`e673a698b2bbfd8e9a9890fc03a87b6b069c3d3e`.

User objective: establish Yulang type/effect inference soundness against its
original source typing rules. The target is not Rust implementation correctness.
Parent: original `SourceProblem.InferenceSoundness`, preserving all forms,
quantifiers, one satisfying assignment `a`, and one shared `sameScoped`
witness.

Dispatcher recommendation at the R181 boundary: authenticate the exact
`OriginalSourceSyntax` owner and inspect the named inference-model declarations
in a fixed set of Lean modules. Produce the syntax-to-instance-to-source-owned
image/readback map and stop at the first unpinned owner. No equation or semantic
alternative is adopted.

Contract: `tasks/agent-loop/sprints/source-syntax-owner-r182.md`, SHA-256
`c1ef27937a773c09cb0394dca29684f4def469322def8d864c1a3f38af4ca304`.

Frozen dependencies: 10 exact rows in the R182 contract. Luna recomputed all
10 listed hashes before opening the previously unpinned syntax owner; every
digest matched. Exact output paths are absent at admission time:

- `tasks/agent-loop/inbox/app-syntax-owner-r182-source.md`
- `tasks/agent-loop/inbox/app-inference-instance-r182-proof.md`

The first lane has sole write lease for the syntax output; the second has sole
write lease for the inference-model output. Each receives at most 450 seconds,
read-only source authority, no recursive imports, no Lean/Rust execution or
edits, and a hard stop at any newly referenced owner. Fresh review is assigned
only after both outputs freeze, with a 300-second budget. Unknown workers and
quarantined leases remain untouched. Parent remains OPEN.
