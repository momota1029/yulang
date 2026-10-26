# WHOLE-FRESH-SCOPE-20261026 / r2

Status: producer checked; independent review pending. Original full hygiene OPEN.
Owner: `/root`, sole author and sole Git writer for this lane.
Baseline: `45d307a0aa01722b5aac289b07d71953630abca7`, branch `yulang3`.

## Lease and execution budget

Exact owned outputs:

- `notes/theory/lean/YulangClosure/NativeFreshScopeTransport.lean`
- `notes/theory/lean/AuditFreshScopeTransport.lean`
- `notes/theory/2026-10-26-native-fresh-scope-transport.md`
- this handoff

Scratch: `/workspace/scratch/e3678bef96db/fresh-scope-r2`.
Root owns the existing project cache; all three workers have isolated caches.
One Lean process, `LEAN_NUM_THREADS=1`, `-j1 -M1024`; at most 24 focused checks,
120 seconds per check. No compiler, semantics, toolchain, package, shared
closure-root or current-loop-state edit. The baseline and all foreign leases
remain preserved. Raw logs/build outputs stay outside tracked sources.

## Original goal and actual advance

The requested theorem is full original Yulang soundness/hygiene/principality/
termination. This lane closes the actual fresh-name map construction used by
`NativeScopeTransformer.evaluate_rename`, rather than assuming the needed
injection or interpreting private-support collision checking as enough.

`candidate_source.rs::ScopeInventory::fresh` enumerates copied scope/input
keys, appends an ID at the current respective inventory length and inserts
that old key's image. `candidate_scheme.rs` applies lookup-or-identity to both
the transformer and its demand. The Lean model constructs exactly this
successful ID projection, including overwrite if a key is repeated.

For a count n and arbitrary copy-key list, the constructed map is injective
on all old IDs below n, leaves untouched keys fixed, and sends copied keys
into the appended ID range. No injectivity, key uniqueness, final safety or
commutation law is assumed. It is explicitly NOT globally injective on Nat.

A proof-only injective extension, constructed by a fresh swap at each insert,
agrees with the native map on the complete old inventory. The existing scope
algebra then proves actual fresh-map evaluation commutation for valid old
transformers and incoming states, including external protections. Output
validity is constructed for another copy with the enlarged inventories.

The support-validity premises are explicit. This does not prove that all
original source routes generate valid native inventories, does not establish
owner/receiver/receipt authority, does not identify fallible Rust execution
with Lean reduction, and does not use 4096/65536 availability caps as a
language boundary or a termination argument.

## Validation

Pinned executable:
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
The installed Lean is 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`),
Lake `5.0.0-src+eb6cafb`.

Focused `lake build +YulangClosure.NativeFreshScopeTransport` succeeds with
3 jobs; final source build 1.6 seconds and no warning. Four producer checks
so far: two development failures (simplification order, explicit projection
normalization/argument order), then two clean builds. No holes or supplied
law were introduced as repairs. Complete originating-module audit and fresh
independent nonauthor review are required before commit/promotion.

The complete originating-module audit (focused call 5) exited 0, with all
50 theorem constants checked, 50 unique/balanced begin/end blocks and all ten
required roots present. There are no errors/warnings. Axiom sets: 17 empty,
13 only `propext`, 16 `propext, Quot.sound`, and 4 the three standard axioms
`propext, Classical.choice, Quot.sound`. No `sorryAx`, project axiom or
native-evaluation assumption occurs. Complete types and complete axiom lists
are reproducible with the committed audit script.

Frozen SHA-256 values:

| Input/output | SHA-256 |
| --- | --- |
| NativeFreshScopeTransport.lean | `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5` |
| AuditFreshScopeTransport.lean | `44e6618a59bba54411d4f5b9c75bca5458ae364914c410d5bd357315da3d9e80` |
| NativeScopeTransformer.lean | `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6` |
| candidate_source.rs | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| candidate_scheme.rs | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| scratch audit.log | `03e906b6942533267d434e9bb6e04dc589606ca3db964f67af85ba9685a4bf61` |

After checking, the primary fast-forwarded the disjoint concurrent
`ff12ce504` OriginalSourceChecking contribution. None of the mathematical
or configuration inputs of this lane changed. No new default-build coverage
is claimed yet. The proof and audit source are frozen for nonauthor review.
