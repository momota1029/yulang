# R129 — admission transport kernel validation

Status: ADMITTED. Parent objective remains the original Yulang source
preservation/soundness and effect-hygiene goal. This packet validates existing
proof candidates only; it changes no source semantics, proof statement, or Rust
implementation.

## Goal and exact inputs

Obtain one reproducible Lean kernel result for the 15 R105 logical-owner
declarations, 11 R112 scoped-admission declarations, and 10 R114
admission-transport declarations. Preserve each authored declaration body,
namespace, section, option, and audit command byte-for-byte. The complete
dependency closure and source SHA-256/byte counts are pinned in
`tasks/agent-loop/sprints/effect-permission-admission-kernel-validation-20261102-r129-inputs-r2.json`.
The R114 source/semantic handoff and original parent remain authoritative for
the claims and limits; see R114 outcome and the pinned handoffs in the manifest.

The source closure is 25 Lean modules (1,017,627 bytes) plus Lean standard
imports. Manifest r2 replaces r1's order after a static private-name collision
was found; no source bytes or theorem statements changed. No `.lean` module,
root import, project file, cache, `.olean`, worktree, or local source copy may
be written.

## Construction and review

One `lean_prover` owns only
`tasks/agent-loop/inbox/effect-permission-admission-kernel-validation-r129.md`.
The handoff must specify a dependency-respecting linearization for all 25
modules, the exact in-memory flattening algorithm, byte count and SHA-256,
verified declaration inventory, and any binding/namespace/section/option or
instance-order risk. It must include each module once and retain the existing
fully qualified `#check`/`#print axioms` commands. The ordering must place
`SourceSignatureConstruction` immediately after `OriginalSourceSyntax` and
before `OriginalSourceGeneration`, because the latter introduces private names
under the shared `OriginalSource` namespace. It must also place
`NativeDictionaryDenotation` before `Contracts`; the earlier R105 flattening
failure showed this independent dependency can otherwise change name
resolution. Do not execute Lean or modify any artifact.

A fresh independent `lean_prover` or `compiler_referee` reviews the frozen
handoff, all 25 current source hashes, dependency order, flattening recipe,
target declaration names, and whether flattening preserves the authored
bindings and elaboration environment. No execution occurs unless this review
passes. The reviewer writes no files.

## Primary verification

The flattening supplies one leading `import Std` (which includes `Init`) and
then concatenates each source body in the reviewed order with no separators.
Remove every source module's initial `import` command only; preserve every
remaining byte, including comments, namespace/section/option commands and
existing audit commands. The independent reviewer must decide whether the
resulting shared environment preserves binding and target declaration types.

After review PASS, Luna makes exactly one new invocation using the pinned
Lean 4.35.0 executable with the reviewed bytes supplied directly on stdin:

`lean --stdin -j1 -M1024`

Use one CPU, timeout 120 seconds, process-group RSS cap 1 GiB, and retain the
complete stdout/stderr and exit/resource receipt in memory until recorded in
the primary-owned outcome. No Lake, `.olean`, build, test, cache, retry, or
temporary source/output file is authorized. If the reviewed flattening cannot
be supplied without writing files, stop before execution.

Acceptance requires exit 0; all 36 target theorem declarations have their
actual fully qualified types and complete transitive axiom reports; no target
depends on `sorryAx` or a project axiom; and the output hash/count and resource
receipt match the reviewed input and limits. `propext`, `Classical.choice`, and
`Quot.sound` are the only permitted axioms. Missing output, extra axioms,
dependency errors, binding drift, timeout, RSS overrun, or output capture
failure closes this bounded attempt as failed; no retry in R129.

## Scope boundary

Even a pass establishes only kernel acceptance of these exact declarations in
the reviewed flattened input. It does not establish the missing source-owned
admission/derivation-transport law, Rust-to-Lean correspondence, the original
whole-language theorem, A/B closure, effect hygiene, or production readiness.
The separate R111 Rust compile gate remains unchanged and Cargo remains 0/1.
Dirty Rust files and all quarantined paths remain untouched.

## Resource and ownership

Proof input construction: at most 600 seconds. Independent review: at most 480
seconds. Primary execution and receipt audit: at most 240 seconds. One Lean
call total; Astra 0. Luna owns `current.json`, manifest/admission/outcome,
execution, independent-review assignment, Git staging, commit, and safe push.
Only this packet's contract, manifest, handoff, outcome, and compact current
state may enter its checkpoint. No unrelated dirty or quarantined path may be
staged. No force-push.
