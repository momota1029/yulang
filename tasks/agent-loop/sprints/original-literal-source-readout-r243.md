# Sprint R243 — original literal source readout trace

Status: ADMITTED for one bounded Sol-owned read-only implementation trace.
Parent remains the unchanged `SourceProblem.InferenceSoundness`,
`notes/theory/lean/YulangClosure/Contracts.lean:128–130`; R241/R242 parent
delta is zero. Accepted semantics remain the L1 and canonical-generation
adoptions. This packet grants no Rust implementation or semantic promotion.

## Fixed outcome and method

Trace whether the real source-owned literal payload and occurrence can be
carried through the existing HIR and solver path to the original value/root/
event/readout obligations exposed by R241 and R242. Use a source-indexed
factorization audit: identify the concrete relation linking each input
occurrence to its HIR payload, its solver fact/constraint index, and the
consumer's assignment row; then check whether that relation preserves the
payload and original source coordinates needed by the original carrier.

Inspect only the pinned owners and their direct called/consuming functions:

- `crates/yu-hir/src/module/local_source.rs`
- `crates/yu-solver/src/candidate_source.rs`

Follow the literal branches through `Action::Fact` admission and the existing
result consumer. Include a row for each of unit, bool, int, floatBits, string,
bytes, path and character. For every stage record the actual symbol, source
coordinate/index, carried data and next consumer. Determine whether a reverse
source-indexed lookup can recover the original payload after constraints are
formed, or identify the first exact lost/never-created edge and owning symbol.
Do not infer that typing constraints recover an original literal payload.

Success is a concrete existing constructor/consumer path or an exact source
level obstruction with owner, field and reason. This is source evidence, not a
Lean theorem, Yulang counterexample, original semantic choice, or permission to
change Rust. Preserve the unchanged parent, all source forms, distinct
synthesis/written-target/final-root ports, original root/event/scope/witness,
and contextual effects. No source form may be excluded due to an unimplemented
native branch.

## Sol assignment and exact leases

Registered `researcher`, requested Sol/high, no descendants. Write only:

- `notes/theory/2026-11-02-original-literal-source-readout-r243.md`
- `tasks/agent-loop/inbox/original-literal-source-readout-r243.md`

Frozen read dependencies:

| Path | SHA-256 |
|---|---|
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| R241 literal carrier artifact | `49bbe56ee5525f1a7a5b3db2d5c2b04737468cdaa864c761fd6465e1af914d8a` |
| R242 input-dependence artifact | `b5a5ac8580d71ee15dd595fd2712316451df28a68398a524d558f72a12cee649` |

If either source owner hash differs at execution, stop before citing its
contents and return the mismatch to Luna. Do not read/write the quarantined
runtime paths. No build, test, Cargo, generated cache, scratch file, compiler
edit, Git or external call is authorized.

## Review and resources

Maximum 1,200 active seconds; one Sol/researcher assignment, zero Astra,
zero descendants, zero heavy processes and zero builds/tests. Freeze one
coherent note and one handoff with hashes, exact symbol/line locators, all
eight-form coverage, before/after path, missing edge, falsifier and STOPPED
writing receipt. A fresh `compiler_referee` reviews the frozen trace. Parent
delta remains zero unless the trace itself supplies and justifies an actual
original parent premise; a source map or constraint observation alone cannot.

Stop on a confirmed source-indexed lookup path, a precise missing edge, owner
hash mismatch, budget bound, or user STOP. Any proposed Rust correction or
semantic change returns to Luna before edits. UNKNOWN/quarantined leases remain
unchanged. Luna owns review, current-state synchronization and Git.
