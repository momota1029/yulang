# Independent review: persistent raw-pair rewrite ownership

Reviewer: primary `/root`, not the module author. Date: 2026-10-26.

**Verdict: ACCEPTED for the stated uncancelled successful-publication projection.**
The original whole-source inference termination theorem remains open.

## Source and mathematical review

I inspected the complete new module, the imported dispatch/body characterization,
and the actual `TypedPairMemo`, `dispatch_live_item`,
`retain_candidate_value_rewrite`, and replacing-admission Rust branches.
The three retained-write outcomes (missing/conflicting rejection, identical
no-op, absent-target installation) and the preserved coordinate of replacing
admission match the formal functions. New admission call sites supply an
absent rewrite; existing admission does not overwrite it.

The no-duplication proof is a history invariant: an earlier birth gives a
retained target, whereas a later actual dispatch into fallback requires no
retained target at that same raw pair. The proof keeps duplicate and canonical
routing precedence. It excludes body entry without claiming that the retained
branch must win before those earlier branches. Context execution remains ahead
of dispatch and the theorem keeps its successful-prefix premise.

The changed step has an explicit projection agreement and successful publication;
it does not prove the extrusion callback terminates or succeeds. `unchanged`
is not an original inference step. Rollback/cancel is explicitly excluded;
no finite future pair universe, source restriction, resource bound or total
history is smuggled into the result. The remaining new-pair ancestry and whole
machine/history extraction are not discharged. This is valid progress on
one original allocation owner, not global accessibility.

## Independent checker evidence

Root-owned project cache; pinned Lean 4.35.0/Lake5.0.0-src+eb6cafb;
`LEAN_NUM_THREADS=1`, `-j1 -M1024`, each invocation limited to120seconds.
The separate module build exited0 in9.954seconds. The origin audit exited0
in1.274seconds and checked25 distinct originating theorem constants, including
all11 required authored roots. Ten theorems use no axioms, seven use only
`propext`, and eight use `propext` plus `Quot.sound`. No unexpected/project
axiom, sorry dependency or audit warning occurred. The audit program is checked
in alongside the module; raw output remains in the scratch evidence.

| Evidence | SHA-256 |
| --- | --- |
| Independent build log | `11d561cbbeb215df37efe7e599216b802dddfed772d078185fb711637193dd44` |
| Independent origin audit log | `f949dbe30e1fd54305ab9073566827edd4b57218f94d449082a0442280f7ca48` |

The author separately audited all81 declarations, including the same25 theorem
constants. Root review does not promote a declaration count into a proof of
unmodeled Rust transitions. The handoff's long console excerpt was replaced
with a concise statement map under `rules/git-concurrency.md`; the exact
original handoff remains in scratch. Mathematical source bytes are unchanged.

## Integration base and frozen inputs

The module was checked at99f18bdc54df8057f5a6d5d4bec5dc449336c234.
The concurrent3be95e44e/5428c5e62 changes add separate future/pair modules and
notes only; none modifies this proof's imported source cone or native inputs.
They were preserved by fast-forward before publication.

Current integration parent: `5428c5e62e31b20f261c76128cf426fdd137cca5`.

| Input | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalTerminationClosure.lean` | `f3b1373effdd99b5ef610f30ce3903ce119d66a4e16f9cf71ce09dee80ee00a6` |
| `notes/theory/lean/YulangClosure/NativeValueStructure.lean` | `81060e17ad37f2e4a47edb7ed2829bea6820438bf3d4db0e4de8d113fd9497fc` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `notes/theory/lean/AuditOriginalTerminationClosure.lean` | `a0f4a702a0bd6cda16fe9da52a3a4242a2cbdf6a83020bae068dcdb28a8b025d` |

Scratch evidence: `/workspace/scratch/e3678bef96db/termination-review-r3`.
No compiler, toolchain, dependency or semantic rule was modified.
