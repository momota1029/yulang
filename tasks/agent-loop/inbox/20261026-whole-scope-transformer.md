# WHOLE-SCOPE-TRANSFORMER-20261026 / r1

Status: checked native normal-form algebra; original full hygiene/soundness OPEN.
Author: `/root`; no child contributed to this artifact.
Baseline: `a9c746f31cc0eabeba9ebf5b673b6f121ed0ca82`, branch `yulang3`.
Fresh independent review is assigned to `/root/principality`, which did not
author this module. Its separate receipt determines acceptance.

## Original obligation and actual owner

The user requests the original whole Yulang soundness, Effect hygiene,
principality and inference termination. No supported source form, optional
record, complete Call, shared witness, effect or continuation is removed.

This artifact applies the existing reviewed finite algebra in
`notes/theory/2026-10-15-compose-scoped-release-construction.md` §2 to the exact
normal-form contents of `crates/yu-solver/src/candidate_scope.rs`.
The selected source policy remains
`notes/design/2026-10-15-compose-scoped-effect-release.md` and the existing
annotation/hygiene integration, rather than a newly chosen effect semantics.

The complete carried witness retains the contribution, original receiver,
receipt, provider, grants and source instance. The native transformer changes
only its input-route tags T and protection scopes U. In the native finite
normal form, J is the list of stamped tags; each scope has a keep bit and a
missing-tag disjunction B, with default `(true, [])`.

```text
T' = T union J
s in U' iff (keep_s and s in U) or exists u in B_s, u not in T

first.then(second):
J = J1 union J2
keep_s = keep1_s and keep2_s
B_s = (if keep2_s then B1_s else empty) union (B2_s minus J1)
```

`NativeScopeTransformer.lean` constructs this finite operation, including
omission of identity entries and retention of release tombstones. Its lists
denote sets by membership. They do not claim Rust's exact vector ordering,
sorting/binary-search correctness, allocator behavior or loop execution.
The native sorting/unique-support invariant is a source correspondence
boundary, not an unproved Lean theorem silently treated as accepted.

## New checked consequences

Namespace: `YulangClosure.NativeScopeTransformer`.

| Declaration | Conclusion and premises |
| --- | --- |
| `entryAt_encode`, `then_entry` | Actual finite omission/lookup yields the composed entry at every scope. No assumed representation law. |
| `evaluate_then` | For all two transformers and all input states, computed composition equals successive evaluation in both observable coordinates. No safety/composition premise. |
| `protect_then_release` | Protect then release equals release, including removal of an inherited protection. It is not falsely reduced to identity. |
| `stamp_then_protect`, `protect_then_stamp` | The actual two orders differ: the first suppresses new protection only; the second tests original tags. Inherited protection survives stamping. |
| `untouched_scope`, `evaluate_release` | An unrelated scope survives; only the named scope is removed. |
| `release_no_revival` | Release followed by a transformer cannot recreate that scope when its actual add guard is false. Later genuine introduction is not forbidden. |
| `compiled_execution`, `ordered_associativity` | Every finite ordered transformer list has the same evaluation as actual sequential application, including arbitrary incoming state. |
| `new_protection_has_origin` | Every newly present output protection comes from an applicable guard at a particular real prefix and operation of that same finite list. |
| `witness_observer_preserved` | Every observer of the complete unchanged witness is unchanged. This constructs no original witness or authority. |
| `evaluate_rename` | One jointly injective scope map and one jointly injective tag map, applied to both transformer and state, commute with evaluation. |
| `local_support_injection_is_insufficient` | Explicit counterexample to requiring injectivity only on the transformer's own support. It is not a counterexample to Yulang source soundness. |

The last counterexample uses `release 0`, incoming external protection `{1}`,
and a map sending both 0 and 1 to 0. The map is injective on the transformer's
singleton support; the renamed release nevertheless deletes the unrelated
incoming protection. Native `remap` checks only its own support, so its caller
must provide the wider fresh/external identity invariant. This was already a
boundary of the reviewed source algebra and is now kernel-checked. No claim is
made that the actual fresh-use allocator violates that invariant.

## Application to the original parent

The algebra now supplies actual preservation equations rather than assumed
`then/evaluate` or generic `LocalLaws` fields. It can discharge the local
ordered scoped-transformer part once an authentic source route has selected
its immutable transformer and complete carried witness.

The original full theorem remains OPEN. Its first outstanding owners are:

1. `candidate_source`, `candidate_call`, Function-port and Lambda-entry owners:
   construct the joint original argument-entry/body attribution and the actual
   protection/release scope. This algebra does not choose a scope from row or
   family equality.
2. Context/Replay/FreshUse owners: retain that exact association on every
   present and future route, and construct a shared injective renaming on the
   incoming state as well as the transformer's support, fixing external IDs.
3. Original `Kernel.atom` and V/W/T/Car input relations: realize receipt,
   complete Call, current-world activity, annotation permission and final
   observation interpretation. A preserved witness field does not establish
   those predicates or create handler eligibility.
4. Native implementation correspondence: connect sorted finite vectors,
   successful fallible operations and actual history to the content projection.

No compiler behavior, test expectation, dependency, toolchain pin or source
semantics changed. This result closes the stated finite algebra theorem only.

## Checker, audit and frozen evidence

Toolchain read-only path:
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
Actual Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

Focused `lake --no-cache build +YulangClosure.NativeScopeTransformer` passed,
2 jobs, final module 3.3 seconds, no new warnings. The complete originating
module census inspected all **107 theorem constants**, including generated
and private helpers, with full names, proof-valued type terms, and complete
`#print axioms` output. All 107 begin/end blocks are unique and balanced.

- 38 constants have no axioms.
- 23 use only `propext`.
- 46 use `propext, Quot.sound`.
- No `Classical.choice`, `sorryAx`, project axiom or unchecked evaluation axiom.

Source hash: `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`.
Native owner hash: `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a`.
Reviewed source algebra hash: `773a1ed4c2ebe7503438c57a06acd23e03fbc1fd0d6ae30260848c4430fe676e`.
Selected compose authority hash: `fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679`.

Complete audit log:
`/workspace/scratch/e3678bef96db/proof-checks/scope-audit.log`, SHA256
`5b153ae85db185948f3429e3e3b4a08947c8fad86487513aa1ca41cbc59d99e4`.
The adjacent `ScopeAudit.lean` generates the census. The integration audit will
retain a reproducible repository target for this and the three other modules.
The checker used `-j1 -M1024` and an explicit 120-second subprocess limit.

Material development failures: the first build exposed an over-unfolded
induction hypothesis and unavailable `by_contra`; the first renaming build
exposed a simplification-order mismatch. Both were repaired from actual Lean
goals and the entire final module rebuilt and audited. The original sandbox
could not locate the installed application prefix; the automatically approved
native execution environment resolved that tool issue without installation.

Source is frozen for the separate review. Primary owns only the new module,
this handoff, its scratch audit/build outputs and subsequent Git integration.
No other worker wrote this source; no background process remains.
