# WHOLE-SCOPE-REVIEW-20261026 / r2

Verdict: **ACCEPT for the stated finite normal-form content/algebra claims.**
Blocking findings: none. Major findings: none. Required repairs: none.
Original whole-Yulang hygiene/soundness/principality claims remain OPEN.

Reviewer: `/root/principality`; not an author or contributor to the reviewed
module. This worker authored `OriginalPrincipality.lean`, which is not imported
by the reviewed file and is not part of this review. No child or co-reviewer.

This r2 adds review of the producer handoff received just after r1 froze;
the code verdict and all findings are unchanged. Prior r1 receipt SHA-256:
`ac855becd33dfd518d4c99bcaf7eea3bf08abf0b0a3e4251f91dcd4d700e8398`.

## Frozen review target and sources

All three supplied SHA-256 values were recomputed and matched before review:

| File | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeScopeTransformer.lean` | `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6` |
| `crates/yu-solver/src/candidate_scope.rs` | `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a` |
| `notes/theory/2026-10-15-compose-scoped-release-construction.md` | `773a1ed4c2ebe7503438c57a06acd23e03fbc1fd0d6ae30260848c4430fe676e` |

I read the entire Lean module, the native scope module, the governing
construction §2 and its native-correspondence qualification, and the selected
`notes/design/2026-10-15-compose-scoped-effect-release.md` authority. Initial
large tool output was truncated; the affected final renaming declarations and
source sections were reread in bounded windows before reaching this verdict.

## Source fidelity and proof assessment

1. **Exact state content.** The formal fields correspond to native stamped
   input tags and each scope's keep-initial flag plus missing-tag disjunction.
   An absent entry has `(true, [])`. Lists are interpreted by membership;
   `Equivalent` does not falsely assert sorted-vector or list equality.
   Arbitrary repeated formal keys use the first entry; the native canonical
   maps are included as the intended special case. Duplicate supports emitted
   by formal `encode` carry the same computed entry, so they do not invalidate
   the membership theorems or assert native representation equality.
2. **Composition formula.** `composeEntry` correctly gates the first missing
   set on the SECOND keep bit and removes only FIRST stamps from the second
   missing set. The combined stamp set is union by membership. It does not
   incorrectly remove guards intersecting the final stamp set. `evaluate_then`
   is proved from these definitions and tests the original input tags; it
   neither assumes composition nor imports a safety conclusion as a premise.
3. **Release/order.** Release retains a false-keep empty-guard tombstone.
   `protect_then_release` removes inherited protection as well as a newly
   added mark; it does not rewrite this operation to identity. `stamp_then_protect`
   suppresses a new mark while retaining inherited marks. `protect_then_stamp`
   keeps the initial-input test. `evaluate_release` and `untouched_scope`
   preserve independent scopes. These match the scoped compose decision's
   local operation; they do not construct `compose id g`'s source witness.
4. **Finite histories.** `compiled_execution` and `ordered_associativity` are
   extensional consequences of the verified composition and congruence laws.
   `new_protection_has_origin` identifies an actually applicable guard at
   some history position for a mark absent initially. The theorem does not
   claim that this is the unique or final introduction, or reconstruct a
   complete original source provenance; its comment correctly preserves that
   boundary. `release_no_revival` has the explicit no-add premise evaluated
   against the unchanged incoming tags.
5. **Whole carried witness.** `applyFact` preserves its entire `Witness`
   field. `witness_observer_preserved` therefore quantifies every observer of
   that same field, rather than separate component witnesses. This is a
   correct product-state invariant. It cannot establish that an actual
   native Context contains the original receipts, grant and provider fields;
   the module expressly leaves their source/native interpretation to the
   owner. No complete Call or hygiene premise is thereby discharged.
6. **Renaming.** `evaluate_rename` requires a single globally injective scope
   map and globally injective tag map shared by transformer and incoming
   state. Both positive membership and negative guard tests use those maps.
   `renamed_output_has_origin` closes the non-surjective-map case: no output
   scope outside the image appears. The conclusion is the correct content
   equivalence, not syntactic equality of noncanonical lists. The theorem
   does not infer its global premises from native `remap`'s local checks.
7. **Counterexample validity.** For `release 0`, the transformer's scope
   support is the singleton `{0}`, so the constant-zero map is injective on
   that support and the native support-only collision check would find no
   duplicate. Incoming independent scope 1 becomes 0. Remap-then-evaluate
   releases it, producing no protection; evaluate-then-remap preserves
   original scope 1 and maps it to protected 0. The displayed inequivalence
   is valid. It refutes the proposed support-local-to-global equivariance
   implication only, not the full source algorithm, and is labeled that way.

## Producer handoff claim review

I additionally read `tasks/agent-loop/inbox/20261026-whole-scope-transformer.md`
at SHA-256 `f0741791880a9b2f6f60398cc711ac4cb4336d64d6536a7223c7eeb5900f86b3`.
Its claims match the checked declaration types and source content formulas.
It expressly distinguishes set-content equivalence from Rust vector execution,
keeps authentic source attribution and the external-state FreshUse map open,
and does not turn preservation of a generic carried witness into construction
of original current-world/Call/annotation predicates. Its integration intent
does not claim those missing premises are established. No additional finding.

## Checker evidence inspected

Producer census log:
`/workspace/scratch/e3678bef96db/proof-checks/scope-audit.log`.
Recomputed SHA-256:
`5b153ae85db185948f3429e3e3b4a08947c8fad86487513aa1ca41cbc59d99e4`.
I also read the adjacent `ScopeAudit.lean` that produces the census.

The auditor enumerates the actual originating module via
`getModuleIdxFor?`, includes every `.thmInfo`, rejects project `.axiomInfo`,
prints the complete type and axiom list of each theorem, and rejects axioms
outside the standard whitelist. `pp.fullNames`, `pp.privateNames` and
`pp.proofs` are enabled. I independently counted **107 unique BEGIN markers**
and **107 matching END markers in the same order**, with **107 axiom reports**.
All key authored declarations, including the counterexample and witness
observer theorem, have their printed types in the log. Distribution matches:

- 38 declarations: no axioms.
- 23 declarations: `propext` only.
- 46 declarations: `propext` and `Quot.sound`.
- No `Classical.choice`, project axiom or unapproved dependency appears.
- No warning/error text appears in the census log.

The producer reports pinned native Lean 4.35.0 focused build/audit exit 0.
This review inspected that evidence and performed source/mathematical review;
it did not independently rerun Lean or Rust. No concrete residual elaboration
or execution risk warranted spending the optional focused recheck.

## Scope expressly not certified

Acceptance does not cover Rust sorting/binary-search/loop implementation,
allocation and overflow paths, the runtime binary, native caller authentication,
FreshUse's construction of one map over external state, source attribution,
complete Call/Context/effect guards, actual provider/grant preservation, general
inference termination, source principality, or the full original hygiene theorem.
It also does not assert canonical-form uniqueness or raw-list representation
identity; those are not the delivered theorem conclusions. The definitions and
comments accurately distinguish these omissions from the accepted content laws.

## Receipt

Exact repository write: this review file only. No source, expectation, status,
root import, configuration, dependency or Git mutation. No children and no
running processes. All review writing is stopped at r2. The primary owns intake,
integration and any later whole-source application. Independent acceptance is
for the exact frozen target hash above and cannot follow unreviewed edits.
