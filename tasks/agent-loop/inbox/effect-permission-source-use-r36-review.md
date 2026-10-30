# R36 independent source-use review — PASS after B1 repair

Reviewer: `/root/r36_source_use_review`. Frozen Rust handoff r2 and proof
handoff r1 reviewed independently. Initial inspection used actual Rust diff,
Lean definitions and governing policy before producer explanations. Skill:
`yulang-lean-proofs`, under the contract's read-only stdin exception to its
normal build workflow. Observed model/effort and dispatch-to-finish elapsed:
UNKNOWN; no model receipt or start clock was available. No descendants.

## Verdict and finding

**Final bounded technical verdict: PASS after the repair delta below.**
The original BLOCKING B1 and its evidence are retained here as history;
no blocking, major or minor compiler-correctness finding remains open for R36.

**Original FAIL / BLOCKING B1 — nonexistent annotation field prevents Rust compilation.**
At `tools/inference-playground/src/runtime/program.rs:307`,
`annotation.effects.is_some()` accesses a nonexistent field on
`yu_hir::shadow::SourceAnnotation`. Its actual declaration in
`crates/yu-hir/src/module/source_annotation.rs:125` contains `owner`, `position`
and `ty`; its impl at line 130 provides no Deref. `effects` belongs to
`SourceAnnotationType` at line 136. Therefore the new API cannot type-check
against its pinned direct dependency. This is static source evidence, not a
claimed observed compiler diagnostic. The responsibility owner is the R36
lookup's annotation-shape guard. Contract success evidence (1), an actual Rust
lookup/API deriving Observe from the approved formal shape, cannot hold for an
uncompilable declaration. Existing role construction at `program.rs:1130` uses
`annotation.ty.effects`.

Minimum closure: change this guard to `annotation.ty.effects.is_some()`, freeze
the repaired source and handoff hashes, then obtain a focused independent delta
review. No test-expectation change or semantic decision is needed. No build is
required or authorized by this packet. No other blocking, major or minor
compiler-correctness finding was found in the examined slice.

## Cause, ownership and alternate paths

The source witness otherwise addresses the owning construction: retained HIR
lookup supplies root/Lambda/formal, exact resolved Parameter Name and its direct
Apply-callee edge. It does not infer permission from execution symptoms. Snapshot
Arc identity, root ownership and occurrence/source-key agreement are checked.
The HIR `LocalSource::expression` owner check (local_source.rs:174) prevents a
foreign callee index from being followed. Parameter identity, not spelling or
range, excludes foreign/shadowed names. The immutable HIR builder mints distinct
occurrences and retains lexical resolution; `order_occurrences` and the existing
carrier/parameter tests were inspected. No new HIR/CST transformation is added.

The lookup inventories every matching Apply and returns `Some([])` when no
direct use exists; it does not choose a first use. A matching Name with multiple
Apply parents withholds the whole inventory. Nested Lambda captures resolved
to the same formal remain source uses; the result asserts neither dynamic
invocation nor body execution. Grouped/indirect callees and computation-effect
formals are outside this bounded selection, without narrowing parent semantics.

For an outer-effects-free direct Function formal, the existing role construction
derives Observe. R36's intended guard matches this owner after B1's repair.
Observe remains classification, with no consumed-permission interpretation.
The callback argument type stays general. R35 starts the formal at Negative;
Function.result preserves it and Function.argument flips it. Selecting exactly
`[Result]`/Negative excludes a positive argument row and every nested result path.
The selected row is rechecked against the direct Function result position and
full concrete/symbolic vectors. Ordered clones preserve duplicates and symbolic
entries. No spelling/family-set collapse occurs. Partial inventories are local
and are discarded on failure; no published state or recovery state is mutated.

The Lean model uses owner-indexed arenas and actual indexed Name/Apply edges.
`lookupLambda`/`lookupEdge` derive coordinates; `issueSelected` checks formal and
annotation root ownership and selects the exact R35 result row. The conclusions
bind these computed values, rather than assuming caller-provided row equality.
Its ambiguity count uses indices while Rust uses authentic occurrence IDs;
agreement relies on retained HIR occurrence uniqueness and is not a proved Rust
enumeration simulation. Arbitrary abstract pools are not certified as native HIR.
This distinction is disclosed and does not establish additional runtime facts.

## Independent Lean audit and every theorem result

Read-only command: `bwrap --ro-bind / / --dev /dev --proc /proc
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
--stdin -j1 -M1024`. Python supplied complete R34 standalone source, R35 and R36
with only their first import lines removed, then `#check @` and `#print axioms`
for every R36 theorem. No generated file or import cache was used. Exit 0,
empty stderr and no diagnostics; one measured subprocess, 8.096499784 seconds,
90-second timeout. Peak memory unmeasured. Input SHA-256:
`c1929a9297c4edc1ef9e6c624e5e16871a0bb19df4b6dbeca3708c7e0bf6a754`.
The different producer stdin hash is not an artifact discrepancy: this audit
constructed its own appended command stream. The frozen source hashes match.

All names below are under `YulangClosure.SourceCallbackUseR36`. The actual full
printed types were inspected, including implicit type parameters and
DecidableEq assumptions. No theorem assumes a Rust simulation or runtime law.
All thirteen passed kernel checking; the complete transitive axiom sets follow.

| Theorem | Checked premises/conclusion | Complete axioms |
|---|---|---|
| `lookupLambda_origin` | successful lookup yields actual owner-root/expression/Lambda/formal/annotation, outer-effects-free Function shape and unambiguous inventory | `propext` |
| `lookupLambda_r35` | successful R36 Lambda lookup yields R35 selectFormal on the same projected pool | `propext` |
| `lookupEdge_origin` | successful edge lookup yields exact Apply index/form, actual callee-index Name and selected formal resolution | `propext` |
| `foreign_parameter_name_rejected` | actual Apply/callee Name with distinct resolved formal yields no edge | `propext` |
| `nonparameter_name_rejected` | actual nonparameter callee Name yields no edge | `propext` |
| `ambiguity_withholds` | actual Lambda/formal/annotation with false unambiguous check yields no Lambda lookup | `propext`, `Quot.sound` |
| `source_origin` | authentication yields successful computed Lambda/edge/R35 permission and exact assembled witness | `propext`, `Quot.sound` |
| `authenticated_r35` | R36 authentication implies R35 authentication on pool.toR35 at `[.result]` | `propext`, `Quot.sound` |
| `authenticated_coordinates` | authentication yields shared source root/Lambda/formal/Name/Apply, exact indexed edge/sites, owner/formal binding and Observe | `propext`, `Quot.sound` |
| `authenticated_result_row` | authentication yields computed Function argument/result, actual selected result row, full row equality, every concrete index, all variables, exact result path and contravariance | `propext`, `Quot.sound` |
| `reject_changed_projection` | a candidate differing in any projection from the computed witness cannot authenticate | `propext` |
| `falsifier_rejection` | changed binding/formal/Name/Apply/index/row payload-position/consumption relative to computed witness rejects | `propext` |
| `covariant_or_other_path_rejected` | candidate noncontravariance or non-result path prevents authentication | `propext`, `Quot.sound` |

Seven use only `propext`; six use `propext, Quot.sound`. None uses
`Classical.choice`, `sorryAx` or project axioms. Explicit-file source scan of
complete R34/R35/R36 for `sorry`, `admit`, project `axiom`, `native_decide`,
`skipKernelTC`, `implemented_by`, `unsafe` and check/kernel option bypasses
returned no matches (rg exit 1). Producer failures and successful audit receipt
were also inspected; failed elaboration outputs are not accepted as proofs.

## Quarantined-read incident adjudication

Rust handoff r2 lines 42–48 discloses a recursive search whose matching line
text from both quarantined runtime files entered the producer's tool output
and context. This was an actual unauthorized read-boundary violation under
the contract's explicit exclusion. Absence of a full-file open does not erase
that violation. Its r1 denial was inaccurate and r2 corrects it. The producer's
claim of no influence is not independent evidence of non-influence.

Primary adjudication permits independent review of the frozen artifact against
allowed sources while retaining quarantine and incident evidence. This review
did not open or search either quarantined path. The source-side derivation
above is independently reconstructible entirely from permitted program/HIR,
R35 and policy definitions; no quarantined fact is needed. Thus the incident
does not add a technical source-correspondence blocker. B1 independently keeps
the original artifact FAIL. Preserve the incident and corrected account; do not describe
the producer's search as compliant, or release either quarantined lease.

## Exact frozen hashes

| Artifact | SHA-256 |
|---|---|
| `program.rs` | `1a6f27609bc510d905b85be6f33a43b87bb95e1224794fe0fdd01688381e89b2` |
| Rust handoff r2 | `df72f3c643b1267f4d9ff40e737890d45fe4059f4c9e5b75a7c246bb5d480ec5` |
| R36 Lean | `9e15cb4982248cf90d7a11ef0c66ee7ee95ec0abe99c217d8187c31c488731de` |
| Proof handoff r1 | `0d1a5d7e4c31ff6722269c6d894f301950c87b34c641b395e11c8360aebd8558` |
| Contract r1 | `c471c7dd5d8ef2515022f4665f1ef2151577141a3f0942ea107489ecd86c5ac0` |
| Manifest r1 | `cf03b01ba1cb057972303540dd7deb881e0cfff2f8dbafd93e4912035bee37e4` |
| R35 Lean | `f4d6c85dc12d9e5b9f58a6635c76ee49fba85ff732b5538f9924e1ab052dbcc9` |
| R34 standalone | `24ca25828e1a58f9c3246e5f50f2c73ba8ead6d2d003d05c8c2a8a3d2e85795a` |

All fourteen immutable manifest inputs were independently SHA-256 checked and
matched. `program.rs` is the authorized changed output, not an expected match
to its input hash. No frozen artifact mismatch was found.

## Omissions and remaining gates

No Cargo, build, tests, formatter, Lake build, default/import integration,
scratch, cache, target, copy, worktree or new environment. Existing relevant
HIR tests were read, not executed. No compiler or shared scheduling/Git write.
Only this leased review artifact was written.

B1 initially blocked R36 acceptance; the final delta below closes it. Rust compilation remains
unobserved even after the static correction. Rust-to-Lean HIR extraction,
ownership-map validity, vector/list enumeration and empty-inventory simulation
remain unproved. Source-planned use is not actual runtime invocation or a Name
receipt. Runtime consumer integration, permission/Grant emission, constraints,
transport/propagation, Catch subtraction/residual, selected-arm and observation
provenance, invocation lifetime and native Step/History remain OPEN. Original
Simple-sub A/B, source joint-strategy premise, whole-language hygiene,
soundness, principality, progress, termination and production remain OPEN.

Reviewer STOPPED; writes stopped after this review. No descendants or persistent
verification process; no path leases were released.

## Independent repair delta — B1 CLOSED, bounded technical PASS

Primary repaired `program.rs:307` to `annotation.ty.effects.is_some()`.
The new field path is valid against the pinned actual `SourceAnnotation` /
`SourceAnnotationType` declarations and matches the existing role owner.
Reversing exactly this one replacement in memory reconstructs the previously
reviewed complete source hash
`1a6f27609bc510d905b85be6f33a43b87bb95e1224794fe0fdd01688381e89b2`.
Thus no other byte change to the Rust source is hidden in this delta.

Repaired `program.rs` SHA-256:
`b3fc1daacdba9fa9618b9b741e4f85d8e9ea0dcd5e859540204d09200d23a65d`.
Rust handoff r2 remains frozen at the hash in the table; its reported old source
hash is historical, superseded for review by this primary repair receipt.
No Lean byte changed and the complete independent audit remains applicable.
No build, test, formatter or quarantined read was performed for delta review.
Rust compilation is still unobserved; the static B1 defect is fully closed.

This PASS applies only to the contract's source-planned-use construction and
conditional Lean projection. Every remaining parent/runtime/simulation gate
listed above stays OPEN. The unauthorized producer read incident remains
recorded and does not become a compliant read through this repair. Reviewer
STOPPED with writes stopped after this final delta; no descendants.
