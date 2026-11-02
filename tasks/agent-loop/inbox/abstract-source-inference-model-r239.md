# R239 abstract source inference model — primary outcome

Sprint/contract: R239, revision 1  
Contract SHA-256: `3c03946cab54003b15d56ce4265abbddfba719b3f98965780e040aa02d2c9bd3`  
Baseline: `yulang3/dea5d9d92c4429d0a259e0db8475c315a2ca39b3`  
Owner: Luna primary  
Parent roots: unchanged `SourceProblem` obligations at
`Contracts.lean:128–154`  
Outcome class: **MODEL-INCOMPLETE at independent generator/meaning boundary**.

## Result

No honest concrete Yulang `SourceProblem` value can be assembled from the
reviewed frozen definitions without supplying missing source meaning or
relabeling an existing conditional fragment as the complete algorithm. The
candidate model module was not written. This is an incomplete-model finding,
not a counterexample to Yulang and not evidence that the four original roots
are false.

The unchanged root statements themselves are usable and retain the requested
quantifiers. The missing object is the concrete Yulang instance `p` whose
fields agree on one independently generated problem, assignment and shared
source witness.

## Exact interface cut

1. `OriginalSourceGeneration.sourceRules` and `Build` construct the original
   finite source rule program. `Satisfies` interprets its atoms through a
   supplied `OriginalSource.Kernel`; `SourceJudgment` uses that same kernel.
   `generated_constraints_imply_source_judgment` is therefore a reconstruction
   result from already satisfied source premises, not independent
   Simple-sub generation or solution interpretation.
2. `SimpleSubConstraintSyntax` gives independent structural `Sub` and Store
   satisfaction. Effect atoms remain opaque identities. The module explicitly
   leaves complete Function admission, contextual effects, source generation,
   recursive solution interpretation and generalization open.
3. `SimpleSubGrowingInference` and its lattice counterpart provide transition
   components over supplied bounds, levels, graph and allocation data. They do
   not define the full source initializer/generator or the actual whole-source
   scheduling relation needed for `InferenceTermination`.
4. The R209 inventory and R213 fixed-model outcome already enumerate all
   original constructors and the missing independent generator, full local
   meanings, same-assignment readout, Call/effect equations and full transition
   relation. R238 independently pinned the annotation declaration-to-Lambda
   consumer cut. Those findings remain true; no lemma or definition in this
   sprint removes them.

Consequently, none of the following field substitutions is acceptable:

- `generates := Build` and `solves := Satisfies` (source-rule compilation is
  not Simple-sub generation, and the source `Kernel` remains its meaning);
- a `Kernel` whose local fields are arbitrary predicates or whose atom meaning
  assumes successful source typing;
- a `sameScoped` relation that identifies only endpoint values or drops the
  original owner, event, use, future or shared witness;
- placeholder `nativeSuccess`, `inferInitial` or `inferStep` fields unrelated
  to the actual abstract algorithm.

## Material equations still requiring an authoritative construction

- **Independent source generator and solution readout:** define actual source
  clauses and their denotation for every existing source constructor under one
  source signature and assignment, then derive the original local rule
  premises without using `sourceJudgment` inside `solves`.
- **Annotation hygiene:** connect the resolved declaration to the exact
  Lambda `sourceFormalRole` atom, preserving event/receipt/shared coordinates,
  composed Function polarity, wrapper rows versus arrow rows and effect
  identity/type arguments. R238's independent review found these equations
  absent from R217/R208.
- **Literal generation:** R237's reviewed all-eight direct-generator equation
  remains a proposal awaiting the user's scoped adoption decision. L1 authorizes
  source literal meanings, not that generator clause.
- **Typed Union:** the existing user question remains pending. Do not consume
  its proposal or narrow source coverage.
- **Call/checking and abstract transitions:** expose the original complete Call,
  direct boundaries, accumulation, propagation, level-aware extrusion,
  birth-qualified intrusion and generalization in the same model. Existing
  structural and finite transition lemmas are components, not a whole algorithm.

These are definition/authority blockers before soundness, principality and
termination proofs. No proof lane is activated until the full candidate can
state a concrete `p` without these substitutions. The requested full-domain
model remains the objective.

## Before/after and lane accounting

- Before: R209/R213 said `MODEL-INCOMPLETE`, R238 found no authoritative
  annotation-to-Lambda bridge, and no concrete Yulang `SourceProblem` instance
  existed in the inspected modules.
- After: no root model was built; the same instance/interface cut remains.
- Parent-premise delta: **0**. Roots closed: **0/4**. This packet adds no theorem.
- Rust: `NO_SAFE_CODE_SLICE`; clean source/effect owners already retain and
  authenticate adjacent annotation permission evidence. No Rust path was
  edited. UNKNOWN/quarantined runtime paths and the pending question directory
  were not opened or changed.
- Verification: no Lean/Lake build or theorem check was run because no Lean
  declaration was produced. The pinned toolchain path resolves to
  `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`;
  project pin remains `leanprover/lean4:v4.35.0`. No cache generation, new
  environment, worktree, target or scratch path occurred. The user-authorized
  existing cache remains available for the next checkable definition.
- No tests were run.

## Independent review and adjudication

Fresh independent compiler-referee review passed the exact MODEL-INCOMPLETE
disposition: no blocking or major finding; parent-premise delta remains 0 and
roots remain 0/4. The reviewer confirmed that the only receipt defect was the
65-character Contracts digest in the sprint contract. Luna corrected it to the
actual 64-character SHA-256 and refreshed the contract, handoff and current-state
receipts. Delta review passed the corrected contract and dependent hashes.

Review evidence: contract `3c03946cab54003b15d56ce4265abbddfba719b3f98965780e040aa02d2c9bd3`;
this handoff before this review receipt `cefe5636f30f7233e51927054620fae176b46b0ec7066e2a3992476ca3eeb32f`.
The substantive verdict and model boundary are unchanged.
Only the primary may change the source model, current state or Git. Any next
packet must take the first missing independent-generator equation toward the
original roots; a new local hygiene lemma alone is not a continuation.
