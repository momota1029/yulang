# CALL-OWNER-CONSTRUCTOR/20261028-r20 — producer-owned Call incidence

Status: ADMITTED BY LUNA — REVISION 1 under the standing research authorization.  
Branch/baseline: `yulang3`, `d33805eb5`; frozen inputs are in the R20 manifest.  
Authority: standing Rust/Lean inference-soundness research authorization; original `SourceProblem.InferenceSoundness`, Call/shared-witness and source/native obligations. Prior R19 is CLOSED_INCOMPLETE and remains immutable evidence.  
Contract revision: 1; admitted `2026-10-28T13:59:08Z` at baseline `d33805eb5`. No compiler, test, build or Lean execution authority is granted.

## Original outcome and success evidence

Advance `CALL-OWNER-CONSTRUCTOR/r20`: establish the missing original Call ownership edge at its actual source constructor and consumer, or state a precise construction obstruction. Preserve the original parent and every quantifier, supported source form, shared witness `xi=(nu,K,D)`, lawful allocation premise, independent F1/FK1 cases, complete Call consumer, foreign continuations and effect interpretation. The original parent remains:

```text
forall s xi d a,
  supported(s) -> generates(s,xi,d) -> solves(d,a) ->
  exists e, sourceJudgment(s,xi,e) and sameScoped(s,xi,e,a).
```

Success is one of:

1. a source-constructor inversion and commuting source/native account that derives the same Call owner, incidence and ordered port images from the original source derivation and actual producer, with every premise and application to the original parent explicit; or
2. a precise `NO_SAFE_CODE_SLICE` / missing-supplier result naming the actual constructor and consumer owners, the first absent source equation, and a falsifier for any proposed inference from endpoint equality or graph membership.

No term equality, reconstructed endpoint, native success, row membership, finite trace, or existing supplier predicate may serve as its own source owner. No source domain, theorem, witness, scope, semantics or expected result may be narrowed. A conditional or source-qualified result does not close the parent.

## Frozen inputs and source boundary

The input manifest SHA-256 is `ebd5164460314d7b6a940e9a9caf2bbbe385c105bc8f4ff15f13e7daa9eec57d` (25 exact file pins). The R18 input manifest is pinned at `d07167958cdb5f93a5370d48568a7a0ab4afc8b8ec31a02ffbdb359848a5b455`; the R18 final `candidate_scheme.rs` result is separately pinned at `3eb9ba3b414dd0e40f49957e0ee2b9de1ba21fd86dff718111d1b5030ccac6b7`. Use only `isolated/latent-demand-transport-classification-r18` source bytes. R19's candidate overlay (`985ea3…`) is excluded.

The proof/source investigation is limited to the pinned original Call definitions and source rules: `Contracts.lean` (`SourceProblem.InferenceSoundness`), `OriginalSourceSyntax`, `OriginalSourceGeneration`, `OriginalSourceEnvironment`, `OriginalSourceChecking`, `OriginalSourceInterpretation`, `SourceSignatureConstruction`, and the pinned source-rule/owner documents. Inspect the actual construction of `completeCallCertificate`, `sourceCallIncidence`, and `callableImage` against the governing C-Call and J-Owned rules. No Lean file creation or checker invocation is authorized; only deliver a concrete theorem type if source inspection supports it, otherwise name the missing premise.

The implementation audit reads the R18 `candidate_effect.rs`, `candidate_context.rs`, `candidate_scheme.rs`, `candidate_call.rs`, and `shadow_apply.rs`. Trace actual lower `OwnerEmission` through Function construction, capture/FreshUse retention and replay consumption. At minimum inspect `candidate_bound_origin_with_evidence` and the capture/reconstruction owners. Report whether any existing constructor supplies producer-owned four-port evidence. No source edit is authorized. Do not inspect or modify root working-tree changes; no Cargo, test, build, formatter or Lean process.

## Two continuing lanes and exact leases

- Proof/source: one Sol/high `prover` assignment, maximum 450 seconds, writes only `notes/theory/2026-10-28-call-owner-constructor-r20.md` and `tasks/agent-loop/inbox/call-owner-constructor-r20-proof.md`. It must make a multi-stage construction-directed source audit, apply any justified lemma to the unchanged parent, and stop at the exact absent equation otherwise. No Lean or code writes.
- Implementation: Luna/high primary audit, maximum 450 seconds, read-only over the five pinned R18 Rust files; writes only `tasks/agent-loop/inbox/call-owner-constructor-r20-impl.md`. It returns an end-to-end authorized code slice only if actual constructors already justify ownership and all ordered ports; otherwise give owner-specific `NO_SAFE_CODE_SLICE`. No compiler write lease or source edit.
- Independent review: fresh Sol/medium `compiler_referee`, maximum 300 seconds, read-only, writes only `tasks/agent-loop/inbox/call-owner-constructor-r20-review.md`. Review the frozen note and handoffs, exact source pins, original quantifiers, owner equations, scope and ordered-port falsifiers. Reviewer cannot author or verify its own result.
- Primary reconciliation/closeout: maximum 300 seconds. Luna owns runtime roster/accounting, adjudication, current state, outcome, exact staging and Git.

Aggregate envelope: 1,500 seconds; proof/source 450, primary implementation 450, independent review 300, primary closeout 300. No Astra. No build/test/Lean process. No previous unused allowance carries forward. No descendants. Each worker reports actual runtime settings, all measurements UNKNOWN if unobserved, and a write-stop receipt.

Primary outputs are the four frozen artifacts: the theory note above; the proof, implementation and review handoffs at their exact leased paths; plus Luna-owned outcome `tasks/agent-loop/history/call-owner-constructor-20261028-r20-outcome.md`.

## Review, stop and gate conditions

Review rejects every edge inferred from equal terms, endpoint reconstruction, circular supplier assumptions, changed scope or missing ordered ports. Stop on pin mismatch, missing source authority, incomplete producer/consumer inventory, changed source bytes, overlap, altered quantifiers, reviewer rejection, runtime boundary, unknown writer or user STOP. A blocked lane does not authorize source edits or stop the independent lane.

No production change follows from this packet. `SourceProblem.InferenceSoundness`, source/native Call/shared-witness, independent F1/FK1, effect hygiene, implementation and production remain OPEN unless their complete original obligations are independently discharged. R20 outcome is CLOSED_INCOMPLETE if the required source equation or review remains open. Consult the dispatcher at a material obstruction, authority/dependency/lease change, integration seam or sprint end.
