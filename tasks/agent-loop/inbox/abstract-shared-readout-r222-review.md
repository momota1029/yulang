# R222 bounded obstruction review

Reviewer: `/root/r222_obstruction_review`, registered `compiler_referee`,
read-only. Luna transcribed this final review because the reviewer role cannot
write repository files. This is a review of the direct-encoding obstruction;
it is not a review or approval of a completed R222 compiler.

## Verdict

**PASS for the bounded direct-encoding obstruction; BLOCKING for R222
completion.** No major or minor defect was found in the obstruction argument.
This review is source-based and did not run Lean.

The reviewer confirmed the supplied R222 contract, equation-artifact and
handoff hashes. The pinned R212 core and graph/coalescing dependencies also
matched. The handoff itself was treated as a claim to inspect, not as proof.

## Findings

1. **The concrete R212 operation produces the stated state.** The one-row
   fixture passes `CoreProblem.inputValid`: row 0 exists, both endpoints are
   allocated, and the reference table is valid (`AbstractSimpleSubCore.lean`
   80–91). Initialization creates identity representative `[0]` and an empty
   level-0 row (144–156). `insertPendingUpper` resolves row 0, passes `0 ≤ 0`,
   prepends `.var 0` to upper bounds, and has no replay demand because lower
   bounds are empty (174–189). It leaves the retained reflexive constraint and
   empties pending; this is not evidence of a complete accepted run.

2. **The paper equation and direct graph match the stated boundary.** Fig. 12
   evaluates its positive seed under the original seen context. The R222
   equations retain that context and do not adopt R212's extra positive seen
   key. Paper singleton meet syntax gives `μn.n`; expanding the meet with its
   neutral Top seed gives `μn.(Top ∩ n)`. These are recorded as equation
   presentations; no recursive-semantic equivalence is asserted. Encoding the
   explicit fold body at its root yields `[intersection 1 0, structural Top]`.

3. **The graph is Valid and not Guarded.** Both intersection children exist, so
   graph validity holds. `FiniteLattice` requires both meet children to have
   finite derivations. A derivation at node 0 would therefore contain a
   strictly smaller derivation at node 0 through the self edge, impossible by
   induction. Thus `Graph.Guarded` fails. A terminating Top branch cannot
   discharge the cyclic branch.

4. **This is a construction obstruction only.** The retained store constraint
   is reflexive and has a guarded Top solution. The paper allows unguarded
   recursive syntax while restricting recursive subtype hypotheses. The
   displayed failure proves neither inconsistency nor impossibility of every
   semantics-preserving encoding. Replacing the cycle with Top for this one
   fixture does not establish full Fig. 12 correspondence; filtering immediate
   self bounds also leaves a two-row cycle unresolved.

5. **R222 completion is BLOCKED.** The equation artifact has only an
   unimplemented theorem target. `ExactFig12Interpretation` is not defined,
   and there is no checked compiler, graph/reference/store theorem, or axiom
   audit. The R222 contract's success gate therefore remains unmet. Duplicate
   representative bound preservation and finite structural-spine
   correspondence are additional open seams.

## Disposition

**Parent delta 0; roots 0/4; packages 0/5.** No unchanged parent is proved or
refuted. R222's precise direct-encoding obstruction is independently reviewed;
its construction goal remains open.

Reviewer final-response receipt: read-only final answer from
`/root/r222_obstruction_review` received 2026-11-02; no reviewer-owned file,
cache, test, build, Git, or scratch output was created.
