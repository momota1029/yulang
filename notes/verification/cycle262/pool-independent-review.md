# Independent read review: SourcePool261 and next source request pool

Reviewer: cycle262 read-only child, 2026-11-18 UTC.
Scope: source reading only; no independent rebuild, kernel invocation, runtime test,
or new Lean proof is claimed here. Existing files were not changed.

## SourcePool261 review

Reviewed `GeneralRebaseSourcePool261`, `GeneralRebaseSourceSnapshot261`,
`GeneralNominalVersionedMixedInstallRequests235`, `GeneralNominalVersionedInstall232`,
and actual versioned child emission definitions.

No correctness or claim-scope defect found:

- `same_sites` really needs only equality of the raw sites list because `candidates`
  is precisely flatMap of each raw site's occurrence outputs.
- Actual centered `merge` and `refresh` leave that list unchanged, so `rfl` is exact.
- `installCore` appends `rawSites plan` to the old raw list. In `absorbed_install`,
  an old site's output is directly in the old list; a newly emitted site's output
  is in its old alias class by the supplied `Absorbed` hypothesis and therefore in
  the old candidate list by `SourceSnapshot261.covered`. Conversely every old site
  is still present in the append. The theorem concerns membership, not list equality.
- `installed_requests_covered` first covers requests by the new snapshot's actual
  candidate list, then applies the previous membership equivalence. Its use of
  Absorbed is visible and indispensable to this particular *unchanged pool* result.
- No part of these proofs derives Absorbed for a general source installation, proves
  capture/Plan transport, packet soundness, or closure of substitutions in a pool.

The cycle261 self-review's caveats are accurate. This independent reading fills the
previously missing SourcePool261 read review only; it does not upgrade the prior
verification into an independent full build.

## A meaningful next theorem without Absorbed

A fixed pool may be larger than the current snapshot. One can allow genuinely new
public request targets without needing those targets to appear in the old alias class.

### Local bridge: every emitted child target is a public port

Proposed exact statement (all variables arbitrary, not just a fixture):

For every packet, clause in `packet.declaration.requirements`, clause Signature,
and output in `(VersionedFrame231.clauseChild packet clause signature).demand.outputs`,

```
output.target ∈ PublicPorts253.ports packet.context.state.seed
  packet.site.occurrence.identity packet.declaration
```

Proof obligations are local and appear discharged by existing definitions:

1. Unpack the map of `clause.outputs` to an Equation.
2. Unfold `GeneralDeclarationDemands.outputTarget` and split on normalized RHS.
3. For `.var name`, if `name ∈ declaration.outputNames`, the target is
   capture.outputs name, definitionally the purpose2 allocation. Apply
   `PublicPorts253.output_mem`.
4. Every other case uses `allocation.outputs equation.id`, definitionally the
   purpose5 allocation. Apply `PublicPorts253.clause_output_mem`.

The old/new `VersionedFrame231.output_target_eq` and `child_outputs_eq` also expose
why observation-versioned purpose0/1 private aggregates cannot enter these targets.
This local target statement needs no model, Generated, Installable, Absorbed, or
finite-depth assumption. It is a theorem proposal, not a kernel-certified result yet.

Lift it from `clauseChild` to all children, emitted centers and rawSites by the actual
canonical-requirement map, `emitted_occurrences`, and `rawSites = emitted.map observed`.
Do not replace the canonical list by an assumed arbitrary emission relation.

### Trace-wide target pool

`PublicPorts253.mixed_finite_ports` already supplies one List Nat for every later
eligible mixed-source installation, with explicit Generated, Installable and
not-Committed premises. The install constructor of the actual mixed Step provides
exactly those premises. The finite owner proof is not applied to arbitrary sites.

Proposed statement:

For every sourceRegistry, root, start and actual mixed-source Initial proof, there
exists a fixed finite List Nat targets such that for every state reached by that
boundary's Step and every raw site in `state.core.erased.current.sites`, every
output of that site has target in targets. One possible targets list is
`root.demand.outputs.map Output.target ++ futureInstallationPorts`.

Proof by the actual path constructors:

- Initial raw list is the root point-site singleton.
- Refresh, equate, reobserve and merge do not change raw sites.
- Enqueue cannot occur on these source paths: `MixedTrace235.steps` plus
  `generated_registered` produces an existing raw site for focus, contradicting
  enqueue's absent premise. This is the same reasoning used in
  `OutputMenu254.source_names`; do not silently omit enqueue.
- Install appends rawSites. Old sites use induction; new sites use the local child
  target bridge and mixed_finite_ports at the *pre-install* state/path.

No Absorbed hypothesis is needed; the fixed pool includes ports of future owners,
not merely outputs already recorded in the old state.

### Full request objects, not target names alone

The finite rebase candidate API expects `List GeneralSourceState.Output`, not List Nat.
A target bound alone is insufficient. `OutputMenu254.names compiledRegistry root`
contains root output names plus all requirement-equation names. Its existing
`source_names` theorem is for centered sites, so either prove the corresponding raw
site invariant by the same path induction, or prove raw-to-center occurrence coverage.
Do not cite the centered-site theorem directly for an arbitrary raw site.

A finite request pool is the product of this name list and the fixed target list:
`names.flatMap fun name => targets.map fun target => (⟨name,target⟩ : Output)`.
This overapproximates correlations; it does not claim every product pair is emitted.
Using the raw-site invariants and `HeadOutputs.mem_requests_iff`, the resulting theorem
can quantify over *every queried root*, not only Generated roots:

```
∃ pool : List Output, ∀ state,
  Steps (mixedSourceBoundary.Step sourceRegistry root) start state →
  ∀ queriedRoot output,
    output ∈ HeadOutputs.requests state.core queriedRoot → output ∈ pool
```

The queried root does not add outputs: requests filters existing raw sites. Duplicates
are harmless for membership. This is a source-derived existence theorem, not yet an
executable extraction API from a source syntax input.

## What this still would not prove

The trace above is the legacy mixed/versioned source boundary's actual Step, not the
new finite rebase Step. The result could supply a source-wide candidate basis to the
new observer, but does not itself define or certify advancing the source snapshot
inside that rebase transition. Fixed request identities do not imply fixed Plan or
capture meaning; changing Plan/capture while reinterpreting already-installed facts
still needs its separate transport/history proof. General EvidenceNode, packet
compilation, whole-language termination and public model equivalence remain open.

This is compatible with I52 only as a dependency feeding the already-defined finite
rebase Step; it should not be advertised as a new termination theorem for the old Step.

## Follow-up implementation at parent request

The proposed local and full-trace bridges above were subsequently implemented in
new files only, after the parent explicitly expanded this assignment:

- `lean/Yulang/GeneralRebaseChildRequestPool262.lean`: equation_target, clause_target,
  emitted_target, raw_target, raw_name, product, mem_product, Covered,
  requests_covered, snapshot_product.
- `lean/Yulang/GeneralRebaseSourceRequestPool262.lean`: pool, trace_covered,
  mixed_finite_requests, all_requests.
- `lean/Audit/Cycle262RequestPool.lean`: axiom audit of all14 explicit declarations,
  full types of the source theorems, four usage examples including one pool covering
  two independently selected reachable snapshots and arbitrary query roots.

Both new modules passed strict focused compilation using Lean4.35.0 with
`--trust=0 -DwarningAsError=true` and the retained focused dependency cache.
The standalone audit passed both direct lean and the required independent
`lake env lean --trust=0 -DwarningAsError=true Audit/Cycle262RequestPool.lean` invocation.
Outputs: `request-pool-audit.txt`, `request-pool-lake-audit.txt`. Exit0 for each.
Only standard propext, Classical.choice and Quot.sound occur. The new files contain
none of the forbidden proof placeholders or native evaluation tactic.

Thus the exact `all_requests` type above is now kernel-checked. The caveats about
old-source Step versus new rebase Step, dynamic Plan/capture meaning, executable
source extraction and whole-language termination still apply. This follow-up code
was authored and audited by the same reviewer; it is not an independent rebuild
or independent semantic review of those two new modules.
