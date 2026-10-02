# Current task: prove and implement SCC-intrusion Function inference

Updated: 2026-10-02. Branch: `research/simple-sub-intrusion`.

## Objective and authority

Prove that the successor plan in `notes/design/2026-09-29-scc-intrusion-generalization-sketch.md` and `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` can preserve soundness and principality while matching Oracle's final well-typed-program capability on the supported envelope, then implement the reviewed and approved inference machine. The full objective remains active.

The redesign charter governs. F5 Function generalization is comparison/rollback material, not the target. The new source semantics and implementation remain non-authoritative until reviewed and explicitly approved. No compiler implementation is authorized yet.

## User-selected invariants

- Soundness and principality outrank Oracle compatibility. A deliberate difference needs a concrete conflict, the dropped Oracle behavior, the successor behavior, and final-acceptance impact.
- Final well-typed-program acceptance matters; inference-stage scheme formatting/acceptance parity does not. Preserve meaningful source constraints; polarity-only `q` erasure is not required.
- Exact traces are a soundness reference. Do not require linear/affine continuation typing merely to infer exact trace support; define principality relative to the chosen sound effect abstraction.
- Keep typed-family constraints symbolic through solve, residualization, generalization, freshening, and intrusion. Prefer one compositional relation over site-specific selectors/obligations. Oracle weight routing is characterization evidence, not authority.
- Callback capture is receiver-activation scoped and preserved through nested transitions. Escaped closures retain latent effects, origins, symbolic `K,D`, and required runtime lineage. Fresh caller handling follows the current source relation; no persistent maker mask without an independent source principle.
- Method selection, roles, and implementation resolution are a mandatory later gate after ordinary effects/handlers settle, unless a dependency appears sooner.

## Milestone state

| Milestone | State | Exit evidence |
|---|---|---|
| 1. Coherent ordinary computation semantics for calls, closures, `Force`, requests, callback visibility, and shallow handlers | Candidate source semantics uses the user's rule: concrete typed callback boundaries govern direct and Force-exposed request visibility; origin/identity/`K,D` remain distinct and `Force` creates no authority | Preserve this boundary rule in Milestone 2; no callback micro-cases without a counterexample |
| 2. Source-to-complete-interface adequacy/simulation | Closed for the candidate ordinary machine: exact embedding covers initial `R`, primitive source-rule images, latent future use, and typed resumptions; bind lifting separately reviewed | This proves the candidate machine embeds in its exact complete interface, not that current Yulang typing derives the candidate binder ownership or has a finite presentation |
| 3. Finite symbolic presentation | Finite heap carrier and principal safety-certificate theorem reviewed for a declared conservative abstract judgment; source instantiation remains open | Prove source refinement/error reflection, finite endpoint basis, and future-interaction coverage; bridge to intended typing and audit final acceptance before selecting the abstraction |
| 4. Generalization, fresh instantiation, SCC intrusion | Waiting on a Milestone-3 presentation | Prove lifecycle transport for that presentation, including external uses, internal SCC sharing, parent ports, and symbolic effects |
| 5. Implementation feasibility | Deferred until milestone 4 determines required surfaces | Targeted architecture/resource audit of the reviewed semantics and representation |
| 6. Implementation | Not authorized | Explicit user-approved design, completed required gates, implementation and verification |

## Milestone-3 finiteness classification

The user directed separate classification of (1) finite but unbounded principal
presentations, (2) infinite unfolding with a finite SCC/regular graph, and (3)
genuinely non-finite presentations proven by a concrete counterexample. Current
evidence now includes a finite heap carrier and principal symbolic interface
for a declared abstract safety-certificate judgment, with fixed finite
program, symbolic basis, and observations. It does not yet establish that
judgment for the complete Yulang source interface. Recursive back-edge graphs and regular stacks are candidate
representations, not yet preservation theorems. A stack-only quotient has a
candidate-machine counterexample from captured-reference aliasing and handler
selection; this does not refute richer finite relational graphs. The full
capture/resumption quotient remains unclassified, and no class-3 impossibility
result exists.

If a later representation is finite per source but unbounded across sources,
an explicitly budgeted structural metric may yield a deterministic inference-
complexity failure, never an `ill-typed` result. Its metric, threshold, check
point, no-truncation behavior, and atomic publication belong to the later
resource design gate; no numerical limit is selected now.

The exact-acceptance quotient inquiry rejects stack-only and independent marginal-store
abstractions that forget captured/caller alias incidence without an exact
selection witness. Investigate a joint rooted capture/store/continuation graph
with shared symbolic `K,D`; this is a candidate, not an established finite or
regular representation. Prove source-image closure preserving actual ordered
selection, latent/resumption future use, existential identities, and shared-`ν`
fibers, then prove least representable projection. Class 1/2/3 remain
unclassified for the complete interface, with no class-3 witness.

A conditional lower bound rules out requiring a total effective quotient
with decidable exact selected-event reachability over an envelope encoding
arbitrary Turing-machine runs: a designated event iff halt would decide the
halting problem. Frozen Yulang features make the encoding plausible, but the
candidate machine lacks recursive/list/enum typing rules, and a resource-
bounded envelope may exclude it. This does not obstruct conservative
principality and is not a class-3 result. Next derive an effective
conservative effect abstraction that retains soundness and principal
projection without requiring exact trace/event reachability. The new
`2026-10-02-finite-abstract-safety-presentation.md` constructs that generic
alternative: finite address/store graphs and a maximal safe assignment domain
with minimal joint observations. Its source refinement, finite symbolic basis,
modular future-use coverage, and acceptance bridge remain open. Possible
spurious rejections are disclosed, not approved.

## Current work

The milestone-1 candidate is `notes/design/2026-10-02-ordinary-computation-semantics-package.md`. It defines one state-threaded `Run` relation, concrete closure-frame re-entry under the current caller store/activations, latent `Force`, per-event origins and symbolic `K,D`, event-relevant ordered visibility, and shallow handler images. The user selected preservation of existing callback incidence while its receiver is active, ordinary current-handler search after escape, and concrete typed-boundary visibility for both direct and Force-exposed requests. `Force` exposes latent computation but creates no authority; origin and `K,D` remain event-specific.

The ordinary-computation package received a bundled architect/compiler-referee/spec-auditor review and a focused closure delta review. It repaired event-specific callback relevance, ordinary receiver-body handling, actual post-application `C_h` and current-boundary checks, closure re-entry, and the suspended invocation wrapper across handler unwind. The user selected concrete typed-boundary visibility for direct and Force-exposed requests; its delta review found no major issue. The exact semantic embedding has been package-reviewed: initial `R`, primitive source-rule images, latent future-use, and typed resumptions are covered; finite-resumption bind lifting was separately reviewed. Milestone 2 is closed for the candidate machine, not for the current Yulang typing relation.

For Milestone 3, the earlier conditional finite guarded-saturation theorem
and exact-acceptance route remain valid. On that route, invented selected
arms cannot be counted as actual source obligations. The new conservative
certificate package instead declares its abstract derivation judgment and
proves its principal interface. It supplies a generic finite heap construction,
not yet the complete source refinement or a selected successor acceptance
policy. Package review repaired the safety theorem's error-reflection
quantifiers; independent delta review is clean.

The source-realization package now constructs the predicate basis from a
finite monomorphic ownership/descriptor graph, with all query-schema endpoint
products retained symbolically. Its operational kernel gives conditional
heap simulation; explicit selected-pair observations give universal
selected-incompatibility reflection. Independent semantic and conformance
package reviews are clean within that conditional envelope. This does not
construct elaboration from raw source. The exact source gaps are inductive
callback-boundary relevance/visibility and effective general adapter
descriptors; neither may be hidden in an oracle primitive. The further
interaction gap is uniformity: a finite presentation for every separately
linked finite client does not establish one component presentation for all
admissible future clients. Close those source and modular definitions before
the source typing/acceptance bridge and lifecycle theorem.

Finite presentation need not be uniformly small; resource overflow may be a
distinct deterministic inference-complexity failure. Full-source class 1/2
remain unproved, and no class-3 counterexample is established. The old rule
making `UnknownOrigin` independently block a drop is superseded: origin
uncertainty alone cannot veto a concrete capture contract when complete
`CallView`, exact operation coverage, and active receiver-local handling are
established. Do not begin lifecycle proof against an undefined representation.

Implementation feasibility evidence is recorded in `notes/progress/2026-10-02-successor-implementation-feasibility.md`: resolved HIR lacks calls/handlers/`Force`, effect views cannot carry nonempty symbolic payloads, and runtime execution surfaces are absent. Do not prototype before the semantic carrier and required compiler surfaces are established. Use Rust for any later executable characterization; do not use Python.

## Main records

- `notes/design/2026-10-02-source-realization-and-symbolic-basis.md` — finite ownership inventory, conditional operational realization, selected-fault reflection, and exact remaining source definitions.
- `notes/design/2026-10-02-finite-abstract-safety-presentation.md` — reviewed generic finite carrier and principal certificate theorem; source application open.
- `notes/progress/2026-10-02-finite-interface-obstruction.md` — classification, lower bound, construction progress, and review record.
- `notes/design/2026-10-02-ordinary-computation-semantics-package.md` — current milestone-1 theorem package.
- `notes/design/2026-10-01-coupled-effect-interface-core-draft.md` — relational carrier and prior derivations.
- `notes/progress/2026-10-02-callback-scope-transition.md` — callback/escape evidence and decisions.
- `notes/progress/2026-10-02-successor-implementation-feasibility.md` — alternating feasibility audits.
- `notes/design/INDEX.md` — design status and authority map.
