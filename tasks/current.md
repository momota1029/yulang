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
| 3. Finite symbolic presentation | Conditional finite guarded-saturation theorem established for fixed finite complete-state quotient `Q` and predicate basis `P`; source construction and principal projection remain open | Construct `Q`, prove generated predicates/handler guards stay in `P`, preserve actual ordered-selection admissibility and joint `K,D` fibers, then prove least representable interface |
| 4. Generalization, fresh instantiation, SCC intrusion | Waiting on a Milestone-3 presentation | Prove lifecycle transport for that presentation, including external uses, internal SCC sharing, parent ports, and symbolic effects |
| 5. Implementation feasibility | Deferred until milestone 4 determines required surfaces | Targeted architecture/resource audit of the reviewed semantics and representation |
| 6. Implementation | Not authorized | Explicit user-approved design, completed required gates, implementation and verification |

## Current work

The milestone-1 candidate is `notes/design/2026-10-02-ordinary-computation-semantics-package.md`. It defines one state-threaded `Run` relation, concrete closure-frame re-entry under the current caller store/activations, latent `Force`, per-event origins and symbolic `K,D`, event-relevant ordered visibility, and shallow handler images. The user selected preservation of existing callback incidence while its receiver is active, ordinary current-handler search after escape, and concrete typed-boundary visibility for both direct and Force-exposed requests. `Force` exposes latent computation but creates no authority; origin and `K,D` remain event-specific.

The ordinary-computation package received a bundled architect/compiler-referee/spec-auditor review and a focused closure delta review. It repaired event-specific callback relevance, ordinary receiver-body handling, actual post-application `C_h` and current-boundary checks, closure re-entry, and the suspended invocation wrapper across handler unwind. The user selected concrete typed-boundary visibility for direct and Force-exposed requests; its delta review found no major issue. The exact semantic embedding has been package-reviewed: initial `R`, primitive source-rule images, latent future-use, and typed resumptions are covered; finite-resumption bind lifting was separately reviewed. Milestone 2 is closed for the candidate machine, not for the current Yulang typing relation. For Milestone 3, a compiler-referee-reviewed conditional theorem now gives finite guarded saturation for any fixed finite complete-state quotient `Q` and predicate basis `P`, with at most `|Q|` reachability rounds. The remaining construction is to derive such `Q/P` and exact transition guards from the source machine while preserving actual ordered-selection admissibility, latent/resumption behavior, and joint `K,D` fibers, then prove principal projection. The older support and point-row candidates do not do this. The old candidate rule making `UnknownOrigin` independently block a drop is superseded: origin uncertainty alone cannot veto a concrete capture contract when complete `CallView`, exact operation coverage, and active receiver-local handling are established. Do not begin lifecycle proof against a representation that is not defined.

Implementation feasibility evidence is recorded in `notes/progress/2026-10-02-successor-implementation-feasibility.md`: resolved HIR lacks calls/handlers/`Force`, effect views cannot carry nonempty symbolic payloads, and runtime execution surfaces are absent. Do not prototype before the semantic carrier and required compiler surfaces are established. Use Rust for any later executable characterization; do not use Python.

## Main records

- `notes/design/2026-10-02-ordinary-computation-semantics-package.md` — current milestone-1 theorem package.
- `notes/design/2026-10-01-coupled-effect-interface-core-draft.md` — relational carrier and prior derivations.
- `notes/progress/2026-10-02-callback-scope-transition.md` — callback/escape evidence and decisions.
- `notes/progress/2026-10-02-successor-implementation-feasibility.md` — alternating feasibility audits.
- `notes/design/INDEX.md` — design status and authority map.
