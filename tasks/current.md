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
| 1. Coherent ordinary computation semantics for calls, closures, `Force`, requests, callback visibility, and shallow handlers | Escaped caller search and preservation of already-derived active callback incidence are selected; exact imported-`Force` incidence creation remains open. Ordinary-body handlers and current boundaries now have explicit event-relevance conditions | Resolve the single incidence-creation choice, then freeze the source machine; do not reopen settled escape cases or add callback micro-cases without a counterexample |
| 2. Source-to-complete-interface adequacy/simulation | Conditional theorem schema reviewed; reusable bind lifting lemma now closes return-after-resumption composition, but primitive coverage, initial `R`, and future-use/resumption realization remain unproved | Close the package-level simulation as one theorem under the selected source machine; retain imported-Force incidence creation as the one explicit source decision |
| 3. Finite symbolic presentation | Not started | Constructive presentation with soundness and principality, or one precise obstruction and its accepted consequence |
| 4. Generalization, fresh instantiation, SCC intrusion | Not started | Preservation theorem for the finite presentation, including external uses, internal SCC sharing, parent ports, and symbolic effects |
| 5. Implementation feasibility | Deferred until milestone 4 determines required surfaces | Targeted architecture/resource audit of the reviewed semantics and representation |
| 6. Implementation | Not authorized | Explicit user-approved design, completed required gates, implementation and verification |

## Current work

The milestone-1 candidate is `notes/design/2026-10-02-ordinary-computation-semantics-package.md`. It defines one state-threaded `Run` relation, concrete closure-frame re-entry under the current caller store/activations, latent `Force`, per-event origins and symbolic `K,D`, event-relevant ordered visibility, and shallow handler images. The user's decisions select preservation of an already-derived callback incidence while its receiver is active and ordinary current-handler search after escape. Whether Force of a caller-owned thunk creates a new incidence remains the one source-policy choice.

The ordinary-computation package received one bundled architect/compiler-referee/spec-auditor review and a focused closure delta review. The package review repaired event-specific callback relevance, ordinary receiver-body handling, actual post-application `C_h` and all applicable current-boundary checks, and closure re-entry. A suspended invocation keeps a re-entry wrapper through search unwind; resumption installs its call-frame occurrence before the saved suffix and removes exactly it on completion, preserving live store/lineage without restoring consumed shallow or maker handlers. Existing callback incidence and symbolic `K,D` are preserved while their activation premises hold. The imported-Force incidence-creation choice remains open as A (derive incidence from complete callback execution) versus B (transport only an already-derived incidence); escaped-caller behavior is settled independently. No more callback-specific review loop is planned. The adequacy theorem now has a reusable bind lifting lemma: a focused compiler-referee delta review closed the prior return-after-resumption gap by quantifying over all related returns reachable through finite admissible resumptions. This closes composition only; primitive forward-coverage, initial-`R`, and universal future-use/resumption realization remain unproved. After resolving the one source choice and discharging the theorem package, move directly to the finite constrained-interface presentation and soundness/principality proof.

Implementation feasibility evidence is recorded in `notes/progress/2026-10-02-successor-implementation-feasibility.md`: resolved HIR lacks calls/handlers/`Force`, effect views cannot carry nonempty symbolic payloads, and runtime execution surfaces are absent. Do not prototype before the semantic carrier and required compiler surfaces are established. Use Rust for any later executable characterization; do not use Python.

## Main records

- `notes/design/2026-10-02-ordinary-computation-semantics-package.md` — current milestone-1 theorem package.
- `notes/design/2026-10-01-coupled-effect-interface-core-draft.md` — relational carrier and prior derivations.
- `notes/progress/2026-10-02-callback-scope-transition.md` — callback/escape evidence and decisions.
- `notes/progress/2026-10-02-successor-implementation-feasibility.md` — alternating feasibility audits.
- `notes/design/INDEX.md` — design status and authority map.
