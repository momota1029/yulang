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
| 1. Coherent ordinary computation semantics for calls, closures, `Force`, requests, callback visibility, and shallow handlers | Ordinary caller-after-escape consequence closed relative to active-sequence dispatch; receiver-local caller-owned-`Force` capture scope remains unselected; candidate lexical ownership rule drafted | Select and review the joint source rule for binder lookup/instantiation and callback `Force`, then freeze the ordinary source machine without reopening escape micro-cases |
| 2. Source-to-complete-interface adequacy/simulation | One conditional theorem package reviewed; Yulang instantiation not certified | Instantiate the forward-simulation relation for the selected source rules, proving primitive coverage, typed future-use/resumption preservation, and joint `K,D` under one assignment |
| 3. Finite symbolic presentation | Not started | Constructive presentation with soundness and principality, or one precise obstruction and its accepted consequence |
| 4. Generalization, fresh instantiation, SCC intrusion | Not started | Preservation theorem for the finite presentation, including external uses, internal SCC sharing, parent ports, and symbolic effects |
| 5. Implementation feasibility | Deferred until milestone 4 determines required surfaces | Targeted architecture/resource audit of the reviewed semantics and representation |
| 6. Implementation | Not authorized | Explicit user-approved design, completed required gates, implementation and verification |

## Current work

The milestone-1 candidate is `notes/design/2026-10-02-ordinary-computation-semantics-package.md`. It defines one state-threaded `Run` relation, closure application under the current caller configuration, latent `Force`, per-event request origins and symbolic `K,D`, candidate-specific ordered visibility, callback `Capture` as a call-view projection, and shallow handler images. It derives ordinary caller handling for an escaped closure relative to those rules. Its complete source adequacy and boundary-path correspondence remain unproved.

The ordinary-computation package received one bundled architect/compiler-referee/spec-auditor review. Its missing ordinary caller path is now stated as active-sequence search after receiver unwind; operation application constructs a thunk and source-demanded `Force` emits the request. The escaped-callback caller-search consequence is closed relative to that machine rule. The receiver-local caller-owned-`Force` capture choice remains open. A policy-parametric source/interface simulation theorem is drafted in `notes/design/2026-10-02-source-interface-adequacy-theorem.md`. A second bundled architect/compiler-referee/spec-auditor review found no residual issue in the conditional theorem after requiring explicit forward coverage, universal typed future-use for latent values, and typed admissible resumption/store preservation. This review certifies only the conditional proof shape, not its Yulang premises. The theorem exposes operation-binder ownership as a source-semantics choice; the new lexical-substitution candidate is recorded in §6, pending user approval and source-rule review. Do not restart fixture-level cycles; freeze the ordinary source package, then discharge the actual primitive-simulation premises before claiming milestone 2.

Implementation feasibility evidence is recorded in `notes/progress/2026-10-02-successor-implementation-feasibility.md`: resolved HIR lacks calls/handlers/`Force`, effect views cannot carry nonempty symbolic payloads, and runtime execution surfaces are absent. Do not prototype before the semantic carrier and required compiler surfaces are established. Use Rust for any later executable characterization; do not use Python.

## Main records

- `notes/design/2026-10-02-ordinary-computation-semantics-package.md` — current milestone-1 theorem package.
- `notes/design/2026-10-01-coupled-effect-interface-core-draft.md` — relational carrier and prior derivations.
- `notes/progress/2026-10-02-callback-scope-transition.md` — callback/escape evidence and decisions.
- `notes/progress/2026-10-02-successor-implementation-feasibility.md` — alternating feasibility audits.
- `notes/design/INDEX.md` — design status and authority map.
