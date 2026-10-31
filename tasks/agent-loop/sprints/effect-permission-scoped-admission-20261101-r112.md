# EFFECT-PERMISSION-SOURCE-SCOPED-ADMISSION/20261101-R112

Status: admitted bounded continuation under the user's ongoing Rust/Lean soundness and effect-hygiene goal. R111 is closed with reviewed source candidates but no source integration. This sprint resumes the unchanged parent; it does not relax its claim or semantics.

## Original parent and fixed outcome

Parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5, retaining every supported source, lawful finite history and qualified extrusion, with one lawful joint strategy at original scopes. Current qualification is the immutable Value-birth-level SCC rule in `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. Effect hygiene and whole-language `SourceProblem.InferenceSoundness` remain OPEN.

R112 answers one parent premise: do the actual original App and Lambda `Judgment` derivations supply the source-scoped ViewLogic/EventProof payloads and dependency telescopes needed by the existing equality-lift / shared-strategy argument? Prove the strongest conclusion justified by existing definitions and source laws, or exhibit the exact missing admission/transport law with a discriminating formal obstruction. Preserve App annotation alternatives, Lambda Value/Computation entry modes, arbitrary source operands/pattern/body, all original event/execution quantifiers, and the common witnesses. Do not encode the conclusion into `LocalAdmissions`, strengthen assumptions silently, or treat arbitrary `LocalAdmissions.logical` as a concrete source instance.

## Governing meaning and frozen inputs

Original source authority: `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3.3, 5.2, plus the source-manuscript correction and §3/§5.2 references recorded by the R103/R105 handoffs. ViewLogic stays in its source description region; EventProof stays beneath its actual event and retains that event's telescope. The original scope/dependency order and one shared strategy remain fixed.

Lean input pins (SHA-256):

- `OriginalSourceGeneration.lean` `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- `OriginalSourceEnvironment.lean` `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`
- `OriginalSourceEvents.lean` `cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342`
- `OriginalSourceChecking.lean` `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6`
- `OriginalFormalAdmission.lean` `77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c`
- `OriginalCheckingAdmission.lean` `77a8dd74f5913814d3628f0aed189be24b4aafc4780839eaa57237676a157da7`
- `OriginalSourceClosure.lean` `e39f165848c512830e6f92893c61e2d9f07cec66b729e8878c5f7d3491ab429a`
- `OriginalEffectHygiene.lean` `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f`
- `SourceLogicalOccurrencesR104.lean` `0e7a42d66578388585a5abd1da12c77a9d7d46823687ed511d26e359b3078f39`
- `SourceLogicalOwnerBridgeR105.lean` `6fecc134ac2009392f043331eb4d1a3dd479668208991e60c8a5d339e69b45b4`
- Lean pin: `leanprover/lean4:v4.35.0`; no external Lake packages.

Rust correspondence baseline is immutable commit `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`; inspect only the assigned owners and source hashes cited in R111/R112 records. Current dirty source and quarantined paths are not inputs.

## Parallel lanes, exact leases, and budgets

1. Constructive proof lane, registered `lean_prover`: write only `notes/theory/lean/YulangClosure/SourceScopedAdmissionR112.lean` and `tasks/agent-loop/inbox/effect-permission-scoped-admission-r112-proof.md`. Inspect/invert the actual `Judgment` and selected checking/admission definitions. Deliver a candidate derivation or an exact missing law and countermodel; no `sorry`, axiom, circular typing/safety definition, strengthened hypotheses, or source narrowing.
2. Complementary Rust/source lane, `researcher`: write only `tasks/agent-loop/inbox/effect-permission-scoped-admission-r112-source.md`. Read immutable baseline owners `candidate_effect.rs::candidate_formal_annotation` and `candidate_receiver.rs::internal_formal_permission_incidence`; trace the actual occurrence/effect-constraint producer and permission-consumer seam against the Lean premise. No source edit, Cargo, fixture change, or claim of runtime execution.
3. Fresh independent `compiler_referee` review of the frozen proof and source handoff; exact source conformance, hypotheses, quantifiers, witness/telescope preservation, and the obstruction's limits. Reviewer is neither author nor coauthor.

Aggregate active budget: 1,200 seconds maximum (proof 480, source 180, review 180, Luna integration/reconciliation 360). Astra 0. No Cargo, Rust compiler, Lean/Lake/checker, build, test, installation, generated cache or environment experiment is admitted in R112. New proof material is CONSTRUCTED/UNCHECKED until a separately reviewed and resource-admissible kernel gate. Primary owns records and Git.

## Success, non-goals, and stop

Success is a strictly narrower original missing premise with a candidate conditional construction over already established laws, explicitly left UNCHECKED in this sprint, or a formal countermodel proving the current abstract admission interface is insufficient plus an exact source-owned law that could close the gap. A note, route identity, assumption list, or test does not satisfy this outcome. The Rust lane must identify an actionable source owner or state NO_SAFE_CODE_SLICE. These are distinct results; neither proves the whole parent.

No Rust implementation promotion, semantics decision, expected-output change, new law in the trusted kernel, root-import change, or production claim. Preserve the R103 failures, `sorryAx` audit, all existing A/B quantifiers, and source/UNKNOWN/quarantined paths. Stop on any required authority change, unavailable input, lease conflict, or proof requiring an unapproved law. The parent remains OPEN regardless of packet completion.
