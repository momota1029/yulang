# R224 constraining proof — exact authority stop

- Sprint/contract: R224, revision 1, `tasks/agent-loop/sprints/paper-constrain-soundness-r224.md`, SHA-256 `5c1a2f68200e5d291096ff3634f1fe337dec71ecde2a101eacbfdf0911a1543a`.
- Assignment/handoff: `r224_constraining_proof`, revision 1.
- Baseline supplied by contract: `7a4e25417a2794d3d19e9cb128060ad240d2b255`, branch `yulang3`; no Git command executed by this leaf.
- Worker: `/root/r224_constraining_proof`; current-session NEW_TASK and primary messages establish assignment. Actual model/effort telemetry: UNKNOWN.
- Outcome: **authority/equation blocker; no theorem constructed**. This is neither a mathematical impossibility result nor a source-qualified counterexample.
- Exact leases: `notes/theory/lean/YulangClosure/AbstractConstrainSoundnessR224.lean` and this handoff. Only this handoff was created. The Lean module was not created.
- Authors: this leaf only; no descendants. Luna owns execution, caches, integration and independent-review appointment.

## Original claim and paper equation

Original parents are the unchanged `YulangClosure.SourceProblem.InferenceSoundness`, `SourceScopedCoverage`, `PrincipalCoverage`, and `InferenceTermination` in `Contracts.lean:128–154`. In particular, soundness quantifies over every supported source `s`, original scope `x`, generated constraint `d` and solution `a`, and requires one witness `e` satisfying both `sourceJudgment s x e` and `sameScoped s x e a`. Principal coverage retains its original instance ordering and every original source witness. No premise or source domain was changed.

Original A/B scope: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`, §§1,3,5; apply `notes/design/2026-10-24-birth-level-scc-intrusion.md`, §§2–6. Immutable Value births and birth-level induced-reference SCC qualification remain distinct from type-bound SCC normalization. Shared source witnesses, original scopes, complete Call, annotations, hygiene, publication and lawful uses remain required.

Parreaux, *The Simple Essence of Algebraic Subtyping*, local PDF SHA-256 `5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698`, §5.3.1 Lemma 2 (printed p.124:27), requires:

```text
consistent(σ) ∧ constrain(st0,st1) σ ⇓σ' ()
  ⇒ consistent(σ') ∧ E^-_σ'[st0] ≤ E^+_σ'[st1].
```

This is a schematic transcription, not an existing Lean theorem type. The paper's proof sketch requires a stronger induction relating the comparison cache to delayed subtyping hypotheses, preserving existing coalesced inequalities and allowing temporary inconsistency precisely for cached variables. §3.2.2 requires cache insertion before dispatch, bound insertion before opposite-bound replay, and a snapshot of the traversed bound list. §5.1.2 permits `μ α.α` but unlocks delayed hypotheses only across Function/Record, not recursive unfolding or lattice rules. §5.2 distinguishes mutable-bound execution from coalescing. Figures 11–12 fix polar recursive binder identities; §5's introduction/footnote 15 limits its printed proof sketch to the non-let extension.

## Sourced fragment equations and their exact scope

These definitions fix useful structural equations. Their existence is not the blocker, and they have not been refuted.

| Existing owner | Equation already fixed | Scope boundary |
| --- | --- | --- |
| `SimpleSubConstraintSyntax.lean:101`, `YulangClosure.SimpleSub.Sub.function` | `Sub a' a → Sub ae' ae → Sub re re' → Sub r r' → Sub (function a ae re r) (function a' ae' re' r')` | Independent structural algebra over finite `Term`, not accepted joint Function descriptor resolution. |
| Same file, `Sub.recordCons`, `Sub.tupleCons`, `Sub.variantCons`, lines 104–111 | Covariant fields/tails, tuple heads/tails and variant payloads/tails; record label/optional bit and variant tag agree exactly. | Exact retained metadata; no completeness claim for optional-row admission or arbitrary source boundaries. |
| `SimpleSubConstraintSoundness.lean:190`, `YulangClosure.SimpleSub.Step.function` | Replace a Function demand by the ordered clauses `(a',a)`, `(ae',ae)`, `(re,re')`, `(r,r')`, with kinds Value, Effect, Effect, Value. | Backward constraint reflection; not successful-run consistency or a native acceptance equation. |
| `SimpleSubRegularSolutions.lean:142–170`, `YulangClosure.SimpleSub.Regular.recordPairs`, `variantPairs`, `expandNodes` | Same four Function clauses; exact record labels/optionality, tuple arity/order, variant tags/payload arity. | Independent regular graph interpretation. |
| `SimpleSubLatticeCertificates.lean:156–158,208–213`, `YulangClosure.SimpleSub.Lattice.Layer.structural`, `Approx`, `RegularSub` | Only structural expansion consumes the recursive relation; lattice/transitivity proofs stay at the same layer. | This provides graph-layer guard behavior; it does not identify a graph interpretation with accepted source semantics or direct recursive coalescing. |

`YulangClosure.SimpleSub.AbstractCore.CoreState.insertPendingUpper` is a partial same-level insertion/replay function; `CoreState` has no comparison-cache field or full `CoreRun`. `CoreCoalesced` retains both kinds, free names and named polar recursive binders. Its `toTerm` explicitly rejects bound occurrences. Missing a named recursive judgment or substitution function alone would be a construction task, not evidence of absent semantic authority. The paper fixes the ordinary mathematical unfolding scheme; no claim is made here that named-binder substitution is impossible. R223 likewise explicitly disclaims recursive-Fig.12 equivalence and complete accepted runs.

## First actual semantic boundary: the Function effect equation

Governing source: `notes/design/2026-10-03-concrete-compatibility-boundary.md`, SHA-256 `5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16`, §1. Its header (lines 3–14) distinguishes the Draft full calculus from explicitly recorded user decisions. Only those selected directions are relied on here; its research constructions are not adopted as authority.

- Lines 40–49: Function effects are not independent general-Type subtype checks; the polarities use effect descriptors.
- Lines 101–118: compare both descriptors jointly within the same inequality, under existing shared assignment, family/incidence and `K,D` evidence; do not duplicate the carriers or decompose a port as an unrelated Type inequality.
- Lines 133–159: the missing integration maps effect components to the complete interface under the same `ν`, preserving occurrence incidence, directed evidence and residual meaning. The old effect calculus alone does not supply this theorem.
- Lines 161–190: the intended case is `Fun(a,never,b,c) <: Fun(a,d,[b,d],c)` with the SAME `d` at both target positions and **no independent `d <: never` obligation**; no broader four-field rule is approved. Effect-position `never` must not be assigned a new bottom/empty/sentinel meaning.

The candidate direct lift of `Step.function`/`expandNodes` would generate an independent argument-effect comparison `ae' <: ae`. Applied syntactically to the selected case, that would demand exactly the independent `d <: never` comparison the governing decision excludes. No execution or formal refutation of this source example is claimed: source descriptor elaboration into `Term .effect` is itself missing. The discrepancy is sufficient to prevent treating the structural fragment rule as the accepted whole Function transition.

The first missing equation is therefore the operational clause for

```text
constrainFunction(F0,F1,σ,cache)
```

that resolves the two effect descriptors jointly under the SAME assignment/source owners, retains the value comparisons `a' <: a` and `r <: r'`, and specifies its actual state, residual and cache effects. It cannot be filled by the unconditional sequence `constrain(ae',ae); constrain(re,re')`. The associated preservation statement must use the existing source-supported descriptor/carrier interpretation, rather than inventing a new effect relation or making success depend on the desired consistency conclusion.

**Owner:** Luna's Function source/effect-descriptor integration authority, using §1's component-to-existing-carrier bridge and approved role/source elaboration. The leaf has no authority to choose a replacement descriptor semantics. This is the first authority seam; no recursive constructor unlock policy is newly selected.

The top-level inference principles §§1–3 require proof-derived ordinary Simple-sub operations but do not override this joint comparison decision. The annotation policy (`2026-10-10-annotation-effect-hygiene-integration.md`, §§1–1.2) separates permission, actual inflow and residual and retains unknown symbolic dependencies; the directional Function-upper correction (`2026-10-06-directional-inferred-effect-protection-addendum.md`, §§1–2.2) retains upper-use provenance without back-protecting provider lowers. Neither supplies the missing joint comparison equation. The operational/source manuscripts are research constructions, not authority to replace it; their opening correction notices and explicit roll/unroll syntax do not repair this boundary.

## Extrusion, intrusion, publication and parent application

- Extrusion: `extrudeTerm`, `extrudeCopies`, `extrusion_directed` and `Step.extrudeUpper/Lower` retain both kinds and all four polar ports. Their supplied link/terminal-valuation premises remain; they do not establish successful-run consistency or contextual effect admission.
- Intrusion: `Occurrence.Qualifies` and `Step.intrude` use actual retained pairs and immutable-birth induced-reference qualification. R223 normalizes a different variable-bound graph. No source-scoped joint lift is inferred from either.
- Publication/use: `CorePublication`, `CoreUse` and requests are storage; the missing operational publication/use and coherent freshening bridges remain. Nothing here identifies a partial `CoreState` with accepted execution.

No auxiliary lemma was delivered to apply to the parents. **Parent delta 0; original roots 0/4; packages 0/5.** First remaining premise for this packet is the joint Function transition/component interpretation above, owned by Luna's source/effect integration. After it is fixed, cache-sensitive consistency, coalesced inequality, actual full-run integration and source/native correspondence still require construction and review. No supported constructor, method-selection case, optional field, Call/effect behavior or shared witness was removed from the parent.

## Dependency pins and actual execution evidence

All revision-1 direct source hashes were rechecked with `sha256sum` immediately before writing this handoff; exit 0, all matched:

| File | SHA-256 |
| --- | --- |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `SimpleSubConstraintSoundness.lean` | `33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293` |
| `AbstractSimpleSubCore.lean` | `023635d283f9a00e906ec965a6eaa5595eab21f2b93f353a1d5ea0ede0bffb6c` |
| `AbstractBoundCycleNormalizationR223.lean` | `65335f3b8c6834e1e1cd34429a8fd7330162648a62d532c3a45f44305b255aee` |
| `SimpleSubLatticeCertificates.lean` | `55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b` |
| Additional inspected `SimpleSubRegularSolutions.lean` | `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29` |
| Additional inspected `PaperTypeSubstitution.lean` | `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861` |

Pinned files read: `lean-toolchain` = `leanprover/lean4:v4.35.0`; `lakefile.toml` retains `-j1 -M1024`; manifest has no external packages. Actual Lean/Lake versions: **NOT RUN**, by Luna's sole-verification-owner instruction. No installation, version invocation, build, checker, tests, `#check` or `#print axioms` invocation occurred. Delivered theorem names/types: **none**. Axiom results: **NOT RUN / no delivered theorem**, not an empty-axiom claim. Existing theorem signatures above were read from source, not freshly printed or kernel-checked by this leaf.

Actual read commands included `cat`, focused `sed`, `rg`/`rg --files`, `nl -ba`, `sha256sum`, and `pdftotext -layout /home/momota1029/rust/simple-sub-reference-paper.pdf -` piped to focused section reads; these produced no scratch files. A discovery `rg` also named nonexistent `spec/` and exited 2; subsequent focused searches omitted it. That search failure is not proof evidence. PDF extraction and dependency hashing exited 0. No mathematical checker failure was observed, because none was run.

Resource use: read-only source inspection plus this handoff; zero Lean/Lake/Cargo processes, zero Astra work, zero cache/generated/scratch writes and no child agents. Wall time was not instrumented as a separate budget counter; construction stopped at the first established authority seam before the 4,200-second bound. No budget reset or additional packet is requested by this leaf.

## Stop and exact handoff

Primary instructed theorem-construction pause, then explicitly instructed freezing this revision-1 stop without a Lean module/build. This handoff is the only authored output. **Writes stop immediately after its final hash receipt; no background process or descendant exists.** No shared task/status/index, compiler, tests, root imports, configuration, toolchain or dependency files were edited. No Git operation occurred.

Stable request: `R224-JOINT-FUNCTION-CONSTRAIN-1`. Required input from Luna: an approved/source-derived joint Function effect-descriptor transition and component interpretation under the original shared assignment, including cache/state effects. Proposed next output requires a primary packet/version decision; this handoff grants no new lease. Falsifier for a proposed repair: it recreates the forbidden independent `d <: never` obligation, changes the same target `d` between ports, detaches original contribution/owner evidence, or presumes its consistency theorem. Independent review and integration remain pending; the leaf does not certify its own stop analysis.
