# NATIVE-FRESH-USE-VALIDATION/r1 — fresh independent review

Assignment: `/root/native_fresh_use_validation_review`, revision 1.
Disposition: **REJECT the frozen Rust validator as a successful validator submission. Retain the Lean construction only as partial/incomplete, unchecked research.** The bounded validator gate and every original parent/source/native/effect-hygiene/production gate remain OPEN.

## Authentication and independence

Contract `tasks/agent-loop/sprints/native-fresh-use-validation-20261028-r1.md` SHA-256 `fa16e84d3bd7cdb3c134bbc798c5bfd47e8af0686b80b961c7a8f49a692cf4f8` matched before either target source body was read.

Frozen Rust `isolated/native-fresh-use-validation-r1/crates/yu-solver/src/candidate_scheme.rs`: `6e0695e14895e4c9a0f44c6184586716780bdbdcdca8f52ff8663c2d4138101e`.
Frozen Lean `notes/theory/lean/YulangClosure/NativeFreshUseValidation.lean`: `951317b3617b0a399c1192291819f4dc61b4561ab80065e24c40a5c1e32a19a6`.
Rust handoff: `1f211733f9a193259a1726b8ffccc3d59709f0f75ace2fdd6378e97b9fff193c`.
Lean handoff: `1931a09044e462d73d60132b61cf237c610989a13a50b68937f069cc1866b0a6`.
All four matched assignment hashes. The complete Lean source, Rust validator, reconstruction owners, relevant existing test, and Rust delta were inspected before either handoff explanation. Handoffs were then compared with independently observed coverage; they were not evidence for initial correctness.

Read AGENTS.md and AGENTS.pre-sprint.md, design-authority rules, governing 2026-10-11 inference principles, sprint contract, goal-driven-sprints rules, current state and handoff protocol. Applied the yulang-lean-proofs skill for statement/source-correspondence review; its execution steps were excluded by the explicit reviewer no-execution assignment. Read original `SourceProblem.InferenceSoundness` at Contracts.lean:128, OriginalEffectHygiene's explicit scope boundary, and the native scope proof dependency. No source scope or theorem quantifier is changed by this review.

Actual SHA-256 authentication matched every direct dependency pin listed in the contract: candidate_effect, shadow_apply, term, candidate_context, candidate_source, lib, workspace Cargo.toml/lock, yu-solver Cargo.toml; NativeFreshScopeTransport, NativeScopeTransformer, Contracts, OriginalEffectHygiene; Lean toolchain, lakefile, manifest and README. The baseline candidate_scheme matched `33235b840c42be38be1df634291e309c0d143fa62f412afa633768be9b40aa0e`. No additional implementation dependency was introduced or used.

Requested role: fresh independent reviewer (current state names compiler_referee); requested model/effort: UNKNOWN in assignment/current state. Effective role/model/effort runtime metadata: UNKNOWN. No producer/coauthor work, children, tests, builds, Cargo, Lean/Lake, Git, or installations occurred. Exact sole write lease: this review file, explicitly assigned by the primary; current.json still displays its owner as `/root`, so central bookkeeping should reflect the delegated lease without changing review substance.

## Findings

### F1 — BLOCKING: unsupported retained maps silently pass

Locations: candidate_scheme.rs:4246–4444, especially final `Ok(())` at 4444; FreshUse fields at 593–614; actual construction/consumption at 4494–4498, 4621–4660 and 4790–4819.

The validator never reads `fresh.scoped_relations`, `fresh.context_use`, or `fresh.context_remap`. Starting with any otherwise accepted FreshUse, deleting/changing a scoped demand root, changing its transformer/output scope/input/use instance, substituting another context-use ID, or clearing/replacing context_remap leaves every executed check unchanged. These are successful validations of unsupported fields, despite the contract's complete-map requirement and explicit stop-on-missing-field rule. A wildcard-success arm is not necessary for opaque success: the unconditional end of this function has the same effect for omitted maps.

The Rust handoff discloses these omissions, but disclosure does not make the success value fail closed. Its assertion that a missing map entry fails is broader than the code supports. This targets an observational symptom without yet establishing the owning map construction/transport invariant.

Minimum closure: either implement independent domain/content checks for these maps and their dependent fields using captured construction evidence, or make the function return an explicit unsupported/incomplete outcome whenever such evidence is unavailable. Preserve a separate structural partial-check result if useful. Establish changed/deleted-map rejection with unchanged graph/interner observations before promoting the gate.

### F2 — major: provenance pattern is not ordinary stable Rust guard syntax

Location: candidate_scheme.rs:4298–4301.

The `if a.occurrence ...` appears inside the second tuple pattern, after `Operation(b)` and before the tuple's closing parenthesis. This is a nested guard-pattern position rather than a top-level match-arm guard. The crate has no guard-pattern feature enabled. Moving the guard outside the full OR-pattern alone also fails to solve the ownership of bindings: `a` and `b` are absent from the Annotation alternative. The added validator cannot be treated as an executable implementation on the strength of source inspection; this is a static language-syntax finding, not an observed compiler diagnostic.

Minimum closure: compare provenance with separate match arms for `(Annotation, Annotation)` and `(Operation(a), Operation(b))`, then obtain the primary-owned focused compilation result. No compilation was run by this reviewer.

### F3 — major: accepted effect views omit executable weight invariants

Locations: candidate_scheme.rs:4295–4303; candidate_effect.rs:360–368 and 1340–1377; candidate_context.rs:1735–1741 (`validate_payload_view`).

An accepted allowance/support/annotation-member compares owner, position, allowed members, tail and provenance, but neither `source_weight` nor `closed_weight`. Change the target view's source_weight to an unrelated/invalid weight, or change closed_weight inconsistently with its tail, and this validator observes no difference. The owning payload validator explicitly checks weight boundary, owner/position/allowed, source_weight identity and closed_weight/tail consistency; the proposed validator does not call or independently reconstruct that evidence.

This violates the contract's dependent-field/no-opaque-success boundary. The Rust handoff lists compared fields but does not explicitly identify these two omitted fields; the Lean handoff/header correctly identify them as unresolved. Thus the two outputs' limitations are not disclosed with equal precision.

Minimum closure: authenticate the source and target weight payloads and their relationship to the copied views/contexts, or reject this unsupported field case. Equality of the visible subset is insufficient.

### F4 — major: map key coverage and fresh scope allocation are not validated

Locations: candidate_scheme.rs:4251–4316 and 4423–4444; candidate_source.rs:296–350.

`effect_operands` requires entries at effect nodes but does not reject extra entries at ordinary or out-of-range node indexes. With scoped_experiment enabled, the scope check only visits owned regions and compares each region's scope/input lists with map entries. It does not reject extra map keys, check context-use freshness, establish fresh target allocation, or validate region parent/origin ownership. In particular an identity region/scope/input mapping to the source region satisfies these checks, although `ScopeInventory::fresh` allocates new regions/scopes/inputs. If the owned-region list is empty, arbitrary extra scope map entries are not inspected at all.

These counterexamples show why per-entry consistency does not establish the quantified whole-map invariant. The handoff does disclose incomplete allocation-history evidence, but its broad missing-entry/corruption claim needs narrowing.

Minimum closure: enforce exact key domains and identify independent allocation/ownership evidence for fresh target images; otherwise return incomplete for that part. This review does not require a whole-source allocation theorem from this bounded gate, but a validator cannot claim to validate a native fresh map while accepting arbitrary extra or identity images without qualification.

### F5 — major gate gap, honestly disclosed: required mutation evidence is absent

Locations: candidate_scheme.rs:6668–6669 and contract success evidence 3.

The only added test assertions invoke the validator on two unmodified FreshUse values in the existing Variant test. There are no mutation falsifiers for child, row/polarity, effect operand, scope or evidence maps. The handoff accurately states this omission. F1/F3/F4 demonstrate corruption classes that would survive rather than be rejected.

Minimum closure: after the checker semantics are complete, the assigned primary supplies the focused contract verification and preserved mutation results. Existing successful shape tests do not supply this evidence. No tests were added or run in this review.

## Constructor, theorem and circularity assessment

Rust ordinary Node coverage is explicit: Leaf handles all 13 Atoms (4317–4333); Row reads exact kind/ordinal/polarity through LiveVariable (4335–4342); Function checks four ordered handles and polarity (4344–4352); Tuple checks ordered slices (4354–4363); Record checks field name/optional/value order (4365–4379); Variant checks ordered tag/payload arity/handles (4380–4395). Shared child IDs are checked by handle equality. Missing child handles and slice overflow reject. Row allocation correctness is not independently established; the supplied shared row vector is the expected interpretation parameter. EffectOperand has its separate map and enforces a missing term slot, with payload limitations in F3. Rust also accepts BottomPositive/EmptyNegative/EffectRow effect-endpoint branches at 4273–4277 that prepare_candidate_fresh_use rejects at 4618; Lean operand rejects these at 172. They must not be described as identical accepted domains.

No circular `terms[graph.root] = terms[graph.root]` premise was found. Each ordinary node is checked against actual term readback, and all child slots are themselves checked against captured constructors. The return site at 4485 selects the checked slot. This is useful structural evidence, conditional on the native interner DAG and the supplied shared rows; it is not a complete-map/source-authentication proof.

Lean `interpret` at 202–204 uses captured graph/snapshot/rows; `observe` at 209–210 unfolds a separately supplied native reader. `validateObservation` at 323–327 requires two successful observations and compares their content; `none = none` cannot pass. The six authored theorem roots (329, 356, 372, 384, 393, 402) state comparison soundness, effect-node comparison, unresolved-map rejection and returned-root observation. Their exact premises agree with the proof handoff. `returnSite : retained graph.root = some returned` at 406 identifies the actual returned handle, not its desired interpretation; no desired root-image equation is smuggled into that premise.

However, nativeRead/effectRead/Snapshot/Allocation are parameters without an authenticated concrete Rust decoder. MapRecipe payloads and context source observations are not complete native remapping constructions. `validateMap_sound` proves a comparison property of one supplied recipe; it proves neither completeness of recipes nor that an actual Rust validator checks them. Tree unfolding does not establish native handle equality or DAG sharing. Lines 15–21 and the proof handoff disclose precisely these limits, including Contribution.instance and View/Context weight identities. BothFromRight rejects consistently with the native context discovery owner. No old scope transport theorem is applied under weakened validity hypotheses.

The Lean construction may therefore be retained **only as partial/incomplete**. Source inspection found no `sorry`, `admit`, project axiom declaration or kernel bypass in this module; that is not a transitive axiom audit or checker acceptance. All six roots remain UNCHECKED; complete printed theorem types and `#print axioms` results are NOT RUN/UNKNOWN. Neither a theorem declaration nor the imported Contracts proposition closes the original `∀ s x d a ... ∃ e` source obligation.

## Receipt and stop

Checks performed: read-only SHA-256 authentication, source/delta reading, governing-source/dependency/test inspection, and static counterexample traces above. No executable verification claim. No scratch/generated files or descendants.

Budget: 600 seconds granted; actual aggregate wall time/CPU/RSS not measured and UNKNOWN. One observed clock before writing: 2026-10-28 06:17:20 UTC. No heavy process budget consumed; no additional budget requested.

STOPPED: review complete; this is the only written file. Writes stop on this revision's submission. Frozen inputs remain untouched. Primary owns adjudication, central records and any resumed repair lease. Preserve the incomplete Lean artifact separately from acceptance of the rejected Rust success result.
