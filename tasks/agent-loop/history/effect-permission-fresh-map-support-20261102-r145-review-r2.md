# R145 fresh independent review R2

Reviewer: `/root/r145_fresh_map_review2`
Baseline: `f634b2f426b6aef3e2dd602dab0a6dce3e1ad0dd`
Observed runtime model/effort: **UNKNOWN**

**Verdict: ACCEPT as an explicitly unchecked, conditional research checkpoint. Source application and parent closure remain OPEN.** No concrete reachable source collision, inconsistent map, or uncovered production caller was established. No major correctness defect was found in the candidate's stated finite-support proposition by inspection. This is not kernel acceptance.

The reviewer returned the complete receipt in its final runtime message because its read-only role prohibited file writes. After the reviewer stopped, the primary transcribed that text here without changing the verdict or findings. The initial R145 reviewer receipt remains a separate `NO_VERDICT` boundary-deviation record and is not acceptance evidence.

## Input authentication and isolation

The amended contract was read first. All six hashes were computed and matched before source inspection:

| Frozen input | SHA-256 |
| --- | --- |
| Amended sprint contract | `283bf739e6eab63c2ab2a538137bc8114e3e1613d7565a353925d63eb63beb32` |
| Amended admission | `d4995672266e83f15adac2cb396a11d2b2987ee7d78425ea983627a9f6978d7e` |
| Source handoff | `e543b1cd4c6d98d6fdaf912f228a8cd53e407fe72edf3338b2f1c9fca295ffba` |
| Proof handoff | `da15341b46d3b7adef8cb1bd90d02bfe6dd27fc594a5fb96520f5cf84f82dcea` |
| Lean candidate | `d47da744694beb04abfcf3b06137b5a04b241f568490af5fbf59147933a2db57` |
| Initial no-verdict deviation receipt | `3c35bd548637eb5c8792c5da0b6607540aeb029ca28acdc011645c6b09ab9adf` |

The deviation receipt was hashed but its contents and conclusions were not read. Source was independently inspected before reading the author handoffs. All compiler source searches and reads used baseline-qualified Git objects. Dirty `candidate_scheme.rs` working-tree bytes and other quarantined paths were not inspected. No input-boundary violation occurred.

## Independent source assessment

This submission investigates the owning allocation/transport boundary; it supplies no production repair. The first unresolved cause is the source-to-native support/state correspondence, not a demonstrated downstream symptom requiring a guard.

At baseline `candidate_source.rs:296–357`, a successful `ScopeInventory::fresh` call allocates scope and input identities by their respective vector lengths immediately before append (`334–342`). Let their lengths on entry be `Cs` and `Ct`. The final map keys are the scope/input keys visited through `owned`; copied images lie in the append intervals beginning at `Cs` and `Ct`. Unmapped identifiers use identity fallback. Region identity reservation precedes copying (`318–319`). `scope_origins` records ancestry; its equality provides no injectivity evidence.

At `candidate_scheme.rs:4447–4450`, `begin_use` precedes exactly one `fresh` call. That returned map is reused for transformer keys, transformer guard/stamped tags, and demand `output_scope`/`input` at `4773–4796`. Demand roots use the reconstructed terms table; `use_instance` changes only when the original input is in the copied domain. There is no second scope/input map between these coordinates.

Repeated bounds for a parent reuse `FreshUse.scoped_relations`. `begin_candidate_fresh_bound` passes that retained flow to the FreshUse transport constructor (`candidate_scheme.rs:4888–4907`; `candidate_context.rs:4697–4709`). Replay composes existing transformers and carries the upper demand (`candidate_context.rs:4463–4467`); it does not allocate another map there. Local execution retains its prepared FreshUse across subsequent owner steps (`candidate_scheme.rs:5214–5239`). Later preparations begin separate allocation intervals.

Baseline-qualified search across `crates` found two production call sites: `candidate_scheme.rs:4429` and `5216`. The remaining matches are tests.

Fallible preparation can advance inventory/use identities before returning an error. No completed FreshUse is returned by a failed preparation. Scratch restoration at `4405–4421` is not evidence of full identity restoration or safe retry. The Authoritative top-level principles §§4–5 permit safe termination/discard of an affected private attempt; full rollback is not a general correctness obligation. This review does not certify broader failure/publication safety.

## Findings and remaining gates

### Blocking for source application: actual incoming-state correspondence remains absent

**Locations:** `candidate_scheme.rs:4773–4796`; `candidate_context.rs:3280–3283`; `NativeScopeFreshMapR145.lean`, `StateSupported`, `evaluate_rename_on_support`, and `fresh_evaluate_on_support`.

The candidate conclusion evaluates the renamed transformer on the **same-map renamed incoming state**. FreshUse visibly remaps a transformer and demand; neither demand nor `use_instance` is a `NativeScopeTransformer.State`. The inspected native observation evaluates from empty inputs/protections. It does not identify a general incoming state or establish its transport.

Treating the conditional theorem as an established source FreshUse law would assume its state-side premise and omit the demand/use-instance correspondence. Closure requires identifying the actual state at the relevant source/native consumer, establishing its encoding and same-map rename, and separately proving the demand/root/use-instance correspondence needed for the scoped-flow claim. Alternatively retain this gate OPEN, as both handoffs already do. This blocks theorem application/promotion, not acceptance of the honest conditional checkpoint.

The governing `notes/theory/2026-10-15-compose-scoped-release-construction.md:165–170,223–228` requires joint renaming of transformer and relevant incoming-state identifiers and explicitly leaves caller construction open. The Authoritative compose decision requires preservation of independent protection scopes.

### Blocking for source application: joint support bounds are not authenticated

**Locations:** `candidate_source.rs:296–342`; `candidate_scheme.rs:4783–4791`; `candidate_scope.rs:214–260`; candidate `fresh_evaluate_on_support`.

Append allocation establishes separation from identifiers **below the pre-copy counts**. `ScopeTransformer::remap` checks collisions only in its own support. Neither that local check nor the inspected FreshUse loop independently certifies every transformer, demand and incoming-state identifier against the same pre-copy bounds.

Using only copied-domain membership or transformer-only injectivity would omit external active identifiers. No reachable offending source construction was established. Closure requires establishing allocator validity across initial demand/release constructors, FunctionPort conversion, composition/replay, previous copies and relevant failure histories, then bounding the complete union at this call's entry cut. Inspected locations include `candidate_context.rs:3820–3832,3964–3975,4463–4467`. The handoffs correctly retain this as source-owned work.

### Minor: copied-key uniqueness is stronger than the allocation lemma needs

The source handoff lists uniqueness of copied scope/input keys with the source premise. This is unnecessary for injectivity of the successful overwrite-or-identity projection on old identifiers. Baseline `NativeFreshScopeTransport.lean:48–55,67–117` models repeated-key overwrite and proves old-range injectivity without uniqueness of the copy-key list. Qualify uniqueness as an ownership/iteration correspondence obligation where needed, rather than a prerequisite of that injectivity theorem. The proof handoff already records this correction, so it does not block checkpoint acceptance.

## Proof assessment

The candidate preserves universal finite `Transformer`/`State` quantification. `TransformerSupported` includes stamped tags, every scope-entry key and every missing-guard tag. `StateSupported` includes all incoming inputs and protections. These premises cover the union required by membership lookup, default entries and conditional additions.

The local membership, entry lookup and missing-guard arguments appear mathematically consistent by inspection. The main proof covers inherited and newly introduced protections and observes arbitrary output identifiers. The specialization derives support injection from `fresh_injective_on_old`; it does not assume global injection or source validity. Duplicate copy keys remain permitted.

The theorem does not establish demand semantics, Rust normalization/loop refinement, fallible execution, source attribution, or whole-language A/B closure. Those exclusions agree with its header and proof handoff.

## Tests and evidence limits

Relevant baseline tests were read, not executed:

- `candidate_scope.rs:458–484`: finite rename/evaluate examples, with empty incoming protections.
- `candidate_scope.rs:488–523`: separate collision rejection and one closure call per distinct transformer-support ID.
- `candidate_source.rs:2643–2689,2694–2735`: copied demand identity/ownership and distinct repeated uses.

These are finite discriminators, not proof of joint support validity over all source histories. Origin equality in those tests was not used as injectivity evidence.

No Lean, Lake, Cargo, Rust, tests, builds, checker, scratch/cache, environment creation, worktree, Git mutation or file write occurred during independent review. Kernel checking, actual inferred declaration types and complete axiom audits remain **NOT_RUN / UNKNOWN**. No source refinement, production readiness, semantic change or parent-theorem closure is certified.

**STOPPED. No writes or further inspection remain active.**
