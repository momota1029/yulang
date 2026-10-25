# R59 proof handoff — revision 1, frozen candidate

Sprint-ID: PAPER-HEAP-OBSERVATION-20261026/r59, contract r1 SHA-256 `fd8913816e2ab6c6f3316f2be50125b148dab192aefc1de3b529644547604e21`.
Baseline: `4eb348f7ebf53509ae701c6b0434041a90f8f573`; isolated checkout `/tmp/yulang-r59-heap-observation`.
Worker: `/root/r59_heap_observation_proof`, registered lean_prover, session UNKNOWN; requested role defaults, observed model/effort UNKNOWN; sole author, no descendants. First precise active-work timestamp `2026-10-25T22:56:14Z`; earlier first tool timestamp unavailable. Conservatively charge from primary's sprint origin `2026-10-25T22:53:50Z` through freeze `2026-10-25T23:00:34.593651+00:00`: 404.594s, below 600s.

Outcome: kernel-accepted bounded represented proof candidate; fresh independent review PENDING. No source/native, full executor, inference A/B or production closure.

## Governing claim and mapping

Read root AGENTS.md / AGENTS.pre-sprint.md, goal-driven-sprints, proof skill and both source/execution references, exact frozen R59 contract, current snapshot and handoff protocol. The contract is absent from the isolated baseline; its primary-worktree copy was read and hash verified, without copying or changing it.

Original parent: `docs/yulang-operational-type-safety-ja.tex`, SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`: §§3/3.8, lines 252–326, 488–500; guard and graph-extension/value-shape argument lines 981–1010; execution-safety theorem `thm:safety`, lines 1139–1165. Its quantifiers cover arbitrary finite internal steps, typed external responses and multiple resumes from a closed well-typed graph/plan, preserving original result type and excluding Bad; infinite internal execution remains allowed. Read the opening source correction, original rec guard lines 183–191, type abstraction/application clauses lines 2046–2078, and corrected-core note CV1 §§1–3/V1(b), V2. That research note is context, not semantic authority. The operational manuscript names an older input hash `28dc9b...`; the available `docs/yulang-whole-language-semantics-ja.tex` has hash `6246e7dc179a795b372603eac8cd64bf783ba69e9a4a733bcfc012ebd6869612`, so no identity with the old named input is asserted.

Actual unchanged definitions read: `PaperValueTyped.graphReference`, `.delay`, `.typeAbstraction`, `.typeApplication`; `PaperComputationTyped.force`; `FreshHeap.lookupHeap`, `HeapPayloadTyped`, `allocate`, `finite_allocation`, `self_alias_payload`; `PaperTypeBetaExecution.typeBetaValue` / `.typeBetaValue_preservation`; `PaperCoreStep.step` / `.preservation`. R29 adjudication and R58 review boundaries retained.

Namespace: `YulangClosure.PaperTypes.PaperHeapObservation`.

- `ObservationStep`: exactly graphRead using actual first-match `lookupHeap`, accepted typeBeta, and recursive typeApplication function position. No evaluation under data, lambda, delay, type abstraction, metadata or type arguments.
- `ObservationTrace`: reflexive finite cons trace; no normal-form or termination assumption is hidden in its definition.
- `heapLookup_payloadTyped`: arbitrary d/g/e/heap/reference/payload/type, payload typing plus successful same-identity graph/heap lookups gives payload at precisely the reference's type. Private helper establishes actual selected pair membership; equality of successful graph lookups fixes the type.
- `observationStep_preservation`, `observationTrace_preservation`: arbitrary same d/g/e/heap/result type, payload typing, actual step/finite trace, and independent source value typing yield unchanged endpoint typing. Type-application position retains the same instantiated result type.
- `force_observation_preservation`: typed force source plus actual finite trace to delay body yields typed intermediate force(delay body), existing Force/Delay step equation, and body at original result type.
- `allocated_force_observation`: consumes every actual `finite_allocation` hypothesis (unique IDs, fresh graph and heap IDs, one shared typed substitution, typed RHS block and old payloads), then uses exactly `formals b ++ old` and `allocate b rho heap`; its force typing and trace are in those same objects, without independent witnesses.
- `selfAlias_observation_loop`: the R29 self-edge heap has payload typing, typed reference, a literal observation self-step and nonempty self-trace. It is a discriminator against inferring guard/termination from payload typing, not a counterexample to guarded manuscript safety.
- `duplicate_graph_firstMatch`, `heap_collision_firstMatch`, `mismatched_graph_type_excluded`, `nonRedex_typeBeta_excluded`: explicit first-match, type-equality and beta applicability boundaries.

## Exact evidence

All 18 contract input hashes matched at start and freeze. Full per-file hashes, 12-file direct/transitive source cone hashes and zero hole/bypass/project-axiom pattern matches are in checks. Dependency revisions unchanged.

Frozen paths / SHA-256:

- `notes/theory/lean/YulangClosure/PaperHeapObservation.lean`: `19b54b87b63cdc4175b1b641ca83d0c1e9454e2439c58a0936bf31fa5bc4725f`.
- `notes/theory/lean/.lake/R59Audit.lean`: `07327b553d9f51e1e5dcfc2e352cc72953c6e7bb943d819777ce4d9967f98aed`.
- `tasks/agent-loop/inbox/paper-heap-observation-r59-worker-checks.txt`: `b3847d011403975667bf2cbddb897c0934bf71912627d9200c035e51f946982a`.
- Dedicated `.lake/build`: 96 files; complete sorted `SHA256  relative-path` manifest in checks, manifest SHA-256 `b79a2fc5ed4abb0173b02df86286615cb09a6c15d7020aaa52aefa53f5977dab`.

Read-only `elan which lake` resolved `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake` (L below). Actual literal calls, all in `notes/theory/lean`:

1. `L --version`: exit 0, 0.769280s; Lake 5.0.0-src+eb6cafb, Lean 4.35.0.
2. `L env lean --version`: exit 0, 0.084125s; Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc.
3. `L build +YulangClosure.PaperHeapObservation`: exit 0, 36.370978s; 13 import/build jobs, no candidate warning. Existing dependency linter warnings preserved; dependencies not edited.
4. `L env lean -j1 -M1024 .lake/R59Audit.lean`: exit 1, 4.345299s. Actual failure: `Unknown option pp.width`. Full failed audit source/output preserved; every declaration nevertheless emitted an audit report. This failure was an audit formatting option, not a construction or axiom mismatch.
5. After removing only unsupported option: `L env lean -j1 -M1024 --root=. .lake/R59Audit.lean`: exit 0, 0.590846s. All 37 module declarations, including private helper and generated inductive declarations, have full explicit-name type / literal generated `#print axioms` / whitelist collection; ten public and one private theorem kinds checked via `.thmInfo`. All 37 ordered unique BEGIN/END pairs and completion marker verified.

5/8 calls and 42.160528/90 checker seconds including versions. One Lean process at a time, LEAN_NUM_THREADS=1, -j1/-M1024, no timeout. Manual audit uses the skill checker’s theorem-kind and standard-axiom checks; its helper was not invoked because its temporary audit file is outside the exact fixed audit lease.

Public theorem axioms (prefix is namespace above):

- `[propext, Quot.sound]`: heapLookup_payloadTyped, observationStep_preservation, observationTrace_preservation, force_observation_preservation, allocated_force_observation, selfAlias_observation_loop, nonRedex_typeBeta_excluded.
- `[propext]`: duplicate_graph_firstMatch, heap_collision_firstMatch.
- none: mismatched_graph_type_excluded.
- private lookupHeap_member: `[propext]`.

Across all 37 declarations: 18 none; 3 `[propext]`; 16 `[propext, Quot.sound]`. No Classical.choice, sorryAx, project axiom, native-evaluation assumption or other axiom. Full types and complete axiom output remain in checks; no checking result is inferred from a definition or LocalLaws parameter.

## Parent application, omissions and handoff

This discharges finite observed graph-read/type-beta preservation and composes the concrete R29 allocation payload component with the separate existing Force/Delay transition. The first remaining premise is an actual finite observation reaching the appropriate constructor from the original well-typed guarded heap, including guard preservation after source rec allocation. Owner: primary's graph/canonical-forms proof lane. View, inert wrappers, all remaining eliminators/control/metadata, source rec ordering/realization and actual typed-force formation from the original body remain separate original obligations. Owner: primary/source and executor lanes. No accepted source features or shared witnesses were restricted by this auxiliary relation.

Source lane reports a direct immutable-heap/native-cell identification obstruction and NO_SAFE_CODE_SLICE; this theorem supplies no Rust bridge. Fresh independent review and primary verification/integration remain required; no self-certification or root import was performed.

Writes STOPPED at this frozen revision: source, audit, dedicated cache, checks and this sole handoff are the only worker output paths. No pinned Lean/Lake processes remain; no descendants, background work, Git mutations, network, tests, dependency/manifest/configuration/root-import/compiler/shared-status/question edits. Existing tracked `.lake` probes were read/preserved. Lease release and shared status belong to primary. No further in-envelope work remains before independent review; parent gates remain OPEN.
