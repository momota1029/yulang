# DEMAND-ROOT-CAPTURE-CORRESPONDENCE/r12 proof/source handoff

Assignment `/root/demand_root_capture_r12_proof`, revision **1**. Outcome: **provisional source/native analysis; missing source correspondence; no theorem; repair conditions unestablished**. **WRITES STOPPED** at submission. No descendants. Independent review and primary adjudication remain pending.

## Admission, inputs and writes

Baseline `7b3ad7074`; contract SHA-256 `6ec1f3ba7d3012c8ea29f53abe5b37cca26832d25319502bd472ec47132a0347`; manifest SHA-256 `996d23a3f86541608bc7967658ceee9e29b128a95153fe6a60c26a00ef2ee05b`. Before packet/source bodies, Python SHA-256 authentication covered **104 entries, 104 unique paths, zero mismatches**, plus the parent manifest `a3b10055f0fb497bd341bdbd6ff7dc80d9ec40d15f564c6339d34e95539790b4` and outcome `838204e0451b52eda3a7b23baa01710f65af587992008ada168e8c1c7eb756a9`. The packet prose contains historical counts 100/90; the actual authenticated inventory is 104.

Read root AGENTS.md, AGENTS.pre-sprint.md, goal-driven-sprints, design-authority, current state/README, the fixed packet, Lean skill and source/execution references. No scheduling, configuration, questions, dependencies, Git or compiler outputs were changed. Requested routing Sol/high; observed model/effort UNKNOWN.

Analyzed immutable **R11 original** `isolated/source-receipt-origin-r11/crates/yu-solver/src/` files, whose bytes match the admitted clone pins: scheme `784b3087c875cc3bc05d16c50201d5efdb0da0425b7464ce8ff3744e1e93dfff`, context `be1be2277d54288ba4ae542e003dabc294031c29cb26b2b5d0454b0d1c102bd0`, extrusion `a6538ab3deae503fd2c002c88fb673a51848a350b226b8a38c3b43496cdd03ee`. Those original-path equivalences were separately hashed after initial body inspection; the 104 clone/input pins were authenticated before body inspection. No mutable R12 source body was read.

Final reauthentication at `2026-10-28T11:26:52Z`: all 104 paths rehashed; 103 unchanged. Only the concurrently leased R12 scheme copy differed, observed SHA-256 `dd97ecfb559320bb79116264ff5a648449e3d009adb9b4ff25e140e0f1b5a7df`. This is the implementation writer's output, not an input used by this analysis. All three immutable R11 originals still match admission. The complete manifest supplies other dependency hashes.

Only this handoff is written. Optional `isolated/demand-root-capture-r12/notes/theory/lean/YulangClosure/DemandRootCaptureR12.lean` is **NOT_PRODUCED**. No scratch/generated/cache outputs.

## Original claim, corrections and formal parent

Read the authenticated R7 specification `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`, **§§1, 3–5**, SHA-256 `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`. It quantifies every supported original source program, lawful finite construction history and actual extrusion occurrence, preserving original lexical/event/type scopes, independent uses, recursive sharing, complete Call, effects and one joint evidence strategy. §5 leaves inversion of the complete source Call rule and its joint source-admissible strategy open. §4's local diagonal lift assumes the original demanded comparison at its cut; it does not establish publication/use incidence.

Located the original paper through that source: `/home/momota1029/rust/simple-sub-reference-paper.pdf`, §§3.5.1–3.5.2, Figs. 6–9 and §5. It is outside the immutable input cone and was **not freshly read**. No original-paper result is inferred beyond the authenticated specification's stated scope.

Read birth-level SCC correction **§§2–6**, SHA-256 `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`: qualification uses paths wholly within one immutable-birth Value induced graph; freshening does not create a new source Value or extrusion occurrence. Read annotation-effect correction **§§1–1.2**, SHA-256 `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`: permission, actual inflow and residual remain distinct, with original polarity and correlated evidence retained. Neither correction supplies map membership. Top-level inference principles §1.1 require ordinary generated Function demand, accumulation and propagation; they do not select a new storage convention.

Exact Lean parent, immutable R7 `YulangClosure/Contracts.lean:128`, SHA-256 `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`:

```lean
YulangClosure.SourceProblem.InferenceSoundness p =
  ∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
    ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

`SourceProblem.SourceScopedCoverage`, `PrincipalCoverage`, `NativeCorrespondence`, `LocalLaws`, `LevelPath` and `Qualifies` were inspected. Proposition definitions and assumed laws supply no concrete instance or shared witness `e`. Research drafts are not semantic authority.

## Actual R11 trace and source path

Authenticated R11 stdout `3b05d5cc50b8ea3649a0b43f98ef1aeaa47026f936a90c3eaf251e40c3be3928` records invocation **1**, producer **scheme:4550**, then the same invocation's `session.execute()` consumer returning `Err(ReceiptMismatch)`. Original unwrap at **:8035** panics. The focused test failed, exit **101**; retained resources record **95.0866s**, sampled CPU **47.0s**, process-group RSS **1,815,572,480 bytes**, CPU affinity 0. These are R11 evidence, not new R12 execution.

The fixture at scheme **:8016** contains two module `invoke id` uses and two `outer` uses; each outer body contains two `local id` uses. The trace does **not** select which source occurrence, original call, capture graph, bound ordinal/relation, full demand, context use or antecedent failed. Its test name and post-unwrap restoration/cross-route assertions establish none of these identities. Thus the actual trace cannot yet be applied to one original source judgment or antecedent; it is not a source-qualified counterexample.

Inspected owners and correspondence, using R11 line numbers unless otherwise stated:

1. **Source generation.** Immutable R8 `candidate_source.rs:1865–1929` retains `CandidateRelation::Apply` with all four Call ports, owner, actual checking occurrence/cause and input identity. R11 context **:3540–3571**, `InferenceSession::candidate_context_seed`, creates `ScopedDemand { original_call, use_instance: 0, root: introduction.demand, output_scope, input }` for actual Call slot 0. `ScopedDemand` fields are at **:340–346**.
2. **Bound capture and antecedent.** `Capture::bound`, scheme **:2106–2154**, retains exact `BoundKey`, relation and evidence snapshot. Bound endpoints and relation identity remain separate; the snapshot is not a source typing derivation.
3. **Latent discovery.** Capture loop **:2683–2734**, specifically **:2709–2713**, examines every discovered bound relation's scoped flow and interns `Endpoint::Value(NegativeFunction(demand.root), Negative)` even if no structural bound reaches that root. `Capture::intern` **:1721–1741** returns the actual endpoint's unique node index and queues expansion. `expand_node` **:1944–2042** validates negative Function shape and captures all four children with polarities `[Positive, Positive, Negative, Negative]`. The session is immutably borrowed during capture.
4. **Publication filter.** Capture **:2811–2826** publishes `graph.negative_formal_roots` by iterating only `effect_algebra.formal_domains.values()`, selecting Function/Tuple roots already in this capture's endpoint map. Latent discovery's returned index is discarded. The existing code supplies no implication from discovered deferred root to membership in that registry.
5. **Registry ownership.** Immutable R8 effect **:1599–1655**, `candidate_record_parameter` / `candidate_unit_parameter`, and **:1658–1721**, `candidate_formal_annotation`, publish source-parameter domains. This is a parameter/annotation registry, not a demonstrated inventory of all retained demand roots. R11 `candidate_context_value_rewrite` **:3648–3669** can replace a demand root with the actual copied upper Function; FreshUse **:4545–4552** replaces it with a reconstructed term. Those inspected paths do not publish a new parameter-domain registration. This observation identifies a missing preservation premise; it does not identify which path produced invocation 1's missing root.
6. **Consumer.** `prepare_candidate_fresh_use`, scheme **:4231**, uses one `context_use`, scope/input map and common `terms` vector. At **:4533–4554** each captured parent is processed once; full demand remaps scopes/input, requires its root in `negative_formal_roots` at **:4550**, reconstructs `terms[index]`, and changes use identity only for locally remapped input. Original call remains unchanged.
7. **Later transport.** Only after preparation succeeds, evidence snapshots are imported (**:4591–4593**); `begin_candidate_fresh_bound` **:4619–4665** supplies exact captured antecedent/source bound, shared reconstruction, fresh use and mapped relation. Context **:4443–4455**, `candidate_context_fresh_transport_scoped`, retains the actual `Transport` witness. The failed preparation supplies no successful import/admission receipt for its failing demand.

Existing authentic control at scheme **:7358–7438** checks a selected structural local-formal demand and shared four-port reconstruction, and explicitly says strict latent-only reachability is not established for that source. It cannot prove coverage for the failing fixture or all source programs.

## Missing law, parent application and repair boundary

The immediate native coverage obligation is: for **every retained bound in this exact returned graph**, if its actual scoped relation carries demand `d`, the graph publishes **the very index returned by this capture owner for `(NegativeFunction(d.root), Negative)`**, and FreshUse reconstructs that node through the same row/term/scope/input maps and authentic bound antecedent. No sibling relation, equal-looking root or synthesized node index suffices.

Under the current publication algorithm, this additionally needs `d.root ∈ range(formal_domains)` plus exact endpoint identity. The inspected producers do not establish that registry-membership law for all latent, copied and freshened demands. This is a concrete native representation/preservation obligation of **`Capture` / `capture_candidate_graph_inner` publication and `prepare_candidate_fresh_use`**, with **primary source/native ownership**. It is not a new source restriction.

The source bridge remains: invert the actual original complete Call/source rule for the failed demand; retain its authentic source occurrence, shared witness, use, scope/polarity and captured/imported antecedent; prove that capture and lawful FreshUse preserve those incidences. Owner: **primary source/native correspondence lane**. The R12 implementation trace can identify the native event and actual owner-returned index; it cannot itself discharge this source law.

**No semantic repair follows from structure alone.** The existing latent intern shows where authentic correspondence could be retained, but this analysis neither authorizes blind insertion nor proves that extending the published map preserves complete source meaning. The packet's repair preconditions remain unestablished pending exact trace plus source-law adjudication. No repair is proposed for implementation under this handoff.

Applying this analysis to `SourceProblem.InferenceSoundness` supplies no `p.sourceJudgment s x e` or `p.sameScoped s x e a`. First remaining finite evidence is the exact invocation-1 source/use/bound/root/antecedent join; first remaining substantive premise is the original-source-to-native preservation law above. Full parent, source/native correspondence, effect hygiene, principality, termination and production remain **OPEN** with their original quantifiers and accepted features.

## Execution and cessation

Pinned environment files were read: `leanprover/lean4:v4.35.0`, YulangClosure library, `-j1 -M1024`, no external packages. No native Lake lookup, version command, Lean/Lake/Cargo run, test, formatter, bundled checker or axiom audit ran in this leaf; the packet assigns checks/cache/logs to Luna and permits Lean only for a justified artifact. New theorem inventory and printed-type/axiom results: **none / NOT_RUN**. No conditional theorem was fabricated from the missing premise.

Actual commands were read/hash operations (`pwd`, `cat`, `sed`, `rg`, `head`, `sha256sum`, Python hashlib/JSON, UTC `date`) and this handoff write; completed commands exited 0. CPU/RSS for this leaf were not sampled. Launch-to-stop wall time was not measured; the first retained UTC reading is `11:25:23Z`, reauthentication reading `11:26:52Z`. Work stops within the original 900s finite grant; unused budget is relinquished, with no renewal. The primary retains execution, fresh independent review, integration and gate authority. **Final writes stopped; no children, background processes, scratch/cache or unresolved descendant leases.**
