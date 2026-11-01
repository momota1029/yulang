# R147 proof/source correspondence handoff

## Frozen assignment

- ID `effect-permission-real-consumer-r147-proof`, revision 1.
- Contract `tasks/agent-loop/sprints/effect-permission-real-consumer-r147.md`, SHA-256 `cc33e831cca0bd86717f0e4c7b995b8f89f2a5418979a66fdbcf0464bb6eeb90`.
- Baseline `3560df97dab02744da10e897c73c1cf94118f4ee`.
- Author/actual runtime identity `/root/r147_real_consumer_proof`; current-session parent assignment and explicit lease acknowledgement are the launch/active-work receipts. Requested Sol/high; observed effective model/effort **UNKNOWN**. No descendants or contributing coauthors.
- Sole write lease: this file. Outcome class **source-native-evidence with an OPEN bridge**, pending fresh independent review. No theorem, counterexample, checker acceptance, or production approval claimed.

## Parent and result

The admitted Authoritative compose decision requires release of the original `'e` protection also at its occurrences inside output `'f`, including `f = id`, while preserving contribution attribution and every independent protection. Release does not itself authorize capture. Original Simple-sub A/B quantifiers, source domain and shared witness remain unchanged. The admitted R145 handoff locates the wider A/B and whole-language parents; those original documents are outside this packet's admitted inputs, so this audit does not reconstruct or certify their complete statements. In particular it does not invent a formal type for the wider H obligation from the name alone.

**Actual result:** the admitted source reaches a real effect allowance decision, but that decision does not receive/evaluate the scoped transformer or a carried input/protection state. The source trace identifies the first missing consumer bridge. It supplies neither an authenticated reachable hygiene counterexample nor a whole-language impossibility result. Missing consumption is not refutation.

### Independently reconstructed execution path

1. `candidate_context.rs:4210–4217` transports the task, installs its relation in `context.processing`, executes it, then restores the previous processing relation. `candidate_context_execute_relation:4219–4305` validates the task pair; a nonzero transformer on a reflexive Effect pair returns an availability error. In scoped mode it records `(relation, operand)` observations for Support/Contribution/AnnotationMember operands. This is recording, not transformer evaluation.
2. For a nonidentity ordinary context it traverses zero-word filters. Empty filters return; discharged relations return their consumed-endpoint status. Each retained weight supplies an `Allowance(view)`. A row with an already registered upper allowance reattaches bound provenance and replays that bound (`4265–4288`); otherwise it invokes `candidate_apply_effect(lower, Allowance(view))` (`4290`). Finally it retains discharge/residual bookkeeping (`4293–4303`). Neither branch supplies `ScopeState` arguments.
3. The actual callee is `candidate_extrusion.rs:1147–1170`, independently located without R146 conclusions. It canonicalizes both endpoints and handles equality. Row cases select a bound owner and polarity using actual effect levels, insert the bound, and replay it. Atom/nonrow cases call `candidate_check_effect_operand(lower, upper)` (`1165`). `candidate_insert_bound:635–643` retains the current processing relation as an evidence cause, so relation metadata is not globally erased merely because these function signatures have two endpoint arguments. Physical bound evidence is authenticated by readback (`856–870`). This preserved metadata still is not an incoming protection state.
4. `candidate_replay_bound:1070–1112` meets the new bound with every opposite bound, forms the directed task, calls `candidate_context_begin_replay` and `candidate_context_drive_replay`. The inspected context replay construction `candidate_context.rs:4430–4476` composes the lower and upper transformers in order, preserves upper demand, and rejects lower demand. It constructs a child relation and dependency evidence. This is transformer propagation, not evaluation on a carried contribution state.
5. The real decision is `candidate_effect.rs:1437–1505`. Bottom succeeds. Support enumerates its annotation members and optional tail into new Effect tasks. For Contribution or AnnotationMember against Allowance, it reads the effect family and allowance view; `allowed` is `context.allowed(closed_weight)` when present or `view.allowed` otherwise. Membership succeeds; a remaining tail enqueues another row constraint; otherwise it reports `candidate_effect_mismatch`. Concrete contributions against EmptyNegative also mismatch. No branch reads transformer guards, input-route stamps, or protection membership. Thus there is an actual ordinary allowance check, not merely an empty-state experiment; it is not yet a scoped eligibility/subtraction check.
6. A second entry is visible in `lib.rs:13825–13841`: the candidate feature branch of `apply_effect_task` directly calls the same `candidate_apply_effect`. This corroborates the callee owner without establishing every scheduling path outside the inspected region.

### Catch construction is a separate path

`candidate_source.rs:1383–1437` constructs Catch binder births and `Action::CatchOperation` from resolved operation arms, retaining declaration, owner, arm-body occurrence, payload/continuation positions, original scrutinee endpoint/effect, level, and optional operation-v1 link. Action execution at `2513` passes those arguments to `candidate_catch_operation`.

The inspected `candidate_effect.rs:1181–1268` dispatches the optional-link transaction and builds paired declaration signatures, payload constraints, continuation response constraints, optional field allowance, and fresh entry/returned effect rows. The optional link's row/family checks do not constitute transport of `NativeScopeTransformer.State`.

More decisively, ordinary Catch lowering in `candidate_source.rs:1608–1625` emits the scrutinee effect to the Catch result effect at slot 51 and each arm-body effect to that result. It also propagates the ordinary value results. That inspected constructor does not subtract a handled family according to protection state. This fact is restricted to this constructor and admitted source set; it is not a claim about unadmitted runtime/backend implementation. `shadow_apply.rs:1638–1644` also exposes separate operation-v1 and scoped experimental solve modes, so combining their evidence would need an actual joint path.

## Exact native mathematical comparison

Rust `candidate_scope::ScopeState` (`candidate_scope.rs:37–40`) has `inputs: Vec<InputRouteId>` and `protections: Vec<EffectScopeId>`. That shape alone is not source attribution, a runtime contribution witness, or an instance of Lean `State`.

For successfully constructed canonical transformers, the inspected Rust evaluator (`180–209`) sorts/deduplicates incoming lists, unions input stamps, preserves untouched incoming scopes, and for a present entry retains the scope exactly when `(keep_initial && inherited) || add.holds(initial_inputs)`. `AddCondition::holds:90–93` is an existential missing initial tag. Its stamp/protect/release constructors (`102–128`) match the intended primitive membership equations. The corresponding admitted Lean declarations are:

```text
YulangClosure.NativeScopeTransformer.State
  inputs : List Nat; protections : List Nat

Transformer.evaluate (transformer : Transformer) (initial : State) : State
  inputs = initial.inputs ++ transformer.stamped
  protections = retained incoming scopes ++ applicable missing-guard scopes

evaluate_rename (transformer : Transformer) (initial : State)
  (scopes tags : Nat → Nat)
  (scopeInjection : Function.Injective scopes)
  (tagInjection : Function.Injective tags) :
  Equivalent ((transformer.rename scopes tags).evaluate (initial.rename scopes tags))
    ((transformer.evaluate initial).rename scopes tags)

YulangClosure.NativeFreshScopeTransport.fresh_evaluate
  (scopeCount tagCount : Nat) (scopeKeys tagKeys : List Nat)
  (transformer : Transformer) (state : State)
  (validTransformer : TransformerValid scopeCount tagCount transformer)
  (validState : StateValid scopeCount tagCount state) :
  let scopes := (fresh scopeCount scopeKeys).remap
  let tags := (fresh tagCount tagKeys).remap
  Equivalent ((transformer.rename scopes tags).evaluate (state.rename scopes tags))
    ((transformer.evaluate state).rename scopes tags)
```

These are source-inspected declaration types, not fresh checker output. `StateValid` bounds **all** incoming tags/protections by the pre-copy inventories (`NativeFreshScopeTransport.lean:164–171`); `TransformerValid` bounds stamps, every entry key, and every guard. `fresh_evaluate_and_reuse:278–295` additionally states post-copy transformer/state validity. Its proof depends on `fresh_evaluate`, `fresh_transformer_valid`, `fresh_state_valid`, and `evaluate_valid`. Complete transitive axiom dependencies for these declarations and `evaluate_rename` are **NOT_RUN / UNKNOWN**; no axiom-free or checker-accepted result is asserted.

The Rust/Lean comparison is membership/extensional, since Rust canonical vectors and Lean lists differ in order/duplicates. A formal refinement proof of Rust loops, fallibility, and normalization has not been constructed. An evaluator correspondence restricted to successful calls would still require all canonicality and encoding premises. No assumed Rust object has been substituted for Lean `State`.

The inspected actual evaluation owner is `candidate_context.rs:3280–3284`: `evaluate_observation(relation)` evaluates either identity or the retained transformer with `&[], &[]`. `shadow_apply.rs:1646–1653` invokes it only while constructing scoped inspection observations. A search across all nine admitted Rust blobs found production `ScopeState`/protection/evaluation references in this kernel and observation interface, plus test text; no inspected effect decision consumes those evaluated protections. Empty incoming state is a legitimate special evaluator input, but cannot discharge arbitrary inherited protections in the parent.

## FreshUse application and first missing premise

Independently read `candidate_scheme.rs:4444–4451,4773–4800`: one `ScopeInventory::fresh` result is retained before reconstruction; each captured parent flow remaps its transformer using that `scope_remap` with identity fallback, and maps demand output_scope/input using the same tables. Demand root and local use_instance are reconstructed separately. Demand is not Lean `State`.

This concretely supplies the transformer-side candidate map location for the mathematical law. It supplies no corresponding `state.rename scopes tags` invocation at the reached allowance check. Consequently even a separately established allocator/support invariant and a checked `fresh_evaluate` cannot yet be applied to that decision. The allocator theorem would have a real application only after authenticating:

1. A source-owned incoming contribution/witness carrying the actual input-route and protection state at each relevant boundary, with a precise encoding to native state and validity below the same pre-copy inventory lengths.
2. The **same successful FreshUse maps** on that entire state and transformer, including external fixed coordinates and inherited scopes, without merging residual/provider/witness lineages or replacing them by demand coordinates.
3. A real effect/Catch eligibility consumer whose result is related to protection membership after the ordered transformer evaluation, while retaining operation attribution and independent continuation cases.
4. Source construction/replay/composition coverage placing the compose release on every corresponding `'e` occurrence in `'f`, and preserving all independent protections; release alone grants no capture.

**First missing bridge:** `candidate_context_execute_relation` / `candidate_apply_effect` to the reached `candidate_check_effect_operand` decision has no established incoming witness/state interpretation and scoped decision-consumption law. Catch's owning source constructor currently propagates its scrutinee effect outward; no authenticated subtraction consumer is supplied by this trace. Source owner: Luna's `candidate_context`/`candidate_effect`/`candidate_source` lane; formal refinement owner requires a later explicit packet.

Mutual TODO `R147-CONSUMER-STATE-01`: Luna should identify an already approved source-owned carried state and actual protection-sensitive effect/Catch consumer, or return the smallest provisional implementation proposal to the semantic/implementation gate. Exact falsifier: an admitted reachable source contribution with a protection used by the consumer for which the retained FreshUse map differs between transformer and carried state, or release removes an unrelated protection / fails to remove its own scope at an output occurrence. An abstract out-of-inventory number, an assumed transition, empty-state observation, and lack of a consumer do not meet this falsifier. No production edit is authorized here. The exact full H formal statement/consumer authority, if needed to state a stronger theorem, is an input dependency for Luna rather than an invented interface.

## Input and read inventory

All twelve direct source SHA-256 values below were computed before semantic source inspection and matched the contract. Hashing reads complete bytes; semantic inspection was bounded line windows and text searches, not a full semantic audit of every line.

| Baseline source | SHA-256 |
| --- | --- |
| `candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `candidate_scheme.rs` | `e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814` |
| `candidate_scope.rs` | `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03` |
| `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `shadow_apply.rs` | `2fa42a5570e660babab5da6361e0d71e0c022b234a21f7e01b78eafbfc65f278` |
| `lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `candidate_effect.rs` | `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01` |
| `NativeScopeTransformer.lean` | `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6` |
| `NativeFreshScopeTransport.lean` | `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5` |
| `2026-10-15-compose-scoped-effect-release.md` | `fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679` |

Rust names in that table expand under `crates/yu-solver/src/`; Lean names under `notes/theory/lean/YulangClosure/`; the design under `notes/design/`.

The two admitted R145 handoffs were individually hashed before reading their full text at baseline: `effect-permission-fresh-map-support-r145-proof.md` `da15341b46d3b7adef8cb1bd90d02bfe6dd27fc594a5fb96520f5cf84f82dcea` and `...-source.md` `e543b1cd4c6d98d6fdaf912f228a8cd53e407fe72edf3338b2f1c9fca295ffba`, under `tasks/agent-loop/inbox/`. Their authors identify `/root/r145_fresh_map_proof` and `/root/r145_fresh_map_source`. Reused only their conditional status and parent/input locators; all material Rust claims above were independently inspected. The R145 candidate Lean file was not opened or checked. Its conditional candidate is not used as a completed theorem.

R146 source handoff `tasks/agent-loop/inbox/effect-permission-native-support-invariant-r146-source.md` is absent from the stated baseline tree. On Luna's exact locator instruction its frozen working-tree bytes were **hash-only** read, SHA-256 `9c940ab56ccd182299833fe93b41701619d600b62c15f3af21b9b94659b694ef` matched. Its contents/conclusions were not displayed, inspected, or reused. R146 proof deviation receipt was never opened. Hashing this optional handoff happened after source inspection; the twelve direct source hashes and the R145 hashes preceded their respective inspections. This timing is explicit rather than a claim that every optional receipt was hashed at initial startup.

Governance read in full/batched tool output: `AGENTS.md`, `AGENTS.pre-sprint.md`, `rules/goal-driven-sprints.md`, `tasks/agent-loop/README.md`, the R147 contract, `.agents/skills/yulang-lean-proofs/SKILL.md`, its `references/sources.md`, and `/home/momota1029/.codex/skills/yulang-proofs/SKILL.md`. Initial guessed `.agents/skills/yulang-proofs/SKILL.md` was absent; no bytes read there. Some first combined captures were truncated; the proof skills, base map and sprint rules were reread in narrower calls. No files linked merely by these maps were opened. No central state/board, quarantine artifact contents, unlisted semantic source, working-tree Rust, or external source was read.

Decoder: Python standard-library `pathlib`, `hashlib`, `zlib`, `struct`, invoked via stdin; no Git CLI. It decodes the exact baseline commit and traverses tree entries for admitted paths; loose object SHA-1 checks authenticate their object headers/bodies. Packed inputs use v2 fanout/index lookup and in-memory zlib/OFS_DELTA/REF_DELTA reconstruction; final whole-blob SHA-256 checks against the contract authenticate the reconstructed sources. Delta bases are mechanical object reconstruction inputs, not separately admitted semantic evidence. No decoder file, cache or scratch path was created. An initial loose-only read failed at packed intrusion object `f636c3277f50859055b51ecd245c0ff9f95244d1`; Luna then explicitly authorized in-memory pack decoding. A baseline lookup for the R146 source path raised KeyError before the exact frozen file was hash-read.

Storage metadata inventory: commit `3560df97dab02744da10e897c73c1cf94118f4ee`; tree objects `e5df6055973dded0020a31b69e70961521cd509b`, `a84a6065e1472b8249754a546958be6a00a443ee`, `e3e2b458076edba255fb18baf99dc31f8307ec09`, `dadcc6bc54eb2f68ddb1a0af143c76126f8a7df6`, `24fd0ef8b6a3d7fd44e5b350585b8656adecc00e`, `ba5d0cb9baf4e7536f5c8c20ea1656f973ba0f20`, `bb7d20529de70208c0d9207494ad2a99684af63c`, `22be89251bb6c89b1c0cdc7f6e3b6ea1dce1e363`, `dc90df202addcd1e070db7c2b1678cf7847e6976`, `5026f778d029f452e16cacb422c3bb1618db6098`, `0dd84be223a37cc1b26150477e8af61b205bba51`, `7465b1d16990906472ee6093ab84871d93f83b2d`. Loose blob IDs: `b43f37f4cca246a072b73329aed84e89aef4ebe1`, `9d24adc6cec7a3df8072b543e326a20afd017ea5`, `d455f16ccb07e075d97ba05fc986233e6706ca7c`, `1c9122c4fc87e4695b4d81e9bf1e1962c2167896`, `b790e0bf729dd2f28b000d0f8803747e6ede5c77`, `7ce2a3d59b16a277cd553ea3ef84e28ff3c98378`, `18a4cafb4a1bb6466686d82aa825e28318f91a72`, `84ebeb6cdac0cfae324fdbf270b24d852b479c28`, `2cc8050de67a3d0d620179210595304508edf7dc`, each at `.git/objects/<first two>/<remainder>`.

Index metadata was read only from `.git/objects/pack/pack-<ID>.idx` with IDs `1ab082926185721fd914e65bc2f8da8978cde4fa`, `2276145fae6641546e88e47a370fad7655c4601e`, `29641bfc7645597a28a343dcd2691e63c254f42b`, `376db50574c3e8439898ffcf3bd30b6a75d969f3`, `72ccf503b00ebc5d838226188a608a76dac2452f`, `9b7b12e873c619f4e4481b3f551fa43db318fef1`, `9c6c2d4bf59af46a3f64ee21e2cfa9c64d499fe0`, `9c941599dea735331c26a73195efbce99d16a51a`, `a0dbaca0f34dbadb78a1435ea1750f4eff9d0c59`, `ad9e3a92ef88938c47bfbebf7aa3a3bac86ae284`, `d45c7876f6fff7c32521efb34b249b94f05c45a2`, `dedf098049c211100fd96e72edae1c87025aabdd`. Actual compressed object reads were from matching `.pack` paths: `9b7b…` offsets 425889 and 419597 (intrusion and delta base), `376d…` 416971 (extrusion), `dedf…` 834465 and 802900 (Lean modules), `ad9e…` 10141306 (design tree), `72cc…` 1196426 (design blob). Adjacent compressed bytes in bounded stream reads were not decoded as semantic inputs.

Semantic read coverage: complete compose decision; declaration-oriented searches and windows `63–80,98–133,379–416` in NativeScopeTransformer, `160–175,252–295` in NativeFreshScopeTransport; Rust windows cited above, plus source/effect/Catch/scope/state/FreshUse/replay symbol searches across the nine admitted blobs. Additional inspected windows: candidate_context `270–310,2940–3002,3260–3302,3750–3865`; candidate_effect `1112–1180,1188–1268,1398–1505`; candidate_extrusion `760–840,970–1050`; candidate_scope `1–45,65–280`; shadow_apply `1638–1655`. Test lines surfaced in searches/windows were not executed or used to establish reachability. `candidate_intrusion` was hash-read and symbol-searched only. Tree name listing surfaced old `20261020-r145-proof.md` and `20261020-r146-proof.md` names only; their blobs were not read.

## Checks, limitations and stop

Actual operations were read-only shell/Python text extraction, hashing, object decoding, one clock reading and the sole leased artifact write. No Rust/Cargo/Lean/Lake execution, compiler, build, tests, installation, environment creation, Git CLI/mutation, source edit, scratch/cache, external contact, or descendants. No production TODO was implemented. Scope does not establish full allocator preservation, arbitrary source reachability, full Catch/H semantics, F1/FK1 independent quantifiers, residual/provider/witness refinement, or original A/B closure.

Budget cap 480 seconds; work completed within the assignment window, exact elapsed/CPU/RSS not instrumented. No further resource claim. Stop condition reached: exact first missing bridge identified and frozen handoff returned. All writes **STOPPED** after this revision; no descendant leases or other new paths. Handoff SHA-256 is returned separately after hashing the final bytes. Luna owns fresh review, adjudication, next dependency admission and integration. There is no remaining in-envelope writing step.
