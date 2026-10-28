# SOURCE-RECEIPT-ORIGIN/r11 source/proof handoff

Assignment `/root/source_receipt_origin_r11_proof`, handoff revision **1**. Outcome: **provisional source/native evidence; first runtime branch UNDERDETERMINED; no new theorem**. Independent review and primary adjudication pending. **WRITES STOPPED** after this handoff. No descendants.

## Authentication and scope

Baseline `7b3ad7074`. Contract SHA-256 `3d7c9f3362f34277b446e0c3f52d05640a4afd3b866987501746a788e4c05aed`; manifest SHA-256 `a3b10055f0fb497bd341bdbd6ff7dc80d9ec40d15f564c6339d34e95539790b4`. Before source bodies, Python `hashlib.sha256` authenticated **90 entries / 90 unique paths / zero mismatches**. Admission hashes were read even for R11 paths; no mutable R11 Rust body was read. Immutable R9 counterparts were separately hashed against the corresponding manifest entries before their bodies. The manifest remains the complete input inventory.

Read root `AGENTS.md`, `AGENTS.pre-sprint.md`, `rules/goal-driven-sprints.md`, `rules/design-authority.md`, current state/README, the exact packet, `yulang-lean-proofs` and its source/execution references; the sprint skill explicitly leaves children inside their assigned packet. Only this handoff is changed. Optional `isolated/source-receipt-origin-r11/notes/theory/lean/YulangClosure/NativeReceiptOriginR11.lean` is **NOT_PRODUCED**. No scratch, generated/cache, compiler, root-import, dependency, configuration, status, question or Git writes.

Direct immutable sources under `isolated/native-witness-frame-repair-r9/crates/yu-solver/src/`:

| File | SHA-256 |
| --- | --- |
| `candidate_scheme.rs` | `9701321450cda1500a7aa77c0417bcec4a502e006b3c080591a82b7831e9e4bb` |
| `candidate_context.rs` | `19726ef8a6034a1b99f629021b6b7e97ec638f3c1d683206de3c6eac8025a2ec` |
| `candidate_extrusion.rs` | `2fa4cdf965785fc43ff9792af36c1dd86a01d50cf863229de2ddb721878d2477` |
| `candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `candidate_scope.rs` | `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a` |
| `candidate_effect.rs` | `7c8e4fe5270fd45cecece80dfbbdff81aa8f294546687938bf89212325fc146b` |
| `lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |

The last four R9 files were matched to the already authenticated inherited immutable entries. R7 copies of the specification and Lean interfaces below were used directly from the manifest. No dependency changed.

## Original claim and corrections

Original specification: immutable R7 `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`, **§§1, 3–5**, SHA-256 `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`. §1 ranges over **every supported original source program, every lawful finite construction history and actual retained extrusion occurrence**. It preserves source scopes, correlated evidence, recursive sharing, lawful independent uses, complete Call, effects and required principal coverage. §5 explicitly leaves inversion of the actual complete source rule and construction of one joint source-admissible strategy open. §4's pointwise diagonal lift requires a valuation satisfying the original demand at that cut; it establishes neither that source antecedent nor scoped publication/use transport.

The specification locates the original Simple-sub paper at `/home/momota1029/rust/simple-sub-reference-paper.pdf`, §§3.5.1–3.5.2, Figs. 6–9 and §5. That PDF is outside this packet's immutable input cone and was **not freshly read**. The authenticated parent specification, its actual statements and corrections were read; no paper claim is reconstructed from memory.

Corrections read in immutable R7 inputs:

- Birth-level SCC decision, **§§2–6**, SHA-256 `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`: paths stay entirely within one immutable-birth Value induced graph; cross-level references remain source dependencies; numeric type levels neither classify source telescopes nor create Value identities. No new extrusion occurrence is inferred from FreshUse.
- Annotation-effect policy, **§§1–1.2, 3–4**, SHA-256 `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`: original polarity, permission, inflow, residual, ownership and correlated evidence remain required. Local subtraction permission does not create a closed input-effect bound or unconditional removal law. Existing conditional hygiene results retain their premises.

Exact Lean parent read in immutable R7 `YulangClosure/Contracts.lean:128`, SHA-256 `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`:

```lean
YulangClosure.SourceProblem.InferenceSoundness p =
  ∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
    ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

Also inspected `SourceProblem.SourceScopedCoverage`, `PrincipalCoverage`, `NativeCorrespondence`, `InferenceTermination`, `LevelPath`, `Qualifies`, and `LocalLaws`. These are interfaces/propositions/obligations. No concrete source instance, shared witness `e`, original source judgment or law establishing a receipt guard is supplied by their definitions. Research drafts are not semantic authority.

## Actual observation and its unresolved branch

Authenticated R10 `logs/cargo-1.stdout` records `candidate_scheme::authentic_demand_capture_tests::replay_constructor_lineage_observes_rejected_cross_route_authentication` failing at **R9 `candidate_scheme.rs:8019:27`**, `session.execute().unwrap()`, with `Err(ReceiptMismatch)`. The exact fixture starts at line 8007 and contains two module uses of `invoke id` plus two uses of `outer`, whose body makes two local uses of `local id`. The parser/HIR/session constructors returned sufficiently far to enter `execute`; **no restoration projection, mutation/restoration assertion, selected Replay row, four-port assertion or cross-route authentication assertion after that unwrap ran**. In particular, the test name and later `authentication == None` assertion do not identify the error-producing guard.

R10 stdout hash `ebcbe9f7785ee57246f8b823e3a1a947e7753d8e8d9fafa5275ea277e7e925b4`; resources hash `df8a65c59a99b58be11b5db71efa67a1701c7e7dec33934eeb03d6f357b0e7af`. Recorded exit **101**, wall **42.3974s**, CPU peak sample **41.09s**, sampled process-group RSS **1,866,809,344 bytes**, affinity CPU 0. These are retained **R10 observations**, not R11 runs. R10 outcome hash `e151f1a31c4a9396fa9b52a265b0515cc00d073ea628a966d0b46b029de0cc84` leaves the deeper owner unestablished.

`InferenceSession::execute` (`lib.rs:10637`) enters source mode, executes the SCC plan, then loose source work and source expressions before final accounting. Multiple receipt errors propagate through these calls. Static inspection does **not** select the first event or its invocation. There is no source-qualified counterexample here and no assertion that the ordinary source should fail.

## Constructor → transport → restoration → consumer map

All line references in this section are to immutable R9 files.

1. **Original source occurrence / demand.** `candidate_source.rs:1865–1929` retains `CandidateRelation::Apply` with callee, argument and both effects/result ports; it allocates the actual call/input identity and retains owner, occurrence, checking cause, lexical region and computation scope. `InferenceSession::candidate_context_seed` (`candidate_context.rs:3470–3537`) creates the relation and `Origin`. For call local slot 0, an available introduction produces `ScopedDemand { original_call, use_instance: 0, root: introduction.demand, output_scope, input }`; slot 2 introduces the argument-scope release transformer. `ScopedFlow` (`:270–281`) stores **both** transformer and optional demand. Source occurrence identity and relation identity are distinct.
2. **Capture / antecedent / one FreshUse.** Capture preserves bound relation plus full source `BoundKey` and evidence snapshot. At `candidate_scheme.rs:2702`, deferred demand roots are explicitly included as latent payloads even if structural bounds do not reach them. `prepare_candidate_fresh_use` (`:4223`, demand remap at `:4532–4546`) uses one retained scope/input/term map. It remaps the root through `graph.negative_formal_roots` and retains `original_call`; it changes `use_instance` only for an input owned by this remap. `RetainedFreshUseMaps` (`:455`) stores these same maps and evidence imports. These facts are implementation structure, not a proof of complete source telescope coverage.
3. **Mapped relation / bound admission.** `begin_candidate_fresh_bound` (`candidate_scheme.rs:4611`) constructs the mapped bound in its captured polarity and calls `candidate_context_fresh_transport_scoped` (`candidate_context.rs:4373`). That owner retains `Dependency::Transport { child, parent, use_origin, witness: Some({from, to, reason: FreshUse}) }`, attaches the target bound, and preserves the supplied remapped flow. It then enters `candidate_begin_bound_restoration` with `BoundAdmissionCause::FreshUse { antecedent, use_origin, source_bound, mapped_relation }`. Thus the antecedent, original bound, use, mapped relation and destination are separately retained; none can be substituted by a sibling ID or endpoint resemblance.
4. **Physical emission.** `candidate_insert_bound_with_evidence` checks the actual selected physical slot after append (`candidate_extrusion.rs:990–1006`) before emitting `BoundEmission { admission, bound, physical, readback }`. Expected/read-back bound equality is an implementation memory/content invariant. A source typing rule alone does not identify the vector slot. Readback phase is `ConstructorAfterAppend`.
5. **Restoration / replay.** `candidate_begin_bound_restoration` (`candidate_extrusion.rs:1100`) retains owner, polarity, bound, emission, saved opposite count, source occurrence and cause. `candidate_step_bound_restoration_child` (`:1151`) rereads live canonical endpoints at the saved index, derives ordered lower/upper inputs, and calls `candidate_context_begin_replay(..., incoming_use=true)` (`candidate_context.rs:4087`). Replay combines the selected actual lower/upper relation fibers and scopes, retains its recipe and child relation, then uses distinct queued/consumed/child-return frontiers. The restoration-return observer records a completed emission only after this driver returns successfully.
6. **Completion consumers.** `test_completed_restoration_return` and `test_restoration_fresh_use_emission` (`candidate_context.rs:1922–1956`) require the same invocation/handle, unique return and exact FreshUse admission fields, target bound, physical slot/readback and phase. The session wrapper also rereads the current physical content (`candidate_extrusion.rs:703–737`). `authenticate_demand_transport_observed` (`candidate_scheme.rs:901–1055`) additionally checks the actual module/local FreshUse identity, original captured relation, imported snapshot, scope/input maps, ordered four ports, physical emission, Replay recipe/ancestry and exact typed port pairs. It returns `Option`, so **its rejection is not by itself the earlier `ReceiptMismatch`**.

The separate `SourceDrainReceipt` (`candidate_context.rs:112`) is created only after enqueue (`lib.rs:14200–14231`), retains incoming/created/selected relations, ack, origin index, task/cause and drain index, and is marked completed at terminal return (`lib.rs:14939`). `Capture::ensure_incoming_effect_upper_owners` (`candidate_scheme.rs:1624`) consults it for completed Lambda origins. It is not interchangeable with the bound admission/emission or restoration-return receipt. Completion retention is best effort (`candidate_context.rs:2264`); observation allocation failure cannot be silently relabeled as a source typing failure.

## Guard obligations that require the trace

These are concrete inspected candidates, **not an exhaustive list of all `ReceiptMismatch` sites and not a claim any one fired**:

| R9 owner/site | Required native invariant / missing bridge |
| --- | --- |
| `candidate_context_value_rewrite`, context `:3584–3591` | Retained processing pair equals the original pair; transformer is identity; retained demand root is the original upper negative Function; copied demand follows the actual rewritten upper. Needs source-demand/processing-owner correspondence across the actual extrusion. |
| `candidate_function_port_admit`, context `:3641–3645` | Parent flow transformer is identity; if demand exists, the parent's upper negative Function is exactly its root. Then Argument/ArgumentEffect swap and ResultEffect/Result preserve; the effect ports stamp input/protect body. Needs a law for the actual generated Call and its accumulated flow, preserved by each preceding transport. |
| `candidate_context_begin_replay`, context `:4141` | Selected lower fiber carries **no deferred demand**; resulting flow composes both transformers and retains the upper demand. Existing general generation/accumulation principles do not prove that lower-fiber exclusion for every captured/restored relation. |
| `prepare_candidate_fresh_use`, scheme `:4542` | Every retained deferred-demand root has the exact captured negative formal node and coherent reconstructed term. Capture's latent-root insertion is relevant construction evidence; complete coverage and source correspondence remain unproved. |
| `candidate_context_fresh_transport_scoped`, context `:4381` | Scoped mode has an actual remapped flow from this FreshUse. Native map totality/source coverage is required. |
| `candidate_context_reuse_fresh_relation`, context `:4361–4369` | Imported snapshot's original bound/relation, canonical target pair, nonzero use, and exact `Transport` witness agree. A bare ID supplies none of this provenance. |
| `candidate_insert_bound_with_evidence`, extrusion `:992–994` | Current physical slot exists and contains the full expected bound. Needs native construction/readback preservation, not a new source premise. |

No pinned source rule directly states these storage/ownership invariants. The original source rule must first supply its own complete demand, lawful incidence and shared witness; a separately proved native representation/preservation result must then derive the guard on this path. Assuming the guard, its negation, `session.execute()` failure, or a narrowed source domain would not discharge that bridge. Neither immutable-birth qualification nor annotation permission determines a flow transformer, source telescope, use identity or receipt slot.

## Lean status and parent application

**No R11 declaration is delivered.** Kernel print/audit and skill checker: **NOT_RUN**, as required by the exact packet. No new conditional theorem is justified by the available source premises; merely reifying a guard implication would leave its decisive premise untouched. No `sorry`, `admit`, axiom, bypass, stronger parent hypothesis or smaller language was introduced.

The retained R10 artifact SHA-256 `5e44687e7d59f1ccac2da6361befe66bc7a19ed3744d0dc4bc029ea9c48e61f6` and actual R10 `lean-2.stdout` were inspected. Its reusable theorem **`YulangClosure.NativeExternalEffectFrameR8.native_frame_conditional`** requires:

```lean
extract : ∀ stop, reaches start stop → ∃ n : Nat,
  view stop = applyEffects (view start)
    ((observeCapacity io changed active p).effects.take n)
```

It concludes `∀ stop, reaches start stop → pi (view stop) = pi (view start)` under one fixed `io`, `changed`, `active`, plan `p` and view. Its **recorded R10** transitive audit is `[propext]`. The complete recorded seven-theorem audit is: `effect_frame`, `effect_keeps_replay_undo`, `effects_frame`, `every_prefix_frame`: no axioms; `callback_frame`, `observed_capacity_frame`, `native_frame_conditional`: `[propext]`. R10 successful audit log hash `96cbd69b6e1e866a150a271025a5501542b1792b112bfa30cee6d0a7e9ad6fc7`. This is an existing conditional frame result; it establishes neither source-demand legality nor guard success nor `extract` for actual Rust states.

Application to the original parent stops first at **identification of the actual error-producing owner/guard for this invocation** (R11 implementation trace, primary intake). Once identified, the substantive premise remains **the complete original source-rule → retained native demand/flow/antecedent/use incidence → actual consumer guard correspondence**, supplied by the primary source/native lane. A trace can instantiate the native event to investigate; it cannot supply the original source judgment or one joint witness. All four whole goals, `NativeCorrespondence`, effect hygiene and production remain **OPEN**. This packet does not reduce their quantifiers.

Covered by this audit: exact fixed fixture, module/local FreshUse map path, four Call ports, scoped flow/demand, bound provenance, restoration, physical readback and separate source-drain completion. Not observed: any R11 runtime event/branch/ID, post-failure assertion, or whole-language source/native realization. The fixture contains no explicit effect annotation; effectful/annotated programs, optional records, methods, generalization, recursive sharing and all accepted source features remain in the parent domain and are not proved by this audit.

## Commands, resources and frozen handoff

This leaf ran only `pwd`, `cat`, `sed`, `rg`, `head`, `tail`, `sha256sum`, Python read/hash/time operations and the one leased handoff write. Authentication commands exited 0; source reads exited 0 except one `rg` for failure strings in R10 **stderr** exited 1 (no match); the actual panic is in authenticated **stdout**, preserved and read above. No Cargo, Lean, Lake, bundled checker, formatter, install, test, background process, nested CLI or child ran. Native Lake/Lean versions were **not executed by this leaf**. The authenticated toolchain files specify `leanprover/lean4:v4.35.0`, `YulangClosure`, `-j1 -M1024`, no packages; hashes are recorded in the manifest. The primary owns execution, caches and exact logs.

Maximum assignment 900s, no renewal; no heavy-process budget consumed. Exact assignment wall/CPU/RSS was not instrumented by this leaf and is not fabricated. Last pre-freeze time read was `2026-10-28T11:11:33.360739+00:00`; final freeze time and SHA-256 are sent in the stop message. No further writes or pending descendants. Requested Sol/high; effective model/effort metadata UNKNOWN.

Mutual TODO **R11-ORIGIN-SOURCE-1**, owner Luna: authenticate/fresh-review this handoff and implementation candidate before any check; join the first actual error site to the same invocation's occurrence/cause, source/target bounds, relation/snapshot/use and demand/transformer. Preserve absent fields as unavailable. Falsifier for an alleged source-law implication: a lawful original derivation and actual native construction reaching the guard with its negated condition, with full source/native correspondence; an isolated `ReceiptMismatch` is insufficient. If no complete trace distinguishes the branch, retain UNDERDETERMINED and name the first missing instrumented owner. No semantic repair is authorized in R11.
