# R145 proof handoff — finite shared-map support

## Frozen receipt

- Sprint: `EFFECT-PERMISSION-FRESH-MAP-SUPPORT/20261102-R145`.
- Contract: `tasks/agent-loop/sprints/effect-permission-fresh-map-support-20261102-r145.md`, SHA-256 `1062ba2d5c1dc19ccbaa42b31b6a08e10b32454e0dbb72bdf7dcb89b322fa78b`.
- Assignment / revision: `r145-fresh-map-proof`, revision 1.
- Baseline and observed HEAD: `f634b2f426b6aef3e2dd602dab0a6dce3e1ad0dd`.
- Author/runtime: `/root/r145_fresh_map_proof`; requested registered `lean_prover`, observed effective model/effort UNKNOWN. Actual current-session assignment and acknowledgement supplied through the collaboration runtime. No children.
- Outcome: **conditional theorem candidate, UNCHECKED**. No kernel acceptance, independent acceptance, source refinement, or production authority claimed.
- Exact writes: `notes/theory/lean/YulangClosure/NativeScopeFreshMapR145.lean` and this handoff. No scratch/generated/cache/environment paths, root-import edits, compiler/test edits or Git mutations.

## Original sources and unchanged parent

The native algebra's original claim is `notes/theory/2026-10-15-compose-scoped-release-construction.md` §2, “Input tags and conditional introduction of a new scope”, especially the joint injective renaming paragraph. It preserves the same complete carried contribution witness while transforming input tags and protections. That note does not prove that FreshUse constructs the joint map. Its source expectation is the Authoritative `notes/design/2026-10-15-compose-scoped-effect-release.md`, “Direct decision” and “Scope of the operation”: release the original `'e` scope even inside `'f`, including `f = id`, while preserving contribution attribution and every independent scope.

The whole parent remains `docs/yulang-whole-proof-closure-ja.md` §§1, 4 and the original A/B statement in `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5. Quantification remains every supported original source program/history, original scopes and one joint witness; the birth-level qualification correction in `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6 remains applicable. `docs/yulang-semantics-and-soundness-ja.md` is an integration draft; its candidate receipt/route representation is not promoted to semantic authority here.

Actual Lean definitions read: `YulangClosure.NativeScopeTransformer.Entry`, `Transformer`, `State`, `Missing`, `Equivalent`, `Entry.rename`, `Transformer.rename`, `State.rename`, `evaluate_protection`, `evaluate_rename`; and `YulangClosure.NativeFreshScopeTransport.fresh`, `allocate`, `fresh_injective_on_old`, `TransformerValid`, `StateValid`, `fresh_evaluate`. The existing `fresh_evaluate` already uses a ghost global injection agreeing on the old inventory. The new candidate exposes finite support requirements directly and makes no claim to have discovered that existing allocation theorem.

## Candidate types, source inspection only

All new declarations are in namespace `YulangClosure.NativeScopeFreshMapR145`. Their exact source signatures and unexecuted `#check @...` / `#print axioms ...` directives are in the candidate file. No printed or inferred checker type is reported as actual output.

`InjectiveOn S f` means `∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b`. `TransformerSupported t S T` includes all stamped tags, every scope-entry key, and every missing-guard tag. `StateSupported x S T` includes every incoming input tag and every incoming protection scope. These proposition definitions expose premises and supply no source instance.

The main candidate has the following source type (aliases `t`, `x`, `S`, `T`, `s`, `u` stand for its explicitly quantified arguments):

```text
evaluate_rename_on_support
  (t : NativeScopeTransformer.Transformer)
  (x : NativeScopeTransformer.State)
  (S T : List Nat) (s u : Nat → Nat)
  (ht : TransformerSupported t S T)
  (hx : StateSupported x S T)
  (hs : InjectiveOn S s) (hu : InjectiveOn T u) :
  NativeScopeTransformer.Equivalent
    ((t.rename s u).evaluate (x.rename s u))
    ((t.evaluate x).rename s u)
```

The exact minimal containing lists can be chosen as `S = keys t.scopes ++ x.protections` and `T = t.stamped ++ (t.scopes.flatMap (fun pair => pair.2.missing) ++ x.inputs)`. Larger finite supports are allowed, for example adding demand coordinates. No hypothesis of injectivity on all natural numbers is present. The proof repeats the existing law's membership argument with local support at each lookup; it does not call the global theorem under a disguised global-injectivity assumption.

The concrete allocation specialization `fresh_evaluate_on_support` quantifies the same `t`, `x`, `S`, `T`, natural pre-copy counts `scopeCount`, `tagCount`, and arbitrary finite `scopeKeys`, `tagKeys`. Its hypotheses are `TransformerSupported t S T`, `StateSupported x S T`, `∀ scope ∈ S, scope < scopeCount`, and `∀ tag ∈ T, tag < tagCount`. Its conclusion is the same equivalence with `s := (NativeFreshScopeTransport.fresh scopeCount scopeKeys).remap` and `u := (NativeFreshScopeTransport.fresh tagCount tagKeys).remap`. The existing `fresh_injective_on_old` supplies local injection from those bounds; injection is not a new allocation hypothesis. Duplicate copy keys are permitted by that model and do not require a uniqueness premise.

Supporting theorem candidates and their source-level statements are:

| Fully qualified suffix under `YulangClosure.NativeScopeFreshMapR145` | Statement / necessary premises |
| --- | --- |
| `mem_map_on_support` | `f a ∈ map f items ↔ a ∈ items`; items and queried `a` lie in the finite support where `f` is injective. |
| `entry_rename_on_support` | Rename then `entryAt` at `s scope` equals renaming original `entryAt`; all keys and the queried scope lie in the locally injective support. |
| `entry_missing_supported` | Every tag in a looked-up entry belongs to the support containing every entry's missing tags; absent keys use the empty identity entry. |
| `missing_rename_on_support` | Renamed `Missing` iff original `Missing`; both guards and inputs lie in the locally injective tag support. |
| `renamed_protection_on_support` | Protection membership at `s scope` iff original membership; transformer and state are supported, both maps locally injective, queried scope supported. |

All seven theorem candidates, including the two main declarations, have axiom status **NOT_RUN / UNKNOWN**. Audit directives cover all seven. No axiom-free claim follows from reading their proof terms. No `sorry`, `admit`, project axiom declaration or checker bypass occurs in the changed source or the two inspected direct Lean dependencies; the text-search matches were the candidate's seven intended `#print axioms` directives. This search is not a transitive axiom audit of `Std` or kernel acceptance.

## Frozen source application and first remaining premise

Source input: `tasks/agent-loop/inbox/effect-permission-fresh-map-support-r145-source.md`, revision 1, SHA-256 `e543b1cd4c6d98d6fdaf912f228a8cd53e407fe72edf3338b2f1c9fca295ffba`, rehashed and matched the primary's frozen receipt.

Its trace authenticates a single retained `scope_remap` for transformer and demand coordinates at `prepare_candidate_fresh_use`, with identity fallback outside the copied domain. It leaves OPEN the combined support/allocator invariant across all flow/transformer producers, replay/composition, prior successful/failed copies and external incoming coordinates.

Conditional application: take `t` to be the original parent flow's represented transformer, `x` to be its actual incoming tag/protection state, the two counts to be the inventory lengths immediately before `ScopeInventory::fresh`, and the two key lists to be that call's actual successful copy iteration. If the source owner establishes support bounds for all of `S,T` and correspondence of the native map to the successful overwrite-or-identity projection, `fresh_evaluate_on_support` is the candidate theorem to apply. This would establish only the displayed native-algebra equivalence for that same pair of maps and state.

**The application is not discharged.** First remaining goal, owner Luna/source: authenticate every incoming transformer guard/key, stamped tag and incoming state tag/protection as below the same pre-copy lengths, and identify the actual incoming state and its same-map rename at the relevant consumer. The source handoff separately remaps demand `output_scope` / `input`, but demand and `use_instance` are not fields of `NativeScopeTransformer.State`; this candidate proves no demand-root, use-instance, term/evidence-reconstruction or full scoped-flow law. Extending support by those demand IDs would permit an injection statement only after their old-inventory bounds are authenticated.

The source handoff's suggested uniqueness of copied keys is unnecessary for the existing Lean allocation projection's injectivity: repeated-key overwrite is already covered by `NativeFreshScopeTransport.fresh_injective_on_old` and `repeated_key_overwrites_without_old_collision`. Actual source iteration/map correspondence and ownership validity still need their own evidence. This refinement supplies no source-side bounds.

No reachable source collision/counterexample was established. Generic outside-inventory collisions and the existing transformer-only-support counterexample are not promoted to actual source counterexamples. Original A/B, hygiene, source/native correspondence and production promotion remain OPEN.

## Dependencies and actual operations

| Input / artifact | SHA-256 |
| --- | --- |
| `NativeScopeTransformer.lean` | `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6` |
| `NativeFreshScopeTransport.lean` | `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5` |
| Candidate `NativeScopeFreshMapR145.lean` | `d47da744694beb04abfcf3b06137b5a04b241f568490af5fbf59147933a2db57` |
| Algebra manuscript | `773a1ed4c2ebe7503438c57a06acd23e03fbc1fd0d6ae30260848c4430fe676e` |
| Authoritative compose expectation | `fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679` |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lakefile.toml` | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |

Actual commands: bounded `cat`, `sed`, `rg`, `sha256sum`, `date -u`, exact-path `git status --short -- ...`, `git rev-parse HEAD`, and leased `apply_patch` writes. Read-only status showed no changes to either imported Lean source; HEAD matched baseline. Hash commands exited 0. Reading a guessed `NativeFreshScopeAllocation.lean` path produced `sed: ... No such file or directory`; the actual allocation definitions were then read from `NativeFreshScopeTransport.lean`. This was a locator failure, not a Lean diagnostic. Source availability was initially tested before its file existed; the later read and hash succeeded.

The inspected pin is `leanprover/lean4:v4.35.0`, library `YulangClosure`, no external packages, project process arguments `-j1 -M1024`. Actual Lean/Lake versions, module checking, proof goals/diagnostics, checker script, type-print output and complete transitive axiom results: **NOT_RUN**, explicitly prohibited by R145. No execution-unavailable/install claim is made. No Rust/Cargo/test command ran.

Represented cases: every finite native `Transformer` / `State`, default/absent entry, stamped inputs, conditional missing guards, inherited and newly introduced protection, release tombstones, arbitrary finite supports, shared maps and duplicate copy keys. Omitted correspondence: sorted-vector normalization/Rust loops, fallible allocation, origins/regions, failed-attempt cleanup, actual native incoming-state encoding, demand/use-instance semantics, source witness construction and full-language closure.

Verification handoff if a later packet authorizes execution: assign the build/cache owner, verify frozen hashes, then run the skill's `check_lean.py` for module `YulangClosure.NativeScopeFreshMapR145` with all seven fully qualified theorem names listed above/in the file. Inspect actual first diagnostics and repair under a renewed exact lease. No checker command is authorized by this receipt itself.

Resource: one leaf, no children, no heavy execution, no measured CPU/RSS; author work within the 600-second limit. Exact wall time was not instrumented. Further construction stops at this frozen revision. **WRITES STOPPED** on both leased paths; no descendant or generated-output leases. Pending fresh independent review and primary adjudication/integration. Handoff byte hash is returned separately after the final write.
