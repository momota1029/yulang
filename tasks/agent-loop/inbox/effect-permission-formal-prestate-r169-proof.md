# R169 proof handoff — revision 1

Sprint: `EFFECT-PERMISSION-FORMAL-PRESTATE/20261102-R169`, contract revision 1,
SHA-256 `59a91fc03524dd9b078d79a929846f63421d29497633dccbd18c7533b0e9394f`.
Activation receipt SHA-256:
`684b18483a2f18b77a3f4d254089a61a88081972c2089be825c9bc21772a3b20`.
Assignment/actual worker: `/root/formal_entry_prestate_r169_proof`.
Requested: registered lean_prover, Sol/high; actual model/effort: UNKNOWN.
Active-work acknowledgement sent to primary at entry; actual command sessions
were `17988` and `11734`, both completed. No descendants.
Baseline: supplied yulang3 HEAD `87ddd80c3f82629337c4a01f297d800a9ecb84f4`.
Only authored paths are this handoff and
`notes/theory/lean/YulangClosure/FormalEntryPrestateBridgeR169.lean`.

Outcome: **CONSTRUCTED, FINAL REPAIR UNCHECKED**. Both allowed focused checks
failed; neither reached the helper's new-theorem audit. No R169 theorem is
claimed kernel-accepted or independently reviewed. The final source repair is
based on actual diagnostics and the pinned Option source. The two-check bound
is exhausted. No third execution was attempted.

## Original claim, authority and quantifiers

The original parent remains
`YulangClosure.SourceProblem.InferenceSoundness`, `Contracts.lean:127`:
for every supported `s`, original scope `x`, generated `d` and successful
solution `a`, produce ONE shared `e` with
`sourceJudgment s x e ∧ sameScoped s x e a`. It is a proposition definition,
not a constructed concrete instance. R169 supplies no whole-language typing,
`LocalLaws`, semantic adoption or production promotion.

Sources actually consulted: `docs/yulang-whole-proof-closure-ja.md` §1;
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1–3,
including its original-scope/shared-witness requirement and current correction
notice in the whole-proof guide; opening corrections of
`docs/yulang-operational-type-safety-ja.tex` and
`docs/yulang-source-type-safety-ja.tex`; authoritative
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2;
`notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–5.
Research manuscripts are not semantic authority. The effect policy is an open
input permission to subtract the specified concrete effect, not a closed
input envelope. This bridge does not adopt a different effect policy.

R169 source handoff:
`tasks/agent-loop/inbox/effect-permission-formal-prestate-r169-source.md`,
SHA-256 `83b73f52a0b4526d51c8ea03683788accb8f2c48a2b58a74eb01c8c3fcf48eea`;
current audit SHA-256
`7004a57f14b79c73450c68431743ef7401232195b7d63c85d55f76f04eabb33d`.
The Rust files were read only at the assigned locations. No Rust build/test.

## Construction and represented cases

All declarations below are in `YulangClosure.FormalEntryPrestateBridgeR169`.
The universally quantified finite model uses arbitrary `Id : Type` with
`DecidableEq Id`; complete branded identities are a source interpretation,
not inferred from numeric keys. `Raw` retains finite formals, recipes,
owner-local raw expressions, source-owner reads, occupied domains, parameter-ID
registration map and prior publication state. `inputs` erases annotations only
when projecting the same raw expressions into R39. Its retained-registration
list is computed from the prior retained permission vector.

`Collected.lambda` reads the actual Lambda parameter ID and its optional
annotation, requires an effect row, looks up the registration using that same
parameter ID, and uses that registration's scope. There is no parallel
annotation table or separately chosen action annotation.
`collected_parameter_payload` records those exact reads. Collector provenance
and constructor acceptance remain separate: collection does not establish all
constructor guards. Native source uniqueness/branding and the actual executor
calling with this exact collected payload still require source correspondence.

`Trace` is a finite indexed event history. Its constructors extend one prefix
by one event: collect, row/arity read, registration read, identity checks,
owner/local-Lambda reads, fresh-domain/retained checks, entry read, exact
concrete copy (or empty branch), successful symbolic equality (or absent-tail
branch), publication and resource sampling. There is no `Valid`, `prepare`,
`permissionFor` or final record-equality transition premise. `entry_prepared`
derives the R39 guard conjunction from those raw event premises.

`successful_nonempty` states, for every successful trace and nonempty row,
existence of the SAME `p` such that R39 `prepare (inputs x) a = some (f,r,port)`
and `permissionFor a f r port = some p`, `pending = some p`, and after-state
is exactly prior permissions appended with `[p]`, prior links appended with
R39 symbolic links, and unchanged projected inflow; `p.concrete = r.concrete`.
`duplicate_order_preserved` retains `[first,first,last]` in that exact order.
`successful_empty` states `permissionFor = none`, `pending = none` and unchanged
permission vector. Symbolic equality occurs in the linked phase before publish.
`duplicate_guard_derived` derives absence from the actual prior records;
`retained_input_rejected` and `malformed_input_rejected` derive R39 rejection.
Explicit no-row, too-many-variable, missing-registration and already-retained
error events are present. Post-publication `sampleError` retains changed state;
`sample_error_changed_state` rules out equality with the pre-state for every
nonempty row. The concrete finite examples show symbolic `[7,7,11]` publication,
both successful sampling and failure after publication, and an empty row.

Omissions: this is only the R39 publication projection. It does not model byte
accounting, allocator capacity, scratch restoration, exact effect levels,
variable lookup implementation, propagation or caller-owned rollback. Successful
reserve/tail/equality/sample outcomes are supplied event observations, not
proven native calls. Early failure events are selected cases, not an exhaustive
Rust-error semantics. Raw `other` retains non-Lambda expression identities;
other language constructors remain obligations of the unchanged parent.

## Parent application and precise remaining owner

`selected_endpoint_application` applies the derived equations directly to
`YulangClosure.SuppressionPermissionR116.selected_endpoint_member` for the SAME
appended `p`. It discharges only R116's producer `prepared` and `retained`
arguments, conditionally on the modeled successful trace. The first native
bridge still needed is authentication that the actual Rust constructor run,
with its pre-state and exact collector action, realizes this event history.
Luna's source mapping supplies a reviewed-by-others input to this gate, not a
Lean execution simulation. The next consumer premises are R116 `SelectedSource`
for the same row, complete operation/declaration matching and actual endpoint
family decoding. Owner: primary's source/native consumer lane. R45 extraction,
R54 state/batch ownership, actual consumer execution and whole shared-witness
InferenceSoundness/A-B obligations remain OPEN. The current native reader is
evidence-only; there is no connected Catch/subtraction consumer here.

## Frozen artifact and dependencies

Artifact SHA-256: `bb0aaffe95f99881b089807a202991c4349a7c61e9ebb0f42f56d7f080a7baf4`.

- `notes/theory/lean/YulangClosure/AuthenticatedResidualConsumerR49.lean`: `4fc4380f3ad1827ecf155f982e5186b32d6d66d91909039fb118063d8f1e2df2`
- `notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean`: `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`
- `notes/theory/lean/YulangClosure/CurrentEmissionOwnershipR47.lean`: `d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c`
- `notes/theory/lean/YulangClosure/FormalEntryPrestateBridgeR169.lean`: `bb0aaffe95f99881b089807a202991c4349a7c61e9ebb0f42f56d7f080a7baf4`
- `notes/theory/lean/YulangClosure/InternalPermissionIncidenceR45.lean`: `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f`
- `notes/theory/lean/YulangClosure/NativeResidualPublicationR51.lean`: `78a729b25e95812ba292c4e625ec69e46ff5eb70ff3ac2ae5b85dd1b33214d61`
- `notes/theory/lean/YulangClosure/OwnedResidualProjectionR54.lean`: `cc5d0b01485560e5091ce454b066ca2fc41eb350eee24ae525133a13bed401c9`
- `notes/theory/lean/YulangClosure/PerCallResidualPublicationR52.lean`: `d0ffaad36139148c3898d70c9da2e03d1b0e17cbb8b71841f751a8720570e73e`
- `notes/theory/lean/YulangClosure/ProviderEntryArrivalR48.lean`: `b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575`
- `notes/theory/lean/YulangClosure/SuppressionPermissionR116.lean`: `2aed350468964d90d8d83714177fff77d477e3df0846ae23150194bd76270e3a`
- `notes/theory/lean/YulangClosure/WholePublicationResidualR53.lean`: `dc9c89e562f905c2c6284fd15eb82e9482a82bc9b2881f567c3454198318f391`

Additional frozen inputs (all hash-matched at startup and final read):

- R118 `NativePermissionDecoderR118.lean`: `f976e0b3b5e8b2b70ee902bdca30ce140db503a4972e8cf1b621892b57bf5d27`.
- Parent `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`.
- `candidate_source.rs`: `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`.
- `candidate_effect.rs`: `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15`.
- `lib.rs`: `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`.
- `lean-toolchain`: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`.
- `lakefile.toml`: `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`.
- `lake-manifest.json`: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.

## Environment, repairs and next exact check

Read-only `elan which lake` resolved the native
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
The initial root-directory lookup warned that release querying failed and used
the installed 4.35.0; a final lookup from the pinned project returned the same
path without that warning. All actual version invocations in the project
reported Lake `5.0.0-src+eb6cafb` (Lean 4.35.0) and Lean 4.35.0 commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release, x86_64-unknown-linux-gnu.

Check 1 failed for a missing explicit `Id : Type` binder on erasure and untyped
existentials. Those were repaired before check 2. Check 2 failed only at the
source-Lambda do-bind simplification and two generic example `decide` calls.
Final unexecuted repair adds the pinned `Option.bind_eq_bind` theorem
(`src/lean/Init/Data/Option/Lemmas.lean:200`) before `Option.bind_some`, and uses
`simp [exampleRaw]` on the empty occupied/retained domains. A relative-path
repair command was initially run from the project with a root-relative path;
it raised FileNotFoundError without writes, then the exact leased path was
repaired from the repository root. Full material Lean failures follow below.

All 18 authored theorem declarations require their printed types and complete
transitive axiom audits. **R169 axiom results: NOT RUN**, because both builds
failed before audit generation. Dependency R116 reports in the logs are real
replayed build output and must not be reported as R169 axiom acceptance.
Source search across the complete local import cone found only two comment
matches for `axiom`/`audit`; no proof hole, project axiom or checker bypass was
introduced. Source grep is not a transitive axiom audit.

Next check needs primary-owned verification authority because this packet's
two-check cap is spent. Exact command over the final repaired bytes:

```sh
python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py --lake /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --module YulangClosure.FormalEntryPrestateBridgeR169 --timeout 120 --theorem YulangClosure.FormalEntryPrestateBridgeR169.erased_source_read --theorem YulangClosure.FormalEntryPrestateBridgeR169.collected_parameter_payload --theorem YulangClosure.FormalEntryPrestateBridgeR169.entry_prepared --theorem YulangClosure.FormalEntryPrestateBridgeR169.copied_exact --theorem YulangClosure.FormalEntryPrestateBridgeR169.linked_exact --theorem YulangClosure.FormalEntryPrestateBridgeR169.published_exact --theorem YulangClosure.FormalEntryPrestateBridgeR169.successful_nonempty --theorem YulangClosure.FormalEntryPrestateBridgeR169.successful_empty --theorem YulangClosure.FormalEntryPrestateBridgeR169.duplicate_guard_derived --theorem YulangClosure.FormalEntryPrestateBridgeR169.retained_input_rejected --theorem YulangClosure.FormalEntryPrestateBridgeR169.malformed_input_rejected --theorem YulangClosure.FormalEntryPrestateBridgeR169.sample_error_changed_state --theorem YulangClosure.FormalEntryPrestateBridgeR169.selected_endpoint_application --theorem YulangClosure.FormalEntryPrestateBridgeR169.duplicate_order_preserved --theorem YulangClosure.FormalEntryPrestateBridgeR169.finite_entry_example --theorem YulangClosure.FormalEntryPrestateBridgeR169.finite_symbolic_publication_example --theorem YulangClosure.FormalEntryPrestateBridgeR169.finite_symbolic_success_and_error_example --theorem YulangClosure.FormalEntryPrestateBridgeR169.finite_empty_example
```

The helper builds the explicit module first, then checks every declaration is a
theorem and prints its exact type and transitive axioms. No root import is
leased or modified; default/full build was not requested or run.

## Resources, generated outputs and stop receipt

Limits: 2400 seconds packet; two focused checks each <=120 seconds; one CPU;
project `-j1 -M1024`. Actual checks: 1.476 and 1.278 seconds, both exit 1.
Final check peak child RSS 793640 KiB, CPU user/system 1.048/0.229 seconds.
Existing `.lake` remains 98 MiB. No separate environment/cache/target/dependency
or persistent scratch was created. The checker failed before making its
ordinary temporary audit source, so no audit scratch path exists. Generated
R169 output observed: only
`notes/theory/lean/.lake/build/ir/YulangClosure/FormalEntryPrestateBridgeR169.setup.json`
(1900 bytes); no R169 `.olean`/`.ilean` was produced. Lake also controls its
ordinary traces under the assigned existing cache. No Lake process remains.

Writer state: **STOPPED WRITING** after this frozen handoff revision. No
unresolved descendants. Exact two path leases remain untouched for Luna's
review/handoff; cache ownership can be reassigned by the primary after receipt.
No scheduling, shared status, questions, Rust, configuration, dependencies or
Git mutation. Pending successful verification, independent proof/source review
and primary integration. This handoff is not self-certification.

## Focused check 1 (material evidence)

Command: `python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py --lake /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --module YulangClosure.FormalEntryPrestateBridgeR169 --timeout 120 --theorem YulangClosure.FormalEntryPrestateBridgeR169.erased_source_read --theorem YulangClosure.FormalEntryPrestateBridgeR169.collected_parameter_payload --theorem YulangClosure.FormalEntryPrestateBridgeR169.entry_prepared --theorem YulangClosure.FormalEntryPrestateBridgeR169.copied_exact --theorem YulangClosure.FormalEntryPrestateBridgeR169.linked_exact --theorem YulangClosure.FormalEntryPrestateBridgeR169.published_exact --theorem YulangClosure.FormalEntryPrestateBridgeR169.successful_nonempty --theorem YulangClosure.FormalEntryPrestateBridgeR169.successful_empty --theorem YulangClosure.FormalEntryPrestateBridgeR169.duplicate_guard_derived --theorem YulangClosure.FormalEntryPrestateBridgeR169.retained_input_rejected --theorem YulangClosure.FormalEntryPrestateBridgeR169.malformed_input_rejected --theorem YulangClosure.FormalEntryPrestateBridgeR169.sample_error_changed_state --theorem YulangClosure.FormalEntryPrestateBridgeR169.selected_endpoint_application --theorem YulangClosure.FormalEntryPrestateBridgeR169.duplicate_order_preserved`

Elapsed: 1.476 seconds; exit 1.

```text
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --version
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
[exit 0]
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache env lean --version
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
[exit 0]
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache build +YulangClosure.FormalEntryPrestateBridgeR169
⚠ [11/12] Replayed YulangClosure.SuppressionPermissionR116
warning: YulangClosure/SuppressionPermissionR116.lean:126:0: automatically included section variable(s) unused in theorem `YulangClosure.SuppressionPermissionR116.same_source_row`:
  [DecidableEq Id]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Id] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: YulangClosure/SuppressionPermissionR116.lean:157:0: automatically included section variable(s) unused in theorem `YulangClosure.SuppressionPermissionR116.same_owner_selected_join`:
  [DecidableEq Id]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Id] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: YulangClosure/SuppressionPermissionR116.lean:166:0: automatically included section variable(s) unused in theorem `YulangClosure.SuppressionPermissionR116.empty_concrete_no_retained`:
  [DecidableEq Id]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Id] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: YulangClosure/SuppressionPermissionR116.lean:196:19: This simp argument is unused:
  Ne.symm different

Hint: Omit it from the simp argument list.
  [apply] simp [different]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
info: YulangClosure/SuppressionPermissionR116.lean:201:0: @YulangClosure.SuppressionPermissionR116.producer_facts : ∀ {Id : Type} [inst : DecidableEq Id]
  (e : YulangClosure.ComputationPermissionEntryR39.Inputs Id)
  (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id)
  (p : YulangClosure.ComputationPermissionEntryR39.Permission Id),
  YulangClosure.ComputationPermissionEntryR39.prepare e a = some (f, r, port) →
    YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port = some p →
      YulangClosure.SuppressionPermissionR116.ProducerFacts e a f r port p
info: YulangClosure/SuppressionPermissionR116.lean:202:0: 'YulangClosure.SuppressionPermissionR116.producer_facts' depends on axioms: [propext, Quot.sound]
info: YulangClosure/SuppressionPermissionR116.lean:203:0: @YulangClosure.SuppressionPermissionR116.operation_match_identity : ∀ {Id : Type} [inst : DecidableEq Id]
  (provider arm : YulangClosure.SuppressionPermissionR116.Operation Id),
  YulangClosure.SuppressionPermissionR116.operationMatch provider arm = true →
    provider.identity = arm.identity ∧ provider.declaration = arm.declaration ∧ provider.family = arm.family
info: YulangClosure/SuppressionPermissionR116.lean:204:0: 'YulangClosure.SuppressionPermissionR116.operation_match_identity' does not depend on any axioms
info: YulangClosure/SuppressionPermissionR116.lean:205:0: @YulangClosure.SuppressionPermissionR116.selected_provider_member : ∀ {Id : Type} [inst : DecidableEq Id]
  (e : YulangClosure.ComputationPermissionEntryR39.Inputs Id)
  (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id)
  (p : YulangClosure.ComputationPermissionEntryR39.Permission Id)
  (provider arm : YulangClosure.SuppressionPermissionR116.Operation Id),
  YulangClosure.ComputationPermissionEntryR39.prepare e a = some (f, r, port) →
    YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port = some p →
      YulangClosure.SuppressionPermissionR116.SelectedSource a r arm →
        YulangClosure.SuppressionPermissionR116.operationMatch provider arm = true →
          YulangClosure.SuppressionPermissionR116.ProducerFacts e a f r port p ∧ provider.family ∈ p.concrete
info: YulangClosure/SuppressionPermissionR116.lean:206:0: 'YulangClosure.SuppressionPermissionR116.selected_provider_member' depends on axioms: [propext, Quot.sound]
info: YulangClosure/SuppressionPermissionR116.lean:207:0: @YulangClosure.SuppressionPermissionR116.selected_endpoint_member : ∀ {Id : Type} [inst : DecidableEq Id]
  (e : YulangClosure.ComputationPermissionEntryR39.Inputs Id)
  (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port endpoint : Id)
  (p : YulangClosure.ComputationPermissionEntryR39.Permission Id)
  (provider arm : YulangClosure.SuppressionPermissionR116.Operation Id),
  YulangClosure.ComputationPermissionEntryR39.prepare e a = some (f, r, port) →
    YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port = some p →
      YulangClosure.SuppressionPermissionR116.SelectedSource a r arm →
        YulangClosure.SuppressionPermissionR116.operationMatch provider arm = true →
          endpoint = provider.family → endpoint ∈ p.concrete
info: YulangClosure/SuppressionPermissionR116.lean:208:0: 'YulangClosure.SuppressionPermissionR116.selected_endpoint_member' depends on axioms: [propext, Quot.sound]
info: YulangClosure/SuppressionPermissionR116.lean:209:0: @YulangClosure.SuppressionPermissionR116.same_source_row : ∀ {Id : Type} [DecidableEq Id]
  (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (r other : YulangClosure.ComputationPermissionEntryR39.Row Id),
  a.annotation.row = some r → a.annotation.row = some other → r = other
info: YulangClosure/SuppressionPermissionR116.lean:210:0: 'YulangClosure.SuppressionPermissionR116.same_source_row' does not depend on any axioms
info: YulangClosure/SuppressionPermissionR116.lean:211:0: @YulangClosure.SuppressionPermissionR116.internal_certificate_member : ∀ {Id : Type} [inst : DecidableEq Id]
  {Artifact Term Fact : Type} [inst_1 : DecidableEq Artifact] [inst_2 : DecidableEq Term] [inst_3 : DecidableEq Fact]
  (e : YulangClosure.InternalPermissionIncidenceR45.Inputs Artifact Id Term Fact)
  (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id)
  (q : YulangClosure.InternalPermissionIncidenceR45.Query Artifact Id)
  (probe : YulangClosure.InternalPermissionIncidenceR45.Probe Artifact Id Term Fact)
  (out : YulangClosure.InternalPermissionIncidenceR45.Certificate Artifact Id Term Fact)
  (provider arm : YulangClosure.SuppressionPermissionR116.Operation Id),
  YulangClosure.ComputationPermissionEntryR39.prepare e.source a = some (f, r, port) →
    YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port = some probe.permission →
      YulangClosure.InternalPermissionIncidenceR45.extract e q probe = some out →
        YulangClosure.SuppressionPermissionR116.SelectedSource a r arm →
          YulangClosure.SuppressionPermissionR116.operationMatch provider arm = true →
            out.permission.registration = a.registration ∧
              out.permission.occurrence = a.occurrence ∧
                out.permission.owner = f.owner ∧ provider.family ∈ out.permission.concrete
info: YulangClosure/SuppressionPermissionR116.lean:212:0: 'YulangClosure.SuppressionPermissionR116.internal_certificate_member' depends on axioms: [propext, Quot.sound]
info: YulangClosure/SuppressionPermissionR116.lean:213:0: @YulangClosure.SuppressionPermissionR116.same_owner_selected_join : ∀ {Id : Type} [DecidableEq Id] {State Batch : Type}
  [inst : DecidableEq State] [inst_1 : DecidableEq Batch]
  (permission :
    YulangClosure.OwnedResidualProjectionR54.Owned State Batch
      (YulangClosure.ComputationPermissionEntryR39.Permission Id))
  (arm :
    YulangClosure.OwnedResidualProjectionR54.Owned State Batch (YulangClosure.SuppressionPermissionR116.Operation Id)),
  permission.owner = arm.owner →
    YulangClosure.OwnedResidualProjectionR54.join permission arm =
      some { owner := permission.owner, value := (permission.value, arm.value) }
info: YulangClosure/SuppressionPermissionR116.lean:214:0: 'YulangClosure.SuppressionPermissionR116.same_owner_selected_join' depends on axioms: [propext]
info: YulangClosure/SuppressionPermissionR116.lean:215:0: @YulangClosure.SuppressionPermissionR116.empty_concrete_no_retained : ∀ {Id : Type} [DecidableEq Id]
  (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id),
  r.concrete = [] → YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port = none
info: YulangClosure/SuppressionPermissionR116.lean:216:0: 'YulangClosure.SuppressionPermissionR116.empty_concrete_no_retained' depends on axioms: [propext]
info: YulangClosure/SuppressionPermissionR116.lean:217:0: @YulangClosure.SuppressionPermissionR116.different_formal_not_same_permission : ∀ {Id : Type} [inst : DecidableEq Id]
  (p : YulangClosure.ComputationPermissionEntryR39.Permission Id)
  (a : YulangClosure.ComputationPermissionEntryR39.Action Id),
  p.registration ≠ a.registration →
    ∀ (e : YulangClosure.ComputationPermissionEntryR39.Inputs Id)
      (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
      (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id),
      ¬YulangClosure.SuppressionPermissionR116.ProducerFacts e a f r port p
info: YulangClosure/SuppressionPermissionR116.lean:218:0: 'YulangClosure.SuppressionPermissionR116.different_formal_not_same_permission' depends on axioms: [propext]
info: YulangClosure/SuppressionPermissionR116.lean:219:0: @YulangClosure.SuppressionPermissionR116.same_spelling_different_operation_rejected : ∀ {Id : Type}
  [inst : DecidableEq Id] (provider arm : YulangClosure.SuppressionPermissionR116.Operation Id),
  provider.spelling = arm.spelling →
    provider.identity ≠ arm.identity →
      provider.spelling = arm.spelling ∧ YulangClosure.SuppressionPermissionR116.operationMatch provider arm = false
info: YulangClosure/SuppressionPermissionR116.lean:220:0: 'YulangClosure.SuppressionPermissionR116.same_spelling_different_operation_rejected' depends on axioms: [propext]
info: YulangClosure/SuppressionPermissionR116.lean:221:0: @YulangClosure.SuppressionPermissionR116.provider_handler_family_mismatch : ∀ {Id : Type} [inst : DecidableEq Id]
  (provider arm : YulangClosure.SuppressionPermissionR116.Operation Id),
  provider.family ≠ arm.family → YulangClosure.SuppressionPermissionR116.operationMatch provider arm = false
info: YulangClosure/SuppressionPermissionR116.lean:222:0: 'YulangClosure.SuppressionPermissionR116.provider_handler_family_mismatch' depends on axioms: [propext]
info: YulangClosure/SuppressionPermissionR116.lean:223:0: @YulangClosure.SuppressionPermissionR116.open_input_write_boundary : ∀ {Id : Type} [inst : DecidableEq Id]
  (signal write : Id),
  write ≠ signal →
    signal ∈ [signal] ∧
      write ∈ [signal, write] ∧
        ¬write ∈ [signal] ∧ List.filter (fun member => member != signal) [signal, write] = [write]
info: YulangClosure/SuppressionPermissionR116.lean:224:0: 'YulangClosure.SuppressionPermissionR116.open_input_write_boundary' depends on axioms: [propext]
✖ [12/12] Building YulangClosure.FormalEntryPrestateBridgeR169 (1.2s)
trace: .> LEAN_PATH=/home/momota1029/rust/yulang/notes/theory/lean/.lake/build/lib/lean /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 /home/momota1029/rust/yulang/notes/theory/lean/YulangClosure/FormalEntryPrestateBridgeR169.lean -o /home/momota1029/rust/yulang/notes/theory/lean/.lake/build/lib/lean/YulangClosure/FormalEntryPrestateBridgeR169.olean -i /home/momota1029/rust/yulang/notes/theory/lean/.lake/build/lib/lean/YulangClosure/FormalEntryPrestateBridgeR169.ilean -c /home/momota1029/rust/yulang/notes/theory/lean/.lake/build/ir/YulangClosure/FormalEntryPrestateBridgeR169.c --setup /home/momota1029/rust/yulang/notes/theory/lean/.lake/build/ir/YulangClosure/FormalEntryPrestateBridgeR169.setup.json --json
error: YulangClosure/FormalEntryPrestateBridgeR169.lean:31:33: Application type mismatch: The argument
  Id
has type
  Type → Type
but is expected to have type
  Type
in the application
  Expression Id
error: YulangClosure/FormalEntryPrestateBridgeR169.lean:31:49: Application type mismatch: The argument
  Id
has type
  Type → Type
but is expected to have type
  Type
in the application
  SourceExpr Id
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:57:4: declaration uses `sorry`
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:61:4: declaration uses `sorry`
error: YulangClosure/FormalEntryPrestateBridgeR169.lean:73:4: unsolved goals
case pos
Id : Type
inst✝ : DecidableEq Id
owner : Id
rest : List (Id × List (Expression Id))
ih : sorry = Option.map (List.map eraseExpression) sorry
key : Id
expressions : List (Expression Id)
same : key = owner
⊢ sorry () = Option.map (List.map eraseExpression) (sorry ())
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:73:12: declaration uses `sorry`
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:73:12: This simp argument is unused:
  eraseSources

Hint: Omit it from the simp argument list.
  [apply] simp [localSource, readSource, same]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:73:26: This simp argument is unused:
  localSource

Hint: Omit it from the simp argument list.
  [apply] simp [eraseSources, readSource, same]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:73:39: This simp argument is unused:
  readSource

Hint: Omit it from the simp argument list.
  [apply] simp [eraseSources, localSource, same]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:73:51: This simp argument is unused:
  same

Hint: Omit it from the simp argument list.
  [apply] simp [eraseSources, localSource, readSource]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
error: YulangClosure/FormalEntryPrestateBridgeR169.lean:95:34: Invalid dotted identifier notation: The expected type of `.lambda` could not be determined

Hint: Using one of these would be unambiguous:
  [apply] `Registration.lambda`
  [apply] `SourceExpr.lambda`
  [apply] `Collected.lambda`
  [apply] `Expression.lambda`
  [apply] `InternalPermissionIncidenceR45.Certificate.lambda`
  [apply] `InternalPermissionIncidenceR45.Construction.lambda`
  [apply] `InternalPermissionIncidenceR45.Query.lambda`
error: YulangClosure/FormalEntryPrestateBridgeR169.lean:96:6: Invalid field notation: Type of
  parameter
is not known; cannot resolve field `annotation`

Hint: Consider replacing the field projection with a call to one of the following:
  • `Action.annotation`
  • `Parameter.annotation`
  • `ProviderEntryArrivalR48.ViewOrigin.annotation`
error: YulangClosure/FormalEntryPrestateBridgeR169.lean:97:45: Invalid field notation: Type of
  parameter
is not known; cannot resolve field `id`

Hint: Consider replacing the field projection with a call to one of the following:
  • `id`
  • `Function.LeftInverse.id`
  • `Function.RightInverse.id`
  • `Std.CancellationContext.id`
  • `Std.CancellationContext.State.id`
  • `Std.Internal.LawfulMonadLiftBindFunction.id`
  • `Parameter.id`
error: YulangClosure/FormalEntryPrestateBridgeR169.lean:209:14: unsolved goals
case entry.fresh.source.identities.registered.row.refine_2
Id : Type
inst✝ : DecidableEq Id
x : Raw Id
a : Action Id
f : Registration Id
r : Row Id
port : Id
hp : f.entry = some port
hr : ¬a.registration ∈ List.map (fun p => p.registration) x.before.permissions
hd : ¬f.recipe ∈ x.occupiedDomains
ho : ownerLookup x.owners a.occurrence = some a.annotation.owner
expressions : List (Expression Id)
annotation : Option (Annotation Id)
hs : readSource x.sources f.owner = some expressions
hl : expressions[f.lambda]? = some (Expression.lambda a.occurrence { id := f.parameter, annotation := annotation })
owner : f.owner = a.annotation.owner
role : f.role = Role.computation
scope : f.scope = a.scope
recipe : x.recipes[f.recipe]? = some f.parameter
hf : x.formals[a.registration]? = some f
collected : Trace x a Phase.collected x.before
rowRead : a.annotation.row = some r
arity : r.variables.length ≤ 1
⊢ (do
      let expressions ← localSource sorry f.owner
      let expression ← expressions[f.lambda]?
      match expression with
        | SourceExpr.lambda occurrence parameter => some (occurrence, parameter)
        | SourceExpr.other occurrence => none) =
    some (a.occurrence, f.parameter)
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:208:28: declaration uses `sorry`
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:210:76: declaration uses `sorry`
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:210:76: declaration uses `sorry`
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:210:76: declaration uses `sorry`
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:210:76: declaration uses `sorry`
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:210:76: declaration uses `sorry`
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:209:49: This simp argument is unused:
  erased_source_read

Hint: Omit it from the simp argument list.
  [apply] simp only [sourceLambda, inputs, hs, Option.map_some, Option.bind_some, List.getElem?_map, hl,
    eraseExpression]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:209:69: This simp argument is unused:
  hs

Hint: Omit it from the simp argument list.
  [apply] simp only [sourceLambda, inputs, erased_source_read, Option.map_some, Option.bind_some, List.getElem?_map, hl,
    eraseExpression]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:210:18: This simp argument is unused:
  Option.map_some

Hint: Omit it from the simp argument list.
  [apply] simp only [sourceLambda, inputs, erased_source_read, hs, Option.bind_some, List.getElem?_map, hl,
    eraseExpression]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:210:35: This simp argument is unused:
  Option.bind_some

Hint: Omit it from the simp argument list.
  [apply] simp only [sourceLambda, inputs, erased_source_read, hs, Option.map_some, List.getElem?_map, hl,
    eraseExpression]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:210:53: This simp argument is unused:
  List.getElem?_map

Hint: Omit it from the simp argument list.
  [apply] simp only [sourceLambda, inputs, erased_source_read, hs, Option.map_some, Option.bind_some, hl,
    eraseExpression]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:210:72: This simp argument is unused:
  hl

Hint: Omit it from the simp argument list.
  [apply] simp only [sourceLambda, inputs, erased_source_read, hs, Option.map_some, Option.bind_some, List.getElem?_map,
    eraseExpression]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:210:76: This simp argument is unused:
  eraseExpression

Hint: Omit it from the simp argument list.
  [apply] simp only [sourceLambda, inputs, erased_source_read, hs, Option.map_some, Option.bind_some, List.getElem?_map,
    hl]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Some required targets logged failures:
- YulangClosure.FormalEntryPrestateBridgeR169
error: build failed
[exit 1]
FAIL: command failed with exit 1
```

## Focused check 2 (final permitted check)

Command: `python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py --lake /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --module YulangClosure.FormalEntryPrestateBridgeR169 --timeout 120 --theorem YulangClosure.FormalEntryPrestateBridgeR169.erased_source_read --theorem YulangClosure.FormalEntryPrestateBridgeR169.collected_parameter_payload --theorem YulangClosure.FormalEntryPrestateBridgeR169.entry_prepared --theorem YulangClosure.FormalEntryPrestateBridgeR169.copied_exact --theorem YulangClosure.FormalEntryPrestateBridgeR169.linked_exact --theorem YulangClosure.FormalEntryPrestateBridgeR169.published_exact --theorem YulangClosure.FormalEntryPrestateBridgeR169.successful_nonempty --theorem YulangClosure.FormalEntryPrestateBridgeR169.successful_empty --theorem YulangClosure.FormalEntryPrestateBridgeR169.duplicate_guard_derived --theorem YulangClosure.FormalEntryPrestateBridgeR169.retained_input_rejected --theorem YulangClosure.FormalEntryPrestateBridgeR169.malformed_input_rejected --theorem YulangClosure.FormalEntryPrestateBridgeR169.sample_error_changed_state --theorem YulangClosure.FormalEntryPrestateBridgeR169.selected_endpoint_application --theorem YulangClosure.FormalEntryPrestateBridgeR169.duplicate_order_preserved --theorem YulangClosure.FormalEntryPrestateBridgeR169.finite_entry_example --theorem YulangClosure.FormalEntryPrestateBridgeR169.finite_symbolic_publication_example --theorem YulangClosure.FormalEntryPrestateBridgeR169.finite_symbolic_success_and_error_example --theorem YulangClosure.FormalEntryPrestateBridgeR169.finite_empty_example`

Elapsed: 1.278 seconds; exit 1. Max child RSS: 793640 KiB; child CPU user/system: 1.048/0.229 s.

```text
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --version
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
[exit 0]
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache env lean --version
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
[exit 0]
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache build +YulangClosure.FormalEntryPrestateBridgeR169
⚠ [11/12] Replayed YulangClosure.SuppressionPermissionR116
warning: YulangClosure/SuppressionPermissionR116.lean:126:0: automatically included section variable(s) unused in theorem `YulangClosure.SuppressionPermissionR116.same_source_row`:
  [DecidableEq Id]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Id] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: YulangClosure/SuppressionPermissionR116.lean:157:0: automatically included section variable(s) unused in theorem `YulangClosure.SuppressionPermissionR116.same_owner_selected_join`:
  [DecidableEq Id]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Id] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: YulangClosure/SuppressionPermissionR116.lean:166:0: automatically included section variable(s) unused in theorem `YulangClosure.SuppressionPermissionR116.empty_concrete_no_retained`:
  [DecidableEq Id]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Id] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: YulangClosure/SuppressionPermissionR116.lean:196:19: This simp argument is unused:
  Ne.symm different

Hint: Omit it from the simp argument list.
  [apply] simp [different]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
info: YulangClosure/SuppressionPermissionR116.lean:201:0: @YulangClosure.SuppressionPermissionR116.producer_facts : ∀ {Id : Type} [inst : DecidableEq Id]
  (e : YulangClosure.ComputationPermissionEntryR39.Inputs Id)
  (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id)
  (p : YulangClosure.ComputationPermissionEntryR39.Permission Id),
  YulangClosure.ComputationPermissionEntryR39.prepare e a = some (f, r, port) →
    YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port = some p →
      YulangClosure.SuppressionPermissionR116.ProducerFacts e a f r port p
info: YulangClosure/SuppressionPermissionR116.lean:202:0: 'YulangClosure.SuppressionPermissionR116.producer_facts' depends on axioms: [propext, Quot.sound]
info: YulangClosure/SuppressionPermissionR116.lean:203:0: @YulangClosure.SuppressionPermissionR116.operation_match_identity : ∀ {Id : Type} [inst : DecidableEq Id]
  (provider arm : YulangClosure.SuppressionPermissionR116.Operation Id),
  YulangClosure.SuppressionPermissionR116.operationMatch provider arm = true →
    provider.identity = arm.identity ∧ provider.declaration = arm.declaration ∧ provider.family = arm.family
info: YulangClosure/SuppressionPermissionR116.lean:204:0: 'YulangClosure.SuppressionPermissionR116.operation_match_identity' does not depend on any axioms
info: YulangClosure/SuppressionPermissionR116.lean:205:0: @YulangClosure.SuppressionPermissionR116.selected_provider_member : ∀ {Id : Type} [inst : DecidableEq Id]
  (e : YulangClosure.ComputationPermissionEntryR39.Inputs Id)
  (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id)
  (p : YulangClosure.ComputationPermissionEntryR39.Permission Id)
  (provider arm : YulangClosure.SuppressionPermissionR116.Operation Id),
  YulangClosure.ComputationPermissionEntryR39.prepare e a = some (f, r, port) →
    YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port = some p →
      YulangClosure.SuppressionPermissionR116.SelectedSource a r arm →
        YulangClosure.SuppressionPermissionR116.operationMatch provider arm = true →
          YulangClosure.SuppressionPermissionR116.ProducerFacts e a f r port p ∧ provider.family ∈ p.concrete
info: YulangClosure/SuppressionPermissionR116.lean:206:0: 'YulangClosure.SuppressionPermissionR116.selected_provider_member' depends on axioms: [propext, Quot.sound]
info: YulangClosure/SuppressionPermissionR116.lean:207:0: @YulangClosure.SuppressionPermissionR116.selected_endpoint_member : ∀ {Id : Type} [inst : DecidableEq Id]
  (e : YulangClosure.ComputationPermissionEntryR39.Inputs Id)
  (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port endpoint : Id)
  (p : YulangClosure.ComputationPermissionEntryR39.Permission Id)
  (provider arm : YulangClosure.SuppressionPermissionR116.Operation Id),
  YulangClosure.ComputationPermissionEntryR39.prepare e a = some (f, r, port) →
    YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port = some p →
      YulangClosure.SuppressionPermissionR116.SelectedSource a r arm →
        YulangClosure.SuppressionPermissionR116.operationMatch provider arm = true →
          endpoint = provider.family → endpoint ∈ p.concrete
info: YulangClosure/SuppressionPermissionR116.lean:208:0: 'YulangClosure.SuppressionPermissionR116.selected_endpoint_member' depends on axioms: [propext, Quot.sound]
info: YulangClosure/SuppressionPermissionR116.lean:209:0: @YulangClosure.SuppressionPermissionR116.same_source_row : ∀ {Id : Type} [DecidableEq Id]
  (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (r other : YulangClosure.ComputationPermissionEntryR39.Row Id),
  a.annotation.row = some r → a.annotation.row = some other → r = other
info: YulangClosure/SuppressionPermissionR116.lean:210:0: 'YulangClosure.SuppressionPermissionR116.same_source_row' does not depend on any axioms
info: YulangClosure/SuppressionPermissionR116.lean:211:0: @YulangClosure.SuppressionPermissionR116.internal_certificate_member : ∀ {Id : Type} [inst : DecidableEq Id]
  {Artifact Term Fact : Type} [inst_1 : DecidableEq Artifact] [inst_2 : DecidableEq Term] [inst_3 : DecidableEq Fact]
  (e : YulangClosure.InternalPermissionIncidenceR45.Inputs Artifact Id Term Fact)
  (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id)
  (q : YulangClosure.InternalPermissionIncidenceR45.Query Artifact Id)
  (probe : YulangClosure.InternalPermissionIncidenceR45.Probe Artifact Id Term Fact)
  (out : YulangClosure.InternalPermissionIncidenceR45.Certificate Artifact Id Term Fact)
  (provider arm : YulangClosure.SuppressionPermissionR116.Operation Id),
  YulangClosure.ComputationPermissionEntryR39.prepare e.source a = some (f, r, port) →
    YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port = some probe.permission →
      YulangClosure.InternalPermissionIncidenceR45.extract e q probe = some out →
        YulangClosure.SuppressionPermissionR116.SelectedSource a r arm →
          YulangClosure.SuppressionPermissionR116.operationMatch provider arm = true →
            out.permission.registration = a.registration ∧
              out.permission.occurrence = a.occurrence ∧
                out.permission.owner = f.owner ∧ provider.family ∈ out.permission.concrete
info: YulangClosure/SuppressionPermissionR116.lean:212:0: 'YulangClosure.SuppressionPermissionR116.internal_certificate_member' depends on axioms: [propext, Quot.sound]
info: YulangClosure/SuppressionPermissionR116.lean:213:0: @YulangClosure.SuppressionPermissionR116.same_owner_selected_join : ∀ {Id : Type} [DecidableEq Id] {State Batch : Type}
  [inst : DecidableEq State] [inst_1 : DecidableEq Batch]
  (permission :
    YulangClosure.OwnedResidualProjectionR54.Owned State Batch
      (YulangClosure.ComputationPermissionEntryR39.Permission Id))
  (arm :
    YulangClosure.OwnedResidualProjectionR54.Owned State Batch (YulangClosure.SuppressionPermissionR116.Operation Id)),
  permission.owner = arm.owner →
    YulangClosure.OwnedResidualProjectionR54.join permission arm =
      some { owner := permission.owner, value := (permission.value, arm.value) }
info: YulangClosure/SuppressionPermissionR116.lean:214:0: 'YulangClosure.SuppressionPermissionR116.same_owner_selected_join' depends on axioms: [propext]
info: YulangClosure/SuppressionPermissionR116.lean:215:0: @YulangClosure.SuppressionPermissionR116.empty_concrete_no_retained : ∀ {Id : Type} [DecidableEq Id]
  (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id),
  r.concrete = [] → YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port = none
info: YulangClosure/SuppressionPermissionR116.lean:216:0: 'YulangClosure.SuppressionPermissionR116.empty_concrete_no_retained' depends on axioms: [propext]
info: YulangClosure/SuppressionPermissionR116.lean:217:0: @YulangClosure.SuppressionPermissionR116.different_formal_not_same_permission : ∀ {Id : Type} [inst : DecidableEq Id]
  (p : YulangClosure.ComputationPermissionEntryR39.Permission Id)
  (a : YulangClosure.ComputationPermissionEntryR39.Action Id),
  p.registration ≠ a.registration →
    ∀ (e : YulangClosure.ComputationPermissionEntryR39.Inputs Id)
      (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
      (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id),
      ¬YulangClosure.SuppressionPermissionR116.ProducerFacts e a f r port p
info: YulangClosure/SuppressionPermissionR116.lean:218:0: 'YulangClosure.SuppressionPermissionR116.different_formal_not_same_permission' depends on axioms: [propext]
info: YulangClosure/SuppressionPermissionR116.lean:219:0: @YulangClosure.SuppressionPermissionR116.same_spelling_different_operation_rejected : ∀ {Id : Type}
  [inst : DecidableEq Id] (provider arm : YulangClosure.SuppressionPermissionR116.Operation Id),
  provider.spelling = arm.spelling →
    provider.identity ≠ arm.identity →
      provider.spelling = arm.spelling ∧ YulangClosure.SuppressionPermissionR116.operationMatch provider arm = false
info: YulangClosure/SuppressionPermissionR116.lean:220:0: 'YulangClosure.SuppressionPermissionR116.same_spelling_different_operation_rejected' depends on axioms: [propext]
info: YulangClosure/SuppressionPermissionR116.lean:221:0: @YulangClosure.SuppressionPermissionR116.provider_handler_family_mismatch : ∀ {Id : Type} [inst : DecidableEq Id]
  (provider arm : YulangClosure.SuppressionPermissionR116.Operation Id),
  provider.family ≠ arm.family → YulangClosure.SuppressionPermissionR116.operationMatch provider arm = false
info: YulangClosure/SuppressionPermissionR116.lean:222:0: 'YulangClosure.SuppressionPermissionR116.provider_handler_family_mismatch' depends on axioms: [propext]
info: YulangClosure/SuppressionPermissionR116.lean:223:0: @YulangClosure.SuppressionPermissionR116.open_input_write_boundary : ∀ {Id : Type} [inst : DecidableEq Id]
  (signal write : Id),
  write ≠ signal →
    signal ∈ [signal] ∧
      write ∈ [signal, write] ∧
        ¬write ∈ [signal] ∧ List.filter (fun member => member != signal) [signal, write] = [write]
info: YulangClosure/SuppressionPermissionR116.lean:224:0: 'YulangClosure.SuppressionPermissionR116.open_input_write_boundary' depends on axioms: [propext]
✖ [12/12] Building YulangClosure.FormalEntryPrestateBridgeR169 (1.1s)
trace: .> LEAN_PATH=/home/momota1029/rust/yulang/notes/theory/lean/.lake/build/lib/lean /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 /home/momota1029/rust/yulang/notes/theory/lean/YulangClosure/FormalEntryPrestateBridgeR169.lean -o /home/momota1029/rust/yulang/notes/theory/lean/.lake/build/lib/lean/YulangClosure/FormalEntryPrestateBridgeR169.olean -i /home/momota1029/rust/yulang/notes/theory/lean/.lake/build/lib/lean/YulangClosure/FormalEntryPrestateBridgeR169.ilean -c /home/momota1029/rust/yulang/notes/theory/lean/.lake/build/ir/YulangClosure/FormalEntryPrestateBridgeR169.c --setup /home/momota1029/rust/yulang/notes/theory/lean/.lake/build/ir/YulangClosure/FormalEntryPrestateBridgeR169.setup.json --json
error: YulangClosure/FormalEntryPrestateBridgeR169.lean:210:14: unsolved goals
case entry.fresh.source.identities.registered.row.refine_2
Id : Type
inst✝ : DecidableEq Id
x : Raw Id
a : Action Id
f : Registration Id
r : Row Id
port : Id
hp : f.entry = some port
hr : ¬a.registration ∈ List.map (fun p => p.registration) x.before.permissions
hd : ¬f.recipe ∈ x.occupiedDomains
ho : ownerLookup x.owners a.occurrence = some a.annotation.owner
expressions : List (Expression Id)
annotation : Option (Annotation Id)
hs : readSource x.sources f.owner = some expressions
hl : expressions[f.lambda]? = some (Expression.lambda a.occurrence { id := f.parameter, annotation := annotation })
owner : f.owner = a.annotation.owner
role : f.role = Role.computation
scope : f.scope = a.scope
recipe : x.recipes[f.recipe]? = some f.parameter
hf : x.formals[a.registration]? = some f
collected : Trace x a Phase.collected x.before
rowRead : a.annotation.row = some r
arity : r.variables.length ≤ 1
⊢ (do
      let expressions ← some (List.map eraseExpression expressions)
      let expression ← expressions[f.lambda]?
      match expression with
        | SourceExpr.lambda occurrence parameter => some (occurrence, parameter)
        | SourceExpr.other occurrence => none) =
    some (a.occurrence, f.parameter)
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:211:35: This simp argument is unused:
  Option.bind_some

Hint: Omit it from the simp argument list.
  [apply] simp only [sourceLambda, inputs, erased_source_read, hs, Option.map_some, List.getElem?_map, hl,
    eraseExpression]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:211:53: This simp argument is unused:
  List.getElem?_map

Hint: Omit it from the simp argument list.
  [apply] simp only [sourceLambda, inputs, erased_source_read, hs, Option.map_some, Option.bind_some, hl,
    eraseExpression]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:211:72: This simp argument is unused:
  hl

Hint: Omit it from the simp argument list.
  [apply] simp only [sourceLambda, inputs, erased_source_read, hs, Option.map_some, Option.bind_some, List.getElem?_map,
    eraseExpression]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/FormalEntryPrestateBridgeR169.lean:211:76: This simp argument is unused:
  eraseExpression

Hint: Omit it from the simp argument list.
  [apply] simp only [sourceLambda, inputs, erased_source_read, hs, Option.map_some, Option.bind_some, List.getElem?_map,
    hl]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
error: YulangClosure/FormalEntryPrestateBridgeR169.lean:383:63: Expected type must not contain free variables
  ¬exampleFormal.recipe ∈ (exampleRaw concrete variables).occupiedDomains

Hint: Use the `+revert` option to automatically clean up and revert free variables
error: YulangClosure/FormalEntryPrestateBridgeR169.lean:383:75: Expected type must not contain free variables
  ¬(exampleAction concrete variables).registration ∈
      List.map (fun p => p.registration) (exampleRaw concrete variables).before.permissions

Hint: Use the `+revert` option to automatically clean up and revert free variables
Some required targets logged failures:
- YulangClosure.FormalEntryPrestateBridgeR169
error: build failed
[exit 1]
FAIL: command failed with exit 1
```
