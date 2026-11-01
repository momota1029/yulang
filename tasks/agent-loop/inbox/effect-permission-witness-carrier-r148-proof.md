# R148 Lean audit/application handoff

Revision 1; author `/root/r148_lean_audit`; sole lease is this path. Requested role: lean_prover; observed effective model/effort UNKNOWN. No descendants. Raw checker evidence follows; source application and final stop receipt follow in the same revision.

## Result and evidence limits

**Five named declarations accepted under their exact printed hypotheses; sixth unavailable because its dependency fails. Original A/B, whole-language effect hygiene, source/native correspondence and production remain OPEN.** This is a conditional-mathematics/kernel-audit result awaiting fresh independent review and primary adjudication. No new theorem or semantic definition was constructed. No Rust-to-Lean identification is proved or assumed.

The five actual audit results are each exactly `[propext, Quot.sound]`:

- `YulangClosure.NativeScopeTransformer.evaluate_rename`
- `YulangClosure.NativeFreshScopeTransport.fresh_evaluate`
- `YulangClosure.NativeFreshScopeTransport.fresh_evaluate_and_reuse`
- `YulangClosure.SuppressionPermissionR116.selected_endpoint_member`
- `YulangClosure.SuppressionPermissionR116.internal_certificate_member`

For `YulangClosure.PermissionMemberWitnessR119.selected_retained_member`, no printed actual type or axiom list exists in this run. R118 does not compile, and R119 has no import artifact; this is not a counterexample or evidence that the R119 statement is false. Failed R118 elaboration diagnostics contain `sorryAx`; those failed declarations are not delivered as accepted results. No holes, project axioms, bypasses, strengthened hypotheses, reduced source domain or circular typing definition were introduced.

## Actual execution receipts

Pinned native Lake: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`. The native version lookups passed: `Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)`; `Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`. Commands: `elan which lake` in project; native `lake --version`; native `lake --no-cache env lean --version`; all exit 0. CLI help confirms `--stdin`.

The first stdin audit attempt exited 1 before any theorem query: `<stdin>:1:0: error: object file /home/momota1029/rust/yulang/notes/theory/lean/.lake/build/lib/lean/YulangClosure/NativeScopeTransformer.olean of module YulangClosure.NativeScopeTransformer does not exist`. Four requested imports and 14 dependency modules were initially uncached. The primary then expressly authorized this finite build in the existing `.lake`, 480-second checker bound and 128-MiB growth cap. This invocation used a stricter 420-second combined bound. Bundled check_lean.py was inspected but not run: it creates prohibited scratch and a Lean source file. The equivalent stdin audit checks theorem declaration kind, printed types, complete axiom lists, and the same standard-axiom whitelist.

```text
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache --fail-fast build +YulangClosure.NativeScopeTransformer +YulangClosure.NativeFreshScopeTransport +YulangClosure.SuppressionPermissionR116 +YulangClosure.PermissionMemberWitnessR119
✔ [1/3] Built YulangClosure.NativeScopeTransformer (3.5s)
✔ [2/5] Built YulangClosure.NativeFreshScopeTransport (608ms)
✔ [3/5] Built YulangClosure.ComputationPermissionEntryR39 (1.2s)
✔ [4/13] Built YulangClosure.InternalPermissionIncidenceR45 (1.2s)
✔ [6/15] Built YulangClosure.CurrentEmissionOwnershipR47 (1.1s)
✔ [7/15] Built YulangClosure.ProviderEntryArrivalR48 (821ms)
✔ [8/15] Built YulangClosure.AuthenticatedResidualConsumerR49 (2.3s)
✔ [9/15] Built YulangClosure.NativeResidualPublicationR51 (1.6s)
✔ [10/15] Built YulangClosure.PerCallResidualPublicationR52 (932ms)
✔ [11/15] Built YulangClosure.WholePublicationResidualR53 (1.4s)
✔ [12/15] Built YulangClosure.OwnedResidualProjectionR54 (894ms)
⚠ [13/15] Built YulangClosure.SuppressionPermissionR116 (434ms)
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
✖ [14/15] Building YulangClosure.NativePermissionDecoderR118 (492ms)
trace: .> LEAN_PATH=/home/momota1029/rust/yulang/notes/theory/lean/.lake/build/lib/lean /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 /home/momota1029/rust/yulang/notes/theory/lean/YulangClosure/NativePermissionDecoderR118.lean -o /home/momota1029/rust/yulang/notes/theory/lean/.lake/build/lib/lean/YulangClosure/NativePermissionDecoderR118.olean -i /home/momota1029/rust/yulang/notes/theory/lean/.lake/build/lib/lean/YulangClosure/NativePermissionDecoderR118.ilean -c /home/momota1029/rust/yulang/notes/theory/lean/.lake/build/ir/YulangClosure/NativePermissionDecoderR118.c --setup /home/momota1029/rust/yulang/notes/theory/lean/.lake/build/ir/YulangClosure/NativePermissionDecoderR118.setup.json --json
error: YulangClosure/NativePermissionDecoderR118.lean:87:22: Application type mismatch: The argument
  found
has type
  views[endpoint.view]? = some (endpoint.view, allowed)
but is expected to have type
  some (endpoint.view, allowed) = some (endpoint.view, allowed)
in the application
  And.intro found
warning: YulangClosure/NativePermissionDecoderR118.lean:104:8: `simp` already closes the goal

Hint: Use `simp` instead of `simpa`:
  [apply] simp only [equal]

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: YulangClosure/NativePermissionDecoderR118.lean:90:0: automatically included section variable(s) unused in theorem `YulangClosure.NativePermissionDecoderR118.read_permission_exact`:
  [DecidableEq Id]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Id] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
error: YulangClosure/NativePermissionDecoderR118.lean:136:58: Unknown identifier `actualFamily`
error: YulangClosure/NativePermissionDecoderR118.lean:137:67: Unknown identifier `actualPermission`
error: YulangClosure/NativePermissionDecoderR118.lean:138:28: Unknown identifier `actualPermission.concrete`
error: YulangClosure/NativePermissionDecoderR118.lean:138:54: Unknown identifier `actualFamily`
info: YulangClosure/NativePermissionDecoderR118.lean:166:0: @YulangClosure.NativePermissionDecoderR118.contains_member : ∀ {Id : Type} [inst : DecidableEq Id] (xs : List Id)
  (family : Id), YulangClosure.NativePermissionDecoderR118.contains xs family = true → family ∈ xs
info: YulangClosure/NativePermissionDecoderR118.lean:167:0: 'YulangClosure.NativePermissionDecoderR118.contains_member' depends on axioms: [propext]
info: YulangClosure/NativePermissionDecoderR118.lean:168:0: @YulangClosure.NativePermissionDecoderR118.read_family_exact : ∀ {Id : Type} [DecidableEq Id]
  (views : List (Nat × List Id)) (endpoint : YulangClosure.NativePermissionDecoderR118.Endpoint) (family : Id),
  YulangClosure.NativePermissionDecoderR118.readFamily views endpoint = some family →
    ∃ allowed, views[endpoint.view]? = some (endpoint.view, allowed) ∧ allowed[endpoint.member]? = some family
info: YulangClosure/NativePermissionDecoderR118.lean:169:0: 'YulangClosure.NativePermissionDecoderR118.read_family_exact' depends on axioms: [propext, sorryAx]
info: YulangClosure/NativePermissionDecoderR118.lean:170:0: @YulangClosure.NativePermissionDecoderR118.read_permission_exact : ∀ {Id : Type} [DecidableEq Id]
  (permissions : List (Nat × YulangClosure.ComputationPermissionEntryR39.Permission Id)) (registration storage : Nat)
  (permission : YulangClosure.ComputationPermissionEntryR39.Permission Id),
  YulangClosure.NativePermissionDecoderR118.readPermission permissions registration storage = some permission →
    YulangClosure.NativePermissionDecoderR118.matching permissions registration = [(storage, permission)]
info: YulangClosure/NativePermissionDecoderR118.lean:171:0: 'YulangClosure.NativePermissionDecoderR118.read_permission_exact' depends on axioms: [propext]
info: YulangClosure/NativePermissionDecoderR118.lean:172:0: @YulangClosure.NativePermissionDecoderR118.decode_member : ∀ {Id State Batch : Type} [inst : DecidableEq Id]
  [inst_1 : DecidableEq State] [inst_2 : DecidableEq Batch]
  (permissionOwner viewOwner : YulangClosure.OwnedResidualProjectionR54.Owner State Batch)
  (views : List (Nat × List Id)) (permissions : List (Nat × YulangClosure.ComputationPermissionEntryR39.Permission Id))
  (endpoint : YulangClosure.NativePermissionDecoderR118.Endpoint) (registration storage : Nat) (family : Id)
  (permission : YulangClosure.ComputationPermissionEntryR39.Permission Id),
  YulangClosure.NativePermissionDecoderR118.decode permissionOwner viewOwner views permissions endpoint registration
        storage =
      some (family, permission) →
    permissionOwner = viewOwner ∧
      (∃ allowed, views[endpoint.view]? = some (endpoint.view, allowed) ∧ allowed[endpoint.member]? = some family) ∧
        YulangClosure.NativePermissionDecoderR118.matching permissions registration = [(storage, permission)] ∧
          family ∈ permission.concrete
info: YulangClosure/NativePermissionDecoderR118.lean:173:0: 'YulangClosure.NativePermissionDecoderR118.decode_member' depends on axioms: [propext, sorryAx, Quot.sound]
info: YulangClosure/NativePermissionDecoderR118.lean:174:0: YulangClosure.NativePermissionDecoderR118.unequal_coordinates : YulangClosure.NativePermissionDecoderR118.decode
      { state := 9, batch := 10 } { state := 9, batch := 10 } [(0, [99, 7])]
      [(0, YulangClosure.NativePermissionDecoderR118.examplePermission)] { view := 0, member := 1 } 1 0 =
    some (7, YulangClosure.NativePermissionDecoderR118.examplePermission) ∧
  1 ≠ 0 ∧ 1 ≠ 7
info: YulangClosure/NativePermissionDecoderR118.lean:175:0: 'YulangClosure.NativePermissionDecoderR118.unequal_coordinates' depends on axioms: [propext]
info: YulangClosure/NativePermissionDecoderR118.lean:176:0: YulangClosure.NativePermissionDecoderR118.post_state_is_not_prepare_input : YulangClosure.NativePermissionDecoderR118.decode
      { state := 9, batch := 10 } { state := 9, batch := 10 } [(0, [7])]
      [(0, YulangClosure.InternalPermissionIncidenceR45.witnessProbe.permission)] { view := 0, member := 0 } 0 0 =
    some (7, YulangClosure.InternalPermissionIncidenceR45.witnessProbe.permission) ∧
  YulangClosure.ComputationPermissionEntryR39.prepare YulangClosure.NativePermissionDecoderR118.postInputs
      YulangClosure.InternalPermissionIncidenceR45.witnessAction =
    none
info: YulangClosure/NativePermissionDecoderR118.lean:177:0: 'YulangClosure.NativePermissionDecoderR118.post_state_is_not_prepare_input' depends on axioms: [propext, Quot.sound]
Some required targets logged failures:
- YulangClosure.NativePermissionDecoderR118
error: build failed

[exit 1]
```

## Cache/artifact accounting

Before regular-file bytes: 28753843; after: 48734666; delta: 19980823. Initial du -sb (including directory metadata): 28,753,843 bytes. Combined build/audit elapsed: 16.740 seconds. No CPU/RSS measurement. Existing regular files changed: []; removed: []. New outputs (relative to notes/theory/lean/.lake; size bytes; SHA-256):

```text
build/ir/YulangClosure/AuthenticatedResidualConsumerR49.c 333561 72e39a9aadcc95636c5f65d5a5774a6a7d235b95712dbebcc3f7539de5cdf59b
build/ir/YulangClosure/AuthenticatedResidualConsumerR49.c.hash 16 67216a625f6e4a18bc466619c3c197a0ea3667e74f371ac65af512d68df4490a
build/ir/YulangClosure/AuthenticatedResidualConsumerR49.setup.json 861 7e4e42f657f698a471ad123d5e6cfb8ac15268c3cda91ee5e41d22c7093a0bda
build/ir/YulangClosure/ComputationPermissionEntryR39.c 170889 f13a644c07bed7b49b1a94448046cf07d07fb1af734b2e05c6760d26795b8fba
build/ir/YulangClosure/ComputationPermissionEntryR39.c.hash 16 8fcdd09e6e8e1c4577566cf43f69112802feb60a0952a2def2baf6e3bbf6395b
build/ir/YulangClosure/ComputationPermissionEntryR39.setup.json 171 4db1f0363b60fd31b01324123120f66297a76a1283860c3db86b74902f28839b
build/ir/YulangClosure/CurrentEmissionOwnershipR47.c 234170 129cf9200fd99ac7f01dae1ff9d4489f52693736831a6aaad38f1bd08b003f8a
build/ir/YulangClosure/CurrentEmissionOwnershipR47.c.hash 16 47f3fd9dabfbef6eb58d8ec31e243be0952d7ef7bf55e1557a0cb0faeb484987
build/ir/YulangClosure/CurrentEmissionOwnershipR47.setup.json 520 0a5b1e509f52e2789d7660006e4963c8c936308ec3f89b050e31ff258c3e2af5
build/ir/YulangClosure/InternalPermissionIncidenceR45.c 220310 76054cdd635cfd57bf89c4c166b609c546d869d57d185c01110a72316d74ad7e
build/ir/YulangClosure/InternalPermissionIncidenceR45.c.hash 16 0d17da230859e8c760f0b248fa8636f98870f9ae0adf2e04d600ce5cfbbe483a
build/ir/YulangClosure/InternalPermissionIncidenceR45.setup.json 345 5763766f043863ac119f8e6f2e79d4d71187a4a3ee19866fb3df5d8a8bde4b37
build/ir/YulangClosure/NativeFreshScopeTransport.c 10957 75c3e73a6ef73f2684187e9887444d19bd0df4f4215f49d7d4082a02489e5bd1
build/ir/YulangClosure/NativeFreshScopeTransport.c.hash 16 d5f32ebc2a4e8ef6b6dccf596a113bb56e841aa3c2d2af64e3374cfef75d061c
build/ir/YulangClosure/NativeFreshScopeTransport.setup.json 326 e4f661c46a1706b2fe1fb2e4ee03159f2fa8f172740955dbf6f14a97bc0e97c8
build/ir/YulangClosure/NativePermissionDecoderR118.setup.json 1898 f1510f257d788b45cae30008f1639e868a3b69641956a15d3429d69786f6923c
build/ir/YulangClosure/NativeResidualPublicationR51.c 293508 c1db48f797559f52e45e44e8767bbf14bdcf3f811a989bac4c42050348828a77
build/ir/YulangClosure/NativeResidualPublicationR51.c.hash 16 8d6ce0be03109f72f1f877f3c09c52b1292590d4063121b7a04f216d88f05e08
build/ir/YulangClosure/NativeResidualPublicationR51.setup.json 1039 a7612ce122096c96211bf14c5ca905bccbd0a37e07b5c770921a4b48d76f2be1
build/ir/YulangClosure/NativeScopeTransformer.c 134808 eb7c518ba2ecea96422c91737a197d173383922be7165b3d335960c315bf3143
build/ir/YulangClosure/NativeScopeTransformer.c.hash 16 26f04c1a5819b287833c5fa8bd85ead08a3ade41a228b87010a25b995561600a
build/ir/YulangClosure/NativeScopeTransformer.setup.json 164 7ef6cbcae65abf30877eb3cc234f86408a979820e01f88063c10604aacad7e4a
build/ir/YulangClosure/OwnedResidualProjectionR54.c 94987 a4d012e69fe26233f7b471d5ccc5e34bbcace98eed62fca61501e0e77f4cea19
build/ir/YulangClosure/OwnedResidualProjectionR54.c.hash 16 1390d3087886381f70472ffca8587276bdb1b20d01c7dd4fc435b1326749e2da
build/ir/YulangClosure/OwnedResidualProjectionR54.setup.json 1559 e7e1fa715e14d06c45c49fefc9ae8065e915b178ea9c47f3163303378fd6c8b2
build/ir/YulangClosure/PerCallResidualPublicationR52.c 80666 bb3e9a2005064949c6dc73eb10fb869386b5a0d86a9057bea81bd8db6f0ea4dd
build/ir/YulangClosure/PerCallResidualPublicationR52.c.hash 16 7c3c4b2558a0a1cd4a5e5603c04310f73cad488c4dc2e76ee2c220be1c8d1c27
build/ir/YulangClosure/PerCallResidualPublicationR52.setup.json 1214 038f751584b5ae66a572c37adff7418bf23149b968a82fd00e28bbbcc29e5957
build/ir/YulangClosure/ProviderEntryArrivalR48.c 95961 7f5cc9d0f6553cbb90f92929e643f2ab9c6cd9d731adbccd8dda8c3a12cdcc54
build/ir/YulangClosure/ProviderEntryArrivalR48.c.hash 16 074efa46d67dbd8a41928e3d96ada7e19dd7cdcf4474a2b1526941e83ac2afc6
build/ir/YulangClosure/ProviderEntryArrivalR48.setup.json 688 cc2f05c5b59624063902ab52a17396a61b4aa887a333a3b30d59adebf975cfac
build/ir/YulangClosure/SuppressionPermissionR116.c 12915 b092ecfe4c10a4e121d8a339d36f438b2c131497e134f74eac0ed74ac2b67cfd
build/ir/YulangClosure/SuppressionPermissionR116.c.hash 16 db64f4288e4cace5907d0925045abdab836fb40eb3653d755f9c4e1324c653c1
build/ir/YulangClosure/SuppressionPermissionR116.setup.json 1728 81b2c487aef06481258e08431d8e6f7a5bd534d0786bc916e87a0b507896e65a
build/ir/YulangClosure/WholePublicationResidualR53.c 114130 4a5223c03a88dc0537f370d413d328dfe424eb8ca20dc094338edb24dbe07417
build/ir/YulangClosure/WholePublicationResidualR53.c.hash 16 63ae7d98ddc97c892098f3d0c9f28c3bf929b734e0d4bbba5d7a3c2310df0258
build/ir/YulangClosure/WholePublicationResidualR53.setup.json 1388 c094083e94317947ea07a8ffc13533b88f66ce44724b32ab4304fd19fa39105a
build/lib/lean/YulangClosure/AuthenticatedResidualConsumerR49.ilean 207052 a9cb7745e40e19f8a9060c0d6e7701f003a8cc955e267f04e8d397efe9f9807c
build/lib/lean/YulangClosure/AuthenticatedResidualConsumerR49.ilean.hash 16 f9169040ee7ab4f43d0cc0d69242d39c4a81f969383ba84daa9022f56ede83ec
build/lib/lean/YulangClosure/AuthenticatedResidualConsumerR49.olean 2870232 2ec911490c13ce611284965c94e2cb30fc2313faea7b312aa14ba7044d6627db
build/lib/lean/YulangClosure/AuthenticatedResidualConsumerR49.olean.hash 16 7e658ad7fdebaeea065473e060158e47022ca3d698de6d86ad9deadc3a18f522
build/lib/lean/YulangClosure/AuthenticatedResidualConsumerR49.trace 2066 6a9729a8afbb6b53741a56a4a118e29ab7a1b7fd7aa67557bba2c530f552f0f1
build/lib/lean/YulangClosure/ComputationPermissionEntryR39.ilean 76843 502507a61772cdf746602e9a1ce245c8380632af3f4bea25f80a5113cdc8bf11
build/lib/lean/YulangClosure/ComputationPermissionEntryR39.ilean.hash 16 09ab00f1ed17ba1facb09c1a7db1d127456cee8a7c51544c8b2938034852cf90
build/lib/lean/YulangClosure/ComputationPermissionEntryR39.olean 1515320 e6efb347db05a8171236d03187cd5da601d81abe56fd1a30c3e9e8f7c9f97489
build/lib/lean/YulangClosure/ComputationPermissionEntryR39.olean.hash 16 eb457f73c027b48a0974aa18c35f7addbff87c790b680250135fdb23d3f20397
build/lib/lean/YulangClosure/ComputationPermissionEntryR39.trace 1870 9ee7b62a4dffbf06fccc63fecc45813815d088b94ca53ac7849555e6d16c4cd1
build/lib/lean/YulangClosure/CurrentEmissionOwnershipR47.ilean 91662 7807fbf61cf245c5483f9497c8a3c5bb4f524dc048e6154a2d5c9bb86c29dda3
build/lib/lean/YulangClosure/CurrentEmissionOwnershipR47.ilean.hash 16 c2689c0278a09089f7350260235a20dd0aacc0347b6de248e161d8b58f41ac43
build/lib/lean/YulangClosure/CurrentEmissionOwnershipR47.olean 1773488 e6a188912d9e8d361e0084b7dc90a0e4e11d8e1ad948a01db3c411a1dec6faa6
build/lib/lean/YulangClosure/CurrentEmissionOwnershipR47.olean.hash 16 fe75667955615310ff5643497825e80ba27b2cba669e9951746ce34203a61e9f
build/lib/lean/YulangClosure/CurrentEmissionOwnershipR47.trace 2045 172ca0d741d01aa7ea645d176406353292a3756f875779889455c6c351c3c6de
build/lib/lean/YulangClosure/InternalPermissionIncidenceR45.ilean 89068 256b7dee560135052dedb0dc56615806cec6e977f45b72a2c105645749eb7729
build/lib/lean/YulangClosure/InternalPermissionIncidenceR45.ilean.hash 16 4821f81358b87669cd134bd39c3d6fe5b2b0d182b38668e443d1ac788929a08a
build/lib/lean/YulangClosure/InternalPermissionIncidenceR45.olean 2487496 5da13590e510800915da32888c2490a7b9d5d1a80b9e4f266a777d65878f10c8
build/lib/lean/YulangClosure/InternalPermissionIncidenceR45.olean.hash 16 3da0f69268569c90bfd554196a2aee394e1f76f54c00dc8e1d9389a0a9c9028d
build/lib/lean/YulangClosure/InternalPermissionIncidenceR45.trace 2064 d7929e36b8b97c8edcd41bf5ba3e6cc742207038d7125beaaa608513dee846be
build/lib/lean/YulangClosure/NativeFreshScopeTransport.ilean 51677 fd8518653b4381401412cb1a64a922a11bb109b2fc5c997292270680ae858389
build/lib/lean/YulangClosure/NativeFreshScopeTransport.ilean.hash 16 779d7bc1fe05f12ef7ba70778e1d0ac5db302bad586ad733e97b7073f44c3d35
build/lib/lean/YulangClosure/NativeFreshScopeTransport.olean 339840 c3a00eaacb005568da260ec51dff2404e94313d09438572272e8a9bb29d8add7
build/lib/lean/YulangClosure/NativeFreshScopeTransport.olean.hash 16 bdf78c3a6a5af5a38f2a9fa76e3a13f24c9dfdaec9b6b730a451e45c3021a351
build/lib/lean/YulangClosure/NativeFreshScopeTransport.trace 2012 8224e7411d51b5215a34f06bc9ebcaa979061102f0c45bfe69a5bacd746969c0
build/lib/lean/YulangClosure/NativeResidualPublicationR51.ilean 179482 ae2558cd540a348bf8cc711a98fce093cae975fcbe9cb93c67e77078414e07ec
build/lib/lean/YulangClosure/NativeResidualPublicationR51.ilean.hash 16 eeaba847da2b02050a760a838b5deba8fe2c0f39f47ed79e81f53c948b035926
build/lib/lean/YulangClosure/NativeResidualPublicationR51.olean 2409264 ba3b93f84e5b5bca6de1c240cba1c5692241b36090797b0fd38559e06f2e4a35
build/lib/lean/YulangClosure/NativeResidualPublicationR51.olean.hash 16 169fd2f849ee3f226c5b095f7471e1960f2d90233e04b89e286a737c1965e4f0
build/lib/lean/YulangClosure/NativeResidualPublicationR51.trace 2056 6841f95d64bbb7fa23c3ba6913a601eb4a26a63d1810288e3c83a5224ca7fdd0
build/lib/lean/YulangClosure/NativeScopeTransformer.ilean 73360 1aa98835ada98fe87191acf927f820eb2dedd05801db71af17f512834ebfa1f6
build/lib/lean/YulangClosure/NativeScopeTransformer.ilean.hash 16 729d69194e39b8bba32c35b17353764c1c1b71e1c56cbfc3d03c41bc104cf810
build/lib/lean/YulangClosure/NativeScopeTransformer.olean 800784 9fa2726097f52da97213093624eea44d03cc43d6511152ae42201a189495c5bf
build/lib/lean/YulangClosure/NativeScopeTransformer.olean.hash 16 e412c765944eb31bd48671024e308ad54cd13d4e23543b15190ad8c1090094f6
build/lib/lean/YulangClosure/NativeScopeTransformer.trace 1818 061f1bf7c9c44829e1ae1fb51421e104465c076fe39b54f968f5d0312a43dea6
build/lib/lean/YulangClosure/OwnedResidualProjectionR54.ilean 95983 d5ee5bc87643c3d6f624585f08745a8d8f23f6d253f404312a11701c399bccb6
build/lib/lean/YulangClosure/OwnedResidualProjectionR54.ilean.hash 16 c5356b9dc874d8b2b7ec64a3f3631437879c27857090bcb6ecf4c7024ce66e35
build/lib/lean/YulangClosure/OwnedResidualProjectionR54.olean 906536 89cc437745c68776c837133227a5f08bf866633da1f66f7455d7fadf6964a42a
build/lib/lean/YulangClosure/OwnedResidualProjectionR54.olean.hash 16 ad2852907caac3b632a513bb57c60c66abd77247d338cbc00099bafd0f242cc0
build/lib/lean/YulangClosure/OwnedResidualProjectionR54.trace 2029 b0a44fee339b570f5f9c92a2bfe92acff5e5eacf3d3c55bbfdf949ef49b720f5
build/lib/lean/YulangClosure/PerCallResidualPublicationR52.ilean 126423 a4a2de15acaece64603ac6b5e7d4a253ba30dd2679b7d5340509bff8dd943d52
build/lib/lean/YulangClosure/PerCallResidualPublicationR52.ilean.hash 16 d58ae037743d2ebef1323540fce8f3ea7995b5ddd12e0e52075c18a631b64a6e
build/lib/lean/YulangClosure/PerCallResidualPublicationR52.olean 929864 640cc877c1266662ff47d13f9707e2bfed7b06d966750cecf7723a8d4e68e464
build/lib/lean/YulangClosure/PerCallResidualPublicationR52.olean.hash 16 f2734622e332680220b55e7dd18ca0de46d6209130b56fb2a3587ed3d477de4b
build/lib/lean/YulangClosure/PerCallResidualPublicationR52.trace 2055 30ff80b4d0709852e488c1e6044f631f710b285416d17db47e13d0512025435c
build/lib/lean/YulangClosure/ProviderEntryArrivalR48.ilean 63473 f7497e4c53d5956b8578929caa2fee7c7e4307065d9d86de42d67ee8cea9d173
build/lib/lean/YulangClosure/ProviderEntryArrivalR48.ilean.hash 16 108aaa0ea1e849ed092608cbe176a0c17a7a6c5d8a2a4837416c7bb498a18816
build/lib/lean/YulangClosure/ProviderEntryArrivalR48.olean 1064960 10563346e3630ac3470d31547e896192ccfbb47c99cd6c3b2d4f1ed7307052aa
build/lib/lean/YulangClosure/ProviderEntryArrivalR48.olean.hash 16 c8c0450211e80adeea34bb7e076db6fcdfcec0dcff36b0cd7c0a0f8929e44d67
build/lib/lean/YulangClosure/ProviderEntryArrivalR48.trace 2008 0132d4de88689616fb4b93a0b7dfe6c28df15a938f0c327e703d55debc3870a8
build/lib/lean/YulangClosure/SuppressionPermissionR116.ilean 37651 8edfb7c23f3bde5790417bbae674a75a2ce9fbba6d2020e5b0dbb7a90c5f946a
build/lib/lean/YulangClosure/SuppressionPermissionR116.ilean.hash 16 82c6a095a2888ff7ce8601d59421115b7c54c42aea12781486c3070355fea376
build/lib/lean/YulangClosure/SuppressionPermissionR116.olean 368056 c31c0274523ac3068cf6d1bb87c767560b0b5e31d7f6566267f2833574238c15
build/lib/lean/YulangClosure/SuppressionPermissionR116.olean.hash 16 53f448e644e804e9e80d8179ebc13253c250b105fcedd59aed57fa4d0ecab105
build/lib/lean/YulangClosure/SuppressionPermissionR116.trace 14870 acc9a397a33da80f194a6887d809b4839a697b92d7f90a6ac8babb0808394f7b
build/lib/lean/YulangClosure/WholePublicationResidualR53.ilean 136282 a0617b8b7e0b4031289714fd6c582b46e81cf593cd57b8ad7895ca8c9b0f0195
build/lib/lean/YulangClosure/WholePublicationResidualR53.ilean.hash 16 6b1069c4f17f0c725064c10b992156865c377369d41046c8b8062c28a749ce8c
build/lib/lean/YulangClosure/WholePublicationResidualR53.olean 1439752 a704c5771e8edcf4d68689f4b696bfddafc389fa67d4e799705358e0963ddc74
build/lib/lean/YulangClosure/WholePublicationResidualR53.olean.hash 16 db45851466f0b2734afc3f58ed4e51131ec02ef9e94f2e9afcd537b8b66757d0
build/lib/lean/YulangClosure/WholePublicationResidualR53.trace 2043 af7603f65417b6574b1c7b261a05eb8859770feec190d649c4ed253158204009
```

Final combined execution exit: 1.

## Five available declaration audits

Input is shown verbatim; no source/module file was created.

```lean
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.NativeScopeTransformer
import YulangClosure.NativeFreshScopeTransport
import YulangClosure.SuppressionPermissionR116
set_option pp.fullNames true
set_option pp.universes false
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.NativeScopeTransformer.evaluate_rename with
  | some (.thmInfo _) => pure ()
  | _ => throwError "not a theorem: YulangClosure.NativeScopeTransformer.evaluate_rename"
#check @YulangClosure.NativeScopeTransformer.evaluate_rename
#print axioms YulangClosure.NativeScopeTransformer.evaluate_rename
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.NativeScopeTransformer.evaluate_rename
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.NativeFreshScopeTransport.fresh_evaluate with
  | some (.thmInfo _) => pure ()
  | _ => throwError "not a theorem: YulangClosure.NativeFreshScopeTransport.fresh_evaluate"
#check @YulangClosure.NativeFreshScopeTransport.fresh_evaluate
#print axioms YulangClosure.NativeFreshScopeTransport.fresh_evaluate
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.NativeFreshScopeTransport.fresh_evaluate
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.NativeFreshScopeTransport.fresh_evaluate_and_reuse with
  | some (.thmInfo _) => pure ()
  | _ => throwError "not a theorem: YulangClosure.NativeFreshScopeTransport.fresh_evaluate_and_reuse"
#check @YulangClosure.NativeFreshScopeTransport.fresh_evaluate_and_reuse
#print axioms YulangClosure.NativeFreshScopeTransport.fresh_evaluate_and_reuse
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.NativeFreshScopeTransport.fresh_evaluate_and_reuse
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.SuppressionPermissionR116.selected_endpoint_member with
  | some (.thmInfo _) => pure ()
  | _ => throwError "not a theorem: YulangClosure.SuppressionPermissionR116.selected_endpoint_member"
#check @YulangClosure.SuppressionPermissionR116.selected_endpoint_member
#print axioms YulangClosure.SuppressionPermissionR116.selected_endpoint_member
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.SuppressionPermissionR116.selected_endpoint_member
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.SuppressionPermissionR116.internal_certificate_member with
  | some (.thmInfo _) => pure ()
  | _ => throwError "not a theorem: YulangClosure.SuppressionPermissionR116.internal_certificate_member"
#check @YulangClosure.SuppressionPermissionR116.internal_certificate_member
#print axioms YulangClosure.SuppressionPermissionR116.internal_certificate_member
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.SuppressionPermissionR116.internal_certificate_member
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
```

```text
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache env lean -j1 -M1024 --stdin
YulangClosure.NativeScopeTransformer.evaluate_rename : ∀
  (transformer : YulangClosure.NativeScopeTransformer.Transformer)
  (initial : YulangClosure.NativeScopeTransformer.State) (scopes tags : Nat → Nat),
  Function.Injective scopes →
    Function.Injective tags →
      YulangClosure.NativeScopeTransformer.Equivalent
        ((transformer.rename scopes tags).evaluate (initial.rename scopes tags))
        ((transformer.evaluate initial).rename scopes tags)
'YulangClosure.NativeScopeTransformer.evaluate_rename' depends on axioms: [propext, Quot.sound]
YulangClosure.NativeFreshScopeTransport.fresh_evaluate : ∀ (scopeCount tagCount : Nat) (scopeKeys tagKeys : List Nat)
  (transformer : YulangClosure.NativeScopeTransformer.Transformer) (state : YulangClosure.NativeScopeTransformer.State),
  YulangClosure.NativeFreshScopeTransport.TransformerValid scopeCount tagCount transformer →
    YulangClosure.NativeFreshScopeTransport.StateValid scopeCount tagCount state →
      have scopes := (YulangClosure.NativeFreshScopeTransport.fresh scopeCount scopeKeys).remap;
      have tags := (YulangClosure.NativeFreshScopeTransport.fresh tagCount tagKeys).remap;
      YulangClosure.NativeScopeTransformer.Equivalent
        ((transformer.rename scopes tags).evaluate (state.rename scopes tags))
        ((transformer.evaluate state).rename scopes tags)
'YulangClosure.NativeFreshScopeTransport.fresh_evaluate' depends on axioms: [propext, Quot.sound]
YulangClosure.NativeFreshScopeTransport.fresh_evaluate_and_reuse : ∀ (scopeCount tagCount : Nat)
  (scopeKeys tagKeys : List Nat) (transformer : YulangClosure.NativeScopeTransformer.Transformer)
  (state : YulangClosure.NativeScopeTransformer.State),
  YulangClosure.NativeFreshScopeTransport.TransformerValid scopeCount tagCount transformer →
    YulangClosure.NativeFreshScopeTransport.StateValid scopeCount tagCount state →
      have scopes := (YulangClosure.NativeFreshScopeTransport.fresh scopeCount scopeKeys).remap;
      have tags := (YulangClosure.NativeFreshScopeTransport.fresh tagCount tagKeys).remap;
      have renamedTransformer := transformer.rename scopes tags;
      have renamedState := state.rename scopes tags;
      YulangClosure.NativeScopeTransformer.Equivalent (renamedTransformer.evaluate renamedState)
          ((transformer.evaluate state).rename scopes tags) ∧
        YulangClosure.NativeFreshScopeTransport.TransformerValid (scopeCount + scopeKeys.length)
            (tagCount + tagKeys.length) renamedTransformer ∧
          YulangClosure.NativeFreshScopeTransport.StateValid (scopeCount + scopeKeys.length) (tagCount + tagKeys.length)
            (renamedTransformer.evaluate renamedState)
'YulangClosure.NativeFreshScopeTransport.fresh_evaluate_and_reuse' depends on axioms: [propext, Quot.sound]
@YulangClosure.SuppressionPermissionR116.selected_endpoint_member : ∀ {Id : Type} [inst : DecidableEq Id]
  (e : YulangClosure.ComputationPermissionEntryR39.Inputs Id)
  (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port endpoint : Id)
  (p : YulangClosure.ComputationPermissionEntryR39.Permission Id)
  (provider arm : YulangClosure.SuppressionPermissionR116.Operation Id),
  YulangClosure.ComputationPermissionEntryR39.prepare e a = Option.some (f, r, port) →
    YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port = Option.some p →
      YulangClosure.SuppressionPermissionR116.SelectedSource a r arm →
        YulangClosure.SuppressionPermissionR116.operationMatch provider arm = Bool.true →
          endpoint = provider.family → endpoint ∈ p.concrete
'YulangClosure.SuppressionPermissionR116.selected_endpoint_member' depends on axioms: [propext, Quot.sound]
@YulangClosure.SuppressionPermissionR116.internal_certificate_member : ∀ {Id : Type} [inst : DecidableEq Id]
  {Artifact Term Fact : Type} [inst_1 : DecidableEq Artifact] [inst_2 : DecidableEq Term] [inst_3 : DecidableEq Fact]
  (e : YulangClosure.InternalPermissionIncidenceR45.Inputs Artifact Id Term Fact)
  (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id)
  (q : YulangClosure.InternalPermissionIncidenceR45.Query Artifact Id)
  (probe : YulangClosure.InternalPermissionIncidenceR45.Probe Artifact Id Term Fact)
  (out : YulangClosure.InternalPermissionIncidenceR45.Certificate Artifact Id Term Fact)
  (provider arm : YulangClosure.SuppressionPermissionR116.Operation Id),
  YulangClosure.ComputationPermissionEntryR39.prepare e.source a = Option.some (f, r, port) →
    YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port = Option.some probe.permission →
      YulangClosure.InternalPermissionIncidenceR45.extract e q probe = Option.some out →
        YulangClosure.SuppressionPermissionR116.SelectedSource a r arm →
          YulangClosure.SuppressionPermissionR116.operationMatch provider arm = Bool.true →
            out.permission.registration = a.registration ∧
              out.permission.occurrence = a.occurrence ∧
                out.permission.owner = f.owner ∧ provider.family ∈ out.permission.concrete
'YulangClosure.SuppressionPermissionR116.internal_certificate_member' depends on axioms: [propext, Quot.sound]
[exit 0]
```

Elapsed 1.881 seconds.

## Sixth declaration unavailable

```lean
import YulangClosure.PermissionMemberWitnessR119
#check @YulangClosure.PermissionMemberWitnessR119.selected_retained_member
#print axioms YulangClosure.PermissionMemberWitnessR119.selected_retained_member
```

```text
<stdin>:1:0: error: object file '/home/momota1029/rust/yulang/notes/theory/lean/.lake/build/lib/lean/YulangClosure/PermissionMemberWitnessR119.olean' of module YulangClosure.PermissionMemberWitnessR119 does not exist
[exit 1]
```

No actual type or axiom list was produced for R119.selected_retained_member. Its source signature is conditional, but this build failure prevents checker acceptance; the R118 diagnostic sorryAx is failure elaboration evidence, not a delivered accepted theorem.

## Governing source, corrected scope and parent application

At source baseline `3560df97dab02744da10e897c73c1cf94118f4ee`, the original manuscript claim is `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §1 (original scope and one joint witness), §3 (what Simple-sub supplies), §5 (source completeness bridge). It quantifies over every supported original source program, lawful finite construction history and actual retained extrusion occurrence; preserves typing, principal coverage, ordinary progress/termination, original scopes, recursive sharing, complete Call, effect hygiene and correlated evidence. Its native lift does not establish the source-admissible joint strategy through publication/use. The current correction `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6 uses the immutable birth-level induced Value graph, retaining actual origins/receivers/pairs and all accumulated constraints; old cross-level SCC applications are superseded. The source map and research manuscripts are locators/evidence, not fresh semantic approval. The external Simple-sub PDF/Scala sources were not needed or inspected for this finite algebra audit, and no theorem from them is claimed proved here.

Authoritative `2026-10-10-annotation-effect-hygiene-integration.md` §§1,1.1,1.2 separates concrete contravariant permission, actual inflow and residual: `[signal, write]` remains an accepted input to the selected `[signal]` formal, Catch removes signal only, unknown variables/connections remain, and write remains outward. `2026-10-15-compose-scoped-effect-release.md`, Scope of the operation and remaining work, requires releasing the original e protection at corresponding output-f occurrences, including f=id, while preserving contribution attribution and every independent protection. Release itself does not grant capture. This audit changes none of these policies or source cases.

The exact parent definition at `YulangClosure.SourceProblem.InferenceSoundness` (`Contracts.lean:128`) is:

```lean
def InferenceSoundness : Prop :=
  ∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
    ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

`SourceScopedCoverage` additionally preserves the same original `s x e` when constructing a solution; `PrincipalCoverage` retains the original instance ordering. These are proposition definitions, not concrete instances/proofs. `LocalLaws` (`Contracts.lean:53`) takes initial typing, preservation, simulation, observation, no_bad and progress as supplied obligations; no such parameters are discharged by the five finite lemmas. The first remaining application premise here is an authenticated source-owned incoming contribution state and an actual protection-sensitive effect/Catch consumer. Owner: Luna's source/implementation lane, followed by an explicitly leased formal correspondence packet; no production promotion follows.

## Complete premise/conclusion map against admitted R147 evidence

The four admitted R147 artifacts are authenticated at task baseline `b75eaf06bc51ed583650de5bad2e57cb400ba78d`. Their review accepts bounded source-boundary evidence only. This audit also independently hash-authenticated and inspected pinned `candidate_context.rs:305–310,3280–3284,4219–4238`, `candidate_scheme.rs:4773–4796`, `candidate_effect.rs:1478–1505`, and `candidate_scope.rs:37–40,180–209`. The concurrently running R148 source author's early hints came through the primary; they guided these independent baseline windows and were not substituted for source evidence. The unfrozen R148 source artifact was not read.

1. **evaluate_rename.** All inputs are arbitrary Lean transformers/states and maps on Nat. It requires *global* injectivity separately for scopes and tags; concludes extensional membership equivalence of renamed evaluation with evaluation then rename. `Equivalent` compares both input and protection membership, not list order/duplicates. Rust `ScopeState` has inputs/protections; successful canonical `ScopeTransformer.evaluate` uses missing initial input tags, keep_initial and inherited protection. Its sorted/deduplicated vectors and fallible loops are not thereby identified with Lean lists. Actual FreshUse overwrite-or-identity maps are not globally injective on all Nat, so they cannot simply instantiate this older theorem. No source witness, attribution, Rust allocator semantics or consumer decision is concluded.

2. **fresh_evaluate.** Arbitrary counts/key lists plus a transformer and the *entire* incoming state are quantified. `TransformerValid` bounds every stamp, scope entry key and guard under the same old inventory counts. `StateValid` bounds every incoming input tag and protection scope, including inherited/external coordinates. The theorem derives commutation for the candidate `fresh` overwrite map without a supplied global injection. R147 locates native append allocation and one FreshUse remap for transformer plus demand at scheme:4773–4796. It does not supply an authentic incoming state or its bounds/rename at the reached decision. Identity fallback or demand is not that state. A formal refinement of native fresh to Lean `fresh` and success/canonicality is also unproved here.

3. **fresh_evaluate_and_reuse.** Exactly the same quantified objects and two validity premises; concludes commutation, renamed-transformer validity, and evaluated renamed-state validity at counts increased by key-list lengths. This supports subsequent copies *of the represented valid Lean objects*. It does not establish a Rust source execution history, compatible source scopes, original shared witness or complete constructor/replay coverage. R147 has no full carried state for these postconditions to describe.

4. **selected_endpoint_member.** `Id : Type` and `DecidableEq Id` remain universal; `e,a,f,r,port,endpoint,p,provider,arm` are supplied values. Premises: R39 `prepare e a = some(f,r,port)` at the PRE-constructor snapshot; `permissionFor a f r port = some p`; `SelectedSource a r arm` (same annotation row plus singleton concrete arm family); exact `operationMatch` (identity, declaration and family, not spelling); and endpoint=provider.family. Conclusion: that endpoint belongs to that same retained permission's concrete vector. `prepare` requires registered formal/row/entry, computation role, owner/scope/source-lambda/recipe identities, unoccupied recipe domain, no previous retained registration, and at most one row variable. `permissionFor` retains nonempty concrete vectors. These are equations requiring source authentication, not facts obtained by naming a Permission. R147's ordinary `allowed.contains(effect)` at effect:1489 is not an authenticated R39 preparation, selected permission/operation identity, scope release, or successful suppression. It does not establish these premises.

5. **internal_certificate_member.** In addition to generic Artifact/Term/Fact equality and R39 preparation, the retained permission is specifically `probe.permission`; `extract e q probe = some out` requires R45 `OwnerReads` and `Identity` on the same records. These check unique registration-owned construction/permission/receipt, use plan, route/lambda facts, function child/entry, recipe/components, artifact/use/source and target owners, original root identity, internal receipt/fact, typed positions, nonempty concrete permission and component equalities. SelectedSource and operationMatch are still explicit. Conclusion: output permission registration/occurrence/formal owner equal their original action/formal coordinates and provider.family is in that exact output permission. Relation/bound evidence in R147 is metadata and does not authenticate this R45 inventory/extraction; no Rust owner/readback bridge was proved. This theorem preserves a shared *supplied Lean permission*, not an automatically authenticated Rust pointer.

6. **selected_retained_member (source-inspected only).** The source signature below assumes R118 native-family read from a view/member endpoint, registration-keyed retained permission read at a distinct packed storage slot, an ordered first search of that exact permission's concrete vector, and a same-record/same-index consumer read. Its proposed conclusion retains the exact native indexed read, unique matching registration record, consumed=provider family and membership. The vector preserves duplicates and ordered positions; registration, packed storage, permission-member index and native-member index remain distinct. This does not establish R39 PRE-constructor facts, R45 extraction, Rust stable storage/owner or protection state. R118's actual compilation errors block this audit before an accepted R119 declaration is available.

```lean
-- namespace YulangClosure.PermissionMemberWitnessR119; {Id : Type} [DecidableEq Id]
theorem selected_retained_member
    (views : List (Nat × List Id)) (permissions : List (Nat × Permission Id))
    (endpoint : NativePermissionDecoderR118.Endpoint)
    (registration storage permissionMember : Nat)
    (permission : Permission Id) (providerFamily consumedFamily : Id)
    (nativeRead : NativePermissionDecoderR118.readFamily views endpoint = some providerFamily)
    (retainedRead : NativePermissionDecoderR118.readPermission permissions registration storage =
      some permission)
    (searched : orderedSearch permission.concrete providerFamily = some permissionMember)
    (consumerRead : permission.concrete[permissionMember]? = some consumedFamily) :
    (∃ allowed, views[endpoint.view]? = some (endpoint.view, allowed) ∧
      allowed[endpoint.member]? = some providerFamily) ∧
    NativePermissionDecoderR118.matching permissions registration = [(storage, permission)] ∧
    consumedFamily = providerFamily ∧ providerFamily ∈ permission.concrete
```

## First remaining goal and exact handoff

Apply the checked transport laws only after establishing a single decoding relation for the actual source-owned contribution and incoming inputs/protections, inventory validity for all of it, the *same successful FreshUse scope/tag maps* on state and transformer, and a reached consumer whose eligibility/subtraction result reads evaluated protection membership while retaining source contribution attribution. R147's `RelationKey`/processing/bound provenance and remapped demand retain useful identities; none supplies the missing state/consumer law. `evaluate_observation` explicitly uses empty slices, and actual `candidate_check_effect_operand` compares family/allowance or forwards the tail. No authenticated reachable hygiene counterexample is established by this omission.

`R148-PROOF-CHECK-01`: primary may admit an exact R118 repair packet for `read_family_exact:87` (case split has already reduced the first conjunct, while `found` still has the original lookup equality) and `decode_member:136–138` (names no longer available after `cases sf; cases sp`). This is an observed repair lead, not a checked repair or lease to edit. Then rebuild the R118/R119 cone and audit `YulangClosure.PermissionMemberWitnessR119.selected_retained_member`; preserve current failed evidence. Responsible owner: Luna assigns a future Lean leaf. No source edits are authorized in R148.

## Input authentication and direct dependencies

Every local project dependency below was compared byte-for-byte with its pinned source Git blob before use by the build, using read-only `git show`. Native source windows likewise used pinned blobs only; dirty working-tree Rust was not inspected. Build targets read the hash-identical working Lean tree. Governing files were SHA-256-read before semantic inspection. Some large combined instruction/source command outputs were truncated; exact proof interfaces, policies and original parent windows were then reread in focused commands. This is not a claim of full semantic audit of the dependency cone.

```text
4a6c910e12adb8f5ccc07b0921f2cc781ea7044994f99425d3c54c4e75837d3c AGENTS.md
99ae7bbda0a8907a48f762420d996e145e9870ad9794ea0dc608770131182882 AGENTS.pre-sprint.md
f2e01e3c33dc13d6c5cb77a66e7c5f0de15f08669f5a47fef0d6cb5c914da3a5 rules/goal-driven-sprints.md
e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1 rules/design-authority.md
05346b8c6e3d9cdd1715da1774bb26cf7bce313233782240b3493bd9ee8754a7 .agents/skills/yulang-lean-proofs/SKILL.md
cb3f1009e80f0f9f7a1bf2575b4144e002a72f21e474c66b441e1f626a1e4d4a .agents/skills/yulang-lean-proofs/references/sources.md
a1d8c47550e8925220623e0401410556d92719aff5590c459ac4c2e88306800b .agents/skills/yulang-lean-proofs/references/execution.md
a4f10b70297cbf4d8b5bc0c7526bc29783eaf417f1f70e53eeea341d1150dde6 .agents/skills/yulang-lean-proofs/scripts/check_lean.py
6f44b8ab2fbf664a7acf6dc77940bc5ca7e7245495ff1fb215907659c470fc0a tasks/agent-loop/sprints/effect-permission-witness-carrier-r148.md
24978efc978f41eb8400a900dd89d6b8e3312ae6c161374a6a4343c02a88fb2e tasks/agent-loop/history/effect-permission-witness-carrier-20261102-r148-admission.md
4fc4380f3ad1827ecf155f982e5186b32d6d66d91909039fb118063d8f1e2df2 notes/theory/lean/YulangClosure/AuthenticatedResidualConsumerR49.lean @ 3560df97dab02744da10e897c73c1cf94118f4ee
748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean @ 3560df97dab02744da10e897c73c1cf94118f4ee
2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e notes/theory/lean/YulangClosure/Contracts.lean @ 3560df97dab02744da10e897c73c1cf94118f4ee
d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c notes/theory/lean/YulangClosure/CurrentEmissionOwnershipR47.lean @ 3560df97dab02744da10e897c73c1cf94118f4ee
9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f notes/theory/lean/YulangClosure/InternalPermissionIncidenceR45.lean @ 3560df97dab02744da10e897c73c1cf94118f4ee
1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5 notes/theory/lean/YulangClosure/NativeFreshScopeTransport.lean @ 3560df97dab02744da10e897c73c1cf94118f4ee
2ebb7797c683b2bbf51d746f89d58d9abc4be66b5520fe6c0f4c6007a70d82ab notes/theory/lean/YulangClosure/NativePermissionDecoderR118.lean @ 3560df97dab02744da10e897c73c1cf94118f4ee
78a729b25e95812ba292c4e625ec69e46ff5eb70ff3ac2ae5b85dd1b33214d61 notes/theory/lean/YulangClosure/NativeResidualPublicationR51.lean @ 3560df97dab02744da10e897c73c1cf94118f4ee
68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6 notes/theory/lean/YulangClosure/NativeScopeTransformer.lean @ 3560df97dab02744da10e897c73c1cf94118f4ee
cc5d0b01485560e5091ce454b066ca2fc41eb350eee24ae525133a13bed401c9 notes/theory/lean/YulangClosure/OwnedResidualProjectionR54.lean @ 3560df97dab02744da10e897c73c1cf94118f4ee
d0ffaad36139148c3898d70c9da2e03d1b0e17cbb8b71841f751a8720570e73e notes/theory/lean/YulangClosure/PerCallResidualPublicationR52.lean @ 3560df97dab02744da10e897c73c1cf94118f4ee
f0d3d9c51a270b19f24acaf6edecec0885dda1fd1b2718db88dd4105db6a343f notes/theory/lean/YulangClosure/PermissionMemberWitnessR119.lean @ 3560df97dab02744da10e897c73c1cf94118f4ee
b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575 notes/theory/lean/YulangClosure/ProviderEntryArrivalR48.lean @ 3560df97dab02744da10e897c73c1cf94118f4ee
2aed350468964d90d8d83714177fff77d477e3df0846ae23150194bd76270e3a notes/theory/lean/YulangClosure/SuppressionPermissionR116.lean @ 3560df97dab02744da10e897c73c1cf94118f4ee
dc9c89e562f905c2c6284fd15eb82e9482a82bc9b2881f567c3454198318f391 notes/theory/lean/YulangClosure/WholePublicationResidualR53.lean @ 3560df97dab02744da10e897c73c1cf94118f4ee
ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c notes/theory/lean/lean-toolchain @ 3560df97dab02744da10e897c73c1cf94118f4ee
212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4 notes/theory/lean/lakefile.toml @ 3560df97dab02744da10e897c73c1cf94118f4ee
058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3 notes/theory/lean/lake-manifest.json @ 3560df97dab02744da10e897c73c1cf94118f4ee
8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3 notes/theory/lean/README.md @ 3560df97dab02744da10e897c73c1cf94118f4ee
3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271 notes/theory/2026-10-13-intrusion-source-preservation-proof.md @ 3560df97dab02744da10e897c73c1cf94118f4ee
ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae notes/design/2026-10-24-birth-level-scc-intrusion.md @ 3560df97dab02744da10e897c73c1cf94118f4ee
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81 notes/design/2026-10-11-yulang-inference-top-level-principles.md @ 3560df97dab02744da10e897c73c1cf94118f4ee
a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18 notes/design/2026-10-10-annotation-effect-hygiene-integration.md @ 3560df97dab02744da10e897c73c1cf94118f4ee
fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679 notes/design/2026-10-15-compose-scoped-effect-release.md @ 3560df97dab02744da10e897c73c1cf94118f4ee
a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905 crates/yu-solver/src/candidate_context.rs @ 3560df97dab02744da10e897c73c1cf94118f4ee
e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814 crates/yu-solver/src/candidate_scheme.rs @ 3560df97dab02744da10e897c73c1cf94118f4ee
102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01 crates/yu-solver/src/candidate_effect.rs @ 3560df97dab02744da10e897c73c1cf94118f4ee
4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03 crates/yu-solver/src/candidate_scope.rs @ 3560df97dab02744da10e897c73c1cf94118f4ee
d4f20f0f47d64b35416053c1f3be86daba197113b60acfb17ebf2cde9a3793ef tasks/agent-loop/inbox/effect-permission-real-consumer-r147-source.md @ b75eaf06bc51ed583650de5bad2e57cb400ba78d
f12a4cdbfe27bccb5a9a617ad40f775e7896b7c8b644f440a4b8c43f0de6a010 tasks/agent-loop/inbox/effect-permission-real-consumer-r147-proof.md @ b75eaf06bc51ed583650de5bad2e57cb400ba78d
b9bcd8bf2bebca4b063bcef24e8b9094eb40c525db0cbe48930631aab47316ed tasks/agent-loop/history/effect-permission-real-consumer-20261102-r147-review.md @ b75eaf06bc51ed583650de5bad2e57cb400ba78d
e72267fe9da32b8a1408ce85a25056cfcc7888bc7045fd9fecc9555c56003595 tasks/agent-loop/history/effect-permission-real-consumer-20261102-r147-outcome.md @ b75eaf06bc51ed583650de5bad2e57cb400ba78d
8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1 /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake
bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38 /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
81655926012444f214099f1ed6610ed63ade63f9e91b2e5af6689acd9cf1b400 /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean/Std.olean
faac24ec1517d3f518c256955c4c955ed11ac4e559b0128acbab3e2bacf26d00 /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean/Lean/Elab/Command.olean
dd9af656e6d42c262715c601abdf9200f750bedb81e0e099e21e4f851ae7596e /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean/Lean/Util/CollectAxioms.olean
```

Initial current-state metadata hash was `ad4ea562584fd9c9d623cf1397dd7e1cf6188d75dedb7afa95398d11da446876`; task protocol README was `0f829876325565f3c42fbf1950d01deef8c6fda4e92989f668ce1adada41efd6`. Their active-sprint/ownership metadata was read only, not semantic authority. No historical RUNNING row was treated as runtime evidence.

Supplemental source search across all fourteen modules for `sorry`, `admit`, `axiom`, `skipKernelTC`, `native_decide` and `ofReduceBool` found only prose/comment mentions in R54/R116/R118/R119, no source holes or project axioms/bypasses. This does not override actual R118 failed elaboration or replace transitive printed axiom audits.

## Represented and omitted cases; stop receipt

Represented mathematics: finite ordered lists, total Nat renamings, extensional input/protection membership, all old state/transformer supports under explicit bounds, repeated fresh keys, selected singleton concrete permission and the same certificate payload. Scope algebra is generic over input/protection names; generic permission identity types retain all supplied coordinates.

Not established: original whole-language inference, concrete source instance or full LocalLaws; native fallible evaluator/allocator refinement; complete Function/record/optional-record/method-selection/Call constructors; handler/continuation operational cases; source coverage, same joint witness through generation/publication/use; Rust snapshot/pointer/owner authentication, rollback/replay of incoming protection state; scoped subtraction at reached Catch/effect consumers; principality/progress/termination or production readiness. These remain required parent cases; none is removed from the accepted language.

Material failed attempts are preserved: guessed nonexistent R147 path caused a hash command exit 1 before its chained read; an initial root-relative cache path from project cwd caused `du` exit 1; the prebuild four-import stdin audit failed missing NativeScopeTransformer.olean; finite build failed R118 as logged; the separate R119 stdin audit failed missing its .olean. No repair/source edit was attempted. Version/help, input/hash and five-declaration stdin audit commands succeeded; diagnostic source-search commands are read-only evidence.

Only this handoff and the existing `.lake` generated outputs listed above were written. No temporary/scratch Lean module, new cache directory/environment, dependency/toolchain/config edit, Rust/Cargo/test run, Git mutation, descendant, user/third-party contact or independent-review appointment occurred. Existing cache regular files were preserved byte-for-byte; new outputs remain for the verification owner. This is the author's technical receipt, not self-certification or independent review.

Budget: maximum 600 seconds for the leaf; 480 seconds maximum checker envelope, stricter 420-second build-loop cap, actual finite build 16.740 seconds plus the separately recorded short stdin audits. Exact total CPU/RSS and complete leaf elapsed were not instrumented. All operations finished within the finite leaf cap. Remaining obligations are OPEN and return to Luna; no further in-envelope source or cache writes are needed.

**Worker STOPPED; all handoff/cache writes STOPPED after this revision. No outstanding subprocesses or descendant leases.**

Frozen UTC: 2026-11-01T03:10:35.387541+00:00.
