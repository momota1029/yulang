# R149 decoder proof repair — frozen handoff

Revision 1. Assignment R149-LEAN; author `/root/r149_lean_repair`; requested role `lean_prover`; effective model/effort UNKNOWN. No descendants. Outcome: conditional finite mathematics, kernel accepted; independent review and source/native application pending.

## Authentication and exact lease

Baseline `87dfe33bcd4c572d740dc33b454114b6018a4376`.
Corrected sprint contract SHA-256 `3ef1dfd0acd0720b8256d16d81dcd6233c72466a7a5f5116e68083e8a9ddfd36`; final admission SHA-256 `c8080af78bb1a4df698c7e13df11dbf1b59160a752db2a0face60496032d114a`. Both reauthenticated after primary correction. The initial contract candidate_scheme hash had `be86` where the baseline has `be60`; the primary corrected that typo before proof construction. All ten contract source blobs were hashed from baseline via read-only git show; the nine others matched initially. No Rust source contents were inspected.

R118 original SHA `2ebb7797c683b2bbf51d746f89d58d9abc4be66b5520fe6c0f4c6007a70d82ab`, repaired SHA `f976e0b3b5e8b2b70ee902bdca30ce140db503a4972e8cf1b621892b57bf5d27`.
R119 unchanged SHA `f0d3d9c51a270b19f24acaf6edecec0885dda1fd1b2718db88dd4105db6a343f`.
All other direct/transitive local Lean source dependencies equal baseline; hashes below.

Exact authored paths: `notes/theory/lean/YulangClosure/NativePermissionDecoderR118.lean` and this handoff. Generated outputs use the primary-authorized existing `notes/theory/lean/.lake`; sole verification ownership announced to primary before freeze. No environment/worktree/checkout/scratch, new dependencies, compiler code, tests, config, toolchain, manifest, lockfile, shared status, root import, questions, Git mutation or other worker file was written.

R148 source/proof handoffs were authenticated against its frozen independent review: source `07dde6759d846608d11451d6ffaf3f6c1627978b1b0e7dd49fe48e6078e5e51d`, proof `f8e900ff3e82fb821fb4cc9f7a35a576c5907e47e741d1007e38527642f824a2`. Those inbox artifacts intentionally are not present in the baseline commit; an initial git show lookup failed exit 128, and was replaced by frozen-hash authentication. R148 outcome/review are baseline-identical, SHA `3fdfdf2eff967da81664f17598371cce7ea9169b1da3fb950f9a033320bdde3e` / `19329c147c12678ad37aad5158e9ca25f64ba9db5132a6b5eea0a1d1df0f499f`. R147 source/proof frozen hashes matched `d4f20f0f47d64b35416053c1f3be86daba197113b60acfb17ebf2cde9a3793ef` / `f12a4cdbfe27bccb5a9a617ad40f775e7896b7c8b644f440a4b8c43f0de6a010`.

## Original sources, quantifiers and parent application

Original A/B locator: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5; current qualification correction `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–4. For every supported original source program, lawful finite history and actual retained extrusion occurrence, preserve original source typing, required principal coverage, soundness/progress/termination, original scopes, generalization, recursive sharing, complete Call and correlated evidence. One joint witness remains shared at its original scope. The original Simple-sub paper is only indirectly located by that manuscript; its paper proofs were not revalidated in this mechanical repair.

Whole-parent locator `docs/yulang-whole-proof-closure-ja.md` §1: original complete constructor/declaration/name/type/effect/profile/evidence/generalization/use/Call/protection/release/continuation scope. This research integration manuscript is a target map, not new semantic authority.

Effect authority: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1,1.1,1.2,4 and `notes/design/2026-10-15-compose-scoped-effect-release.md`, “Scope of the operation”. Composed contravariant annotation grants local concrete subtraction; allowance is distinct from actual inflow and Catch residual. Symbolic variables and later lowers remain connected, additional write survives signal handling. Compose releases the selected e protection also inside output f including id forwarding, preserves contribution attribution and independent protections, and creates no capture permission.

Actual definitions inspected: R39 `Permission`, source action and constructor inputs; R45 owner/route/construction/permission/extraction inputs; R116 selected-source and operation identity interface; all R118 and R119 definitions/proofs. R118 recursively searches finite lists and models only a partial native guard: same owner, ordinal-checked view/member read, registration-keyed unique permission plus distinct storage coordinate, and concrete-family any-guard. R119 uses ordered first search and the SAME permission value and captured index for consumption. Id denotes full interpreted identity, not a spelling or ordinal.

Applied result: R118.read_family_exact and read_permission_exact now instantiate directly in the unchanged R119.selected_retained_member proof. Given its four explicit successful read/search/read equations, that theorem derives the exact native lookup, unique selected retained record, consumed/provider family equality, and membership in that same permission. The build and audit establish this finite conditional consequence; they do not supply the four Rust equations.

First remaining source premise/owner: Luna's source-construction lane must authenticate each actual AnnotationMember's incoming input/protection state, carry it under the SAME successful FreshUse maps as the transformer, establish combined inventory bounds and stable permission/owner/vector identity, and link evaluated protection membership to the reached effect/Catch decision. R39 PRE-constructor Action/row/Inputs and prepare/permissionFor equations, R45 owner/route/extract reads, full operation/declaration identity and R54 pointer interpretation remain independently OPEN. Post-state registration/membership cannot reconstruct pre-state absence. Parent H/A/B, source/native bridge, semantic adoption and production remain OPEN.

Represented cases: empty/cons lists; failed/present view lookup; matching/mismatched ordinal; zero/one/multiple registration matches; matching/mismatched storage; equal/different owners; any true/false; ordered search including duplicates and original positions; unequal coordinate and PRE/POST examples. Omitted operational cases: allocation, mutable pointer identity, source construction history, all complete decoder guards, genuine Suppress/extract acceptance, input/protection construction/transport, Catch behavior and all-language source/native semantics. No source constructor was removed from the parent domain.

## Repair and actual checking

Two proof-term repairs only:
1. After case splitting the view lookup, the first conjunction goal is reflexive; use `rfl` instead of the old lookup equation `found`.
2. After `cases sf; cases sp`, use surviving names `family`/`permission` instead of eliminated `actualFamily`/`actualPermission`.

A byte comparison against baseline with exactly these replacements reports `EXACT_PROOF_ONLY_DELTA True`. Definitions, theorem types, assumptions, imports, axioms and historical header comments are unchanged. The old CONSTRUCTED/UNCHECKED comments describe pre-R149 history; this receipt records actual current acceptance.

Material pre-repair failure evidence is preserved in R148 proof handoff lines 173–243: line 87 expected reflexive some equality but got views lookup equality; lines 136–138 unknown eliminated names. Failed elaboration printed sorryAx for read_family_exact/decode_member; those failed declarations were never accepted results. No current build failure was hidden or replaced.

Native resolution: `elan which lake` exit 0 in notes/theory/lean returned `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`. Native `lake --version` and `lake --no-cache env lean --version` exit 0:
`Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)`;
`Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`.

One targeted build attempt, 4.440981350984657 seconds, exit 0; 13 dependency jobs. Command in notes/theory/lean:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache --fail-fast build +YulangClosure.NativePermissionDecoderR118 +YulangClosure.PermissionMemberWitnessR119`.
Environment LEAN_NUM_THREADS=1, project -j1/-M1024, subprocess timeout 120 seconds. No default build, no second attempt. Of 240-second total build allowance, 235.559 seconds remain unused; work stops.

Bundled check_lean.py was read. Its normal runner creates forbidden scratch, so the audit used an in-memory stdin Lean program with the same theorem-kind and standard-axiom whitelist checks. No scratch file was created. Seven queried names are actual theorem declarations; complete printed types and #print axioms follow. Audit command `lake --no-cache env lean -j1 -M1024 --stdin`, timeout 60 seconds, exit 0, 1.8503745180205442 seconds. All seven kind/whitelist markers appeared. No sorryAx/project axioms/native-evaluation bypass. Source search of the full twelve-module local dependency cone found only prose matches; full transitive axiom evidence is from Lean.

Warnings: unchanged R116 unused-section-variable and unused-simp warnings replayed; R118 has unused DecidableEq-section-variable warnings and its pre-existing redundant simpa warning; R119 has its pre-existing unused-section-variable warning. Removing the typeclass premises is forbidden by the fixed packet. No warning suppression or unrelated rewrite was introduced.

## Complete fresh audit program/output

```text
AUDIT_PROGRAM_BEGIN
import YulangClosure.PermissionMemberWitnessR119
import Lean.Elab.Command
import Lean.Util.CollectAxioms
set_option pp.fullNames true
#check @YulangClosure.NativePermissionDecoderR118.contains_member
#print axioms YulangClosure.NativePermissionDecoderR118.contains_member
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.NativePermissionDecoderR118.contains_member with
  | some (.thmInfo _) => pure ()
  | _ => throwError "not a theorem: YulangClosure.NativePermissionDecoderR118.contains_member"
  let axioms ← Lean.collectAxioms `YulangClosure.NativePermissionDecoderR118.contains_member
  for ax in axioms do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "unexpected axiom: {ax}"
  Lean.logInfo "THEOREM_KIND_AND_WHITELIST_OK YulangClosure.NativePermissionDecoderR118.contains_member"
#check @YulangClosure.NativePermissionDecoderR118.read_family_exact
#print axioms YulangClosure.NativePermissionDecoderR118.read_family_exact
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.NativePermissionDecoderR118.read_family_exact with
  | some (.thmInfo _) => pure ()
  | _ => throwError "not a theorem: YulangClosure.NativePermissionDecoderR118.read_family_exact"
  let axioms ← Lean.collectAxioms `YulangClosure.NativePermissionDecoderR118.read_family_exact
  for ax in axioms do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "unexpected axiom: {ax}"
  Lean.logInfo "THEOREM_KIND_AND_WHITELIST_OK YulangClosure.NativePermissionDecoderR118.read_family_exact"
#check @YulangClosure.NativePermissionDecoderR118.read_permission_exact
#print axioms YulangClosure.NativePermissionDecoderR118.read_permission_exact
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.NativePermissionDecoderR118.read_permission_exact with
  | some (.thmInfo _) => pure ()
  | _ => throwError "not a theorem: YulangClosure.NativePermissionDecoderR118.read_permission_exact"
  let axioms ← Lean.collectAxioms `YulangClosure.NativePermissionDecoderR118.read_permission_exact
  for ax in axioms do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "unexpected axiom: {ax}"
  Lean.logInfo "THEOREM_KIND_AND_WHITELIST_OK YulangClosure.NativePermissionDecoderR118.read_permission_exact"
#check @YulangClosure.NativePermissionDecoderR118.decode_member
#print axioms YulangClosure.NativePermissionDecoderR118.decode_member
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.NativePermissionDecoderR118.decode_member with
  | some (.thmInfo _) => pure ()
  | _ => throwError "not a theorem: YulangClosure.NativePermissionDecoderR118.decode_member"
  let axioms ← Lean.collectAxioms `YulangClosure.NativePermissionDecoderR118.decode_member
  for ax in axioms do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "unexpected axiom: {ax}"
  Lean.logInfo "THEOREM_KIND_AND_WHITELIST_OK YulangClosure.NativePermissionDecoderR118.decode_member"
#check @YulangClosure.NativePermissionDecoderR118.unequal_coordinates
#print axioms YulangClosure.NativePermissionDecoderR118.unequal_coordinates
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.NativePermissionDecoderR118.unequal_coordinates with
  | some (.thmInfo _) => pure ()
  | _ => throwError "not a theorem: YulangClosure.NativePermissionDecoderR118.unequal_coordinates"
  let axioms ← Lean.collectAxioms `YulangClosure.NativePermissionDecoderR118.unequal_coordinates
  for ax in axioms do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "unexpected axiom: {ax}"
  Lean.logInfo "THEOREM_KIND_AND_WHITELIST_OK YulangClosure.NativePermissionDecoderR118.unequal_coordinates"
#check @YulangClosure.NativePermissionDecoderR118.post_state_is_not_prepare_input
#print axioms YulangClosure.NativePermissionDecoderR118.post_state_is_not_prepare_input
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.NativePermissionDecoderR118.post_state_is_not_prepare_input with
  | some (.thmInfo _) => pure ()
  | _ => throwError "not a theorem: YulangClosure.NativePermissionDecoderR118.post_state_is_not_prepare_input"
  let axioms ← Lean.collectAxioms `YulangClosure.NativePermissionDecoderR118.post_state_is_not_prepare_input
  for ax in axioms do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "unexpected axiom: {ax}"
  Lean.logInfo "THEOREM_KIND_AND_WHITELIST_OK YulangClosure.NativePermissionDecoderR118.post_state_is_not_prepare_input"
#check @YulangClosure.PermissionMemberWitnessR119.selected_retained_member
#print axioms YulangClosure.PermissionMemberWitnessR119.selected_retained_member
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.PermissionMemberWitnessR119.selected_retained_member with
  | some (.thmInfo _) => pure ()
  | _ => throwError "not a theorem: YulangClosure.PermissionMemberWitnessR119.selected_retained_member"
  let axioms ← Lean.collectAxioms `YulangClosure.PermissionMemberWitnessR119.selected_retained_member
  for ax in axioms do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "unexpected axiom: {ax}"
  Lean.logInfo "THEOREM_KIND_AND_WHITELIST_OK YulangClosure.PermissionMemberWitnessR119.selected_retained_member"
AUDIT_PROGRAM_END
AUDIT_OUTPUT_BEGIN
@YulangClosure.NativePermissionDecoderR118.contains_member : ∀ {Id : Type} [inst : DecidableEq Id] (xs : List Id)
  (family : Id), YulangClosure.NativePermissionDecoderR118.contains xs family = Bool.true → family ∈ xs
'YulangClosure.NativePermissionDecoderR118.contains_member' depends on axioms: [propext]
THEOREM_KIND_AND_WHITELIST_OK YulangClosure.NativePermissionDecoderR118.contains_member
@YulangClosure.NativePermissionDecoderR118.read_family_exact : ∀ {Id : Type} [DecidableEq Id]
  (views : List (Nat × List Id)) (endpoint : YulangClosure.NativePermissionDecoderR118.Endpoint) (family : Id),
  YulangClosure.NativePermissionDecoderR118.readFamily views endpoint = Option.some family →
    ∃ allowed,
      views[endpoint.view]? = Option.some (endpoint.view, allowed) ∧ allowed[endpoint.member]? = Option.some family
'YulangClosure.NativePermissionDecoderR118.read_family_exact' depends on axioms: [propext]
THEOREM_KIND_AND_WHITELIST_OK YulangClosure.NativePermissionDecoderR118.read_family_exact
@YulangClosure.NativePermissionDecoderR118.read_permission_exact : ∀ {Id : Type} [DecidableEq Id]
  (permissions : List (Nat × YulangClosure.ComputationPermissionEntryR39.Permission Id)) (registration storage : Nat)
  (permission : YulangClosure.ComputationPermissionEntryR39.Permission Id),
  YulangClosure.NativePermissionDecoderR118.readPermission permissions registration storage = Option.some permission →
    YulangClosure.NativePermissionDecoderR118.matching permissions registration = [(storage, permission)]
'YulangClosure.NativePermissionDecoderR118.read_permission_exact' depends on axioms: [propext]
THEOREM_KIND_AND_WHITELIST_OK YulangClosure.NativePermissionDecoderR118.read_permission_exact
@YulangClosure.NativePermissionDecoderR118.decode_member : ∀ {Id State Batch : Type} [inst : DecidableEq Id]
  [inst_1 : DecidableEq State] [inst_2 : DecidableEq Batch]
  (permissionOwner viewOwner : YulangClosure.OwnedResidualProjectionR54.Owner State Batch)
  (views : List (Nat × List Id)) (permissions : List (Nat × YulangClosure.ComputationPermissionEntryR39.Permission Id))
  (endpoint : YulangClosure.NativePermissionDecoderR118.Endpoint) (registration storage : Nat) (family : Id)
  (permission : YulangClosure.ComputationPermissionEntryR39.Permission Id),
  YulangClosure.NativePermissionDecoderR118.decode permissionOwner viewOwner views permissions endpoint registration
        storage =
      Option.some (family, permission) →
    permissionOwner = viewOwner ∧
      (∃ allowed,
          views[endpoint.view]? = Option.some (endpoint.view, allowed) ∧
            allowed[endpoint.member]? = Option.some family) ∧
        YulangClosure.NativePermissionDecoderR118.matching permissions registration = [(storage, permission)] ∧
          family ∈ permission.concrete
'YulangClosure.NativePermissionDecoderR118.decode_member' depends on axioms: [propext, Quot.sound]
THEOREM_KIND_AND_WHITELIST_OK YulangClosure.NativePermissionDecoderR118.decode_member
YulangClosure.NativePermissionDecoderR118.unequal_coordinates : YulangClosure.NativePermissionDecoderR118.decode
      { state := 9, batch := 10 } { state := 9, batch := 10 } [(0, [99, 7])]
      [(0, YulangClosure.NativePermissionDecoderR118.examplePermission)] { view := 0, member := 1 } 1 0 =
    Option.some (7, YulangClosure.NativePermissionDecoderR118.examplePermission) ∧
  1 ≠ 0 ∧ 1 ≠ 7
'YulangClosure.NativePermissionDecoderR118.unequal_coordinates' depends on axioms: [propext]
THEOREM_KIND_AND_WHITELIST_OK YulangClosure.NativePermissionDecoderR118.unequal_coordinates
YulangClosure.NativePermissionDecoderR118.post_state_is_not_prepare_input : YulangClosure.NativePermissionDecoderR118.decode
      { state := 9, batch := 10 } { state := 9, batch := 10 } [(0, [7])]
      [(0, YulangClosure.InternalPermissionIncidenceR45.witnessProbe.permission)] { view := 0, member := 0 } 0 0 =
    Option.some (7, YulangClosure.InternalPermissionIncidenceR45.witnessProbe.permission) ∧
  YulangClosure.ComputationPermissionEntryR39.prepare YulangClosure.NativePermissionDecoderR118.postInputs
      YulangClosure.InternalPermissionIncidenceR45.witnessAction =
    Option.none
'YulangClosure.NativePermissionDecoderR118.post_state_is_not_prepare_input' depends on axioms: [propext, Quot.sound]
THEOREM_KIND_AND_WHITELIST_OK YulangClosure.NativePermissionDecoderR118.post_state_is_not_prepare_input
@YulangClosure.PermissionMemberWitnessR119.selected_retained_member : ∀ {Id : Type} [inst : DecidableEq Id]
  (views : List (Nat × List Id)) (permissions : List (Nat × YulangClosure.ComputationPermissionEntryR39.Permission Id))
  (endpoint : YulangClosure.NativePermissionDecoderR118.Endpoint) (registration storage permissionMember : Nat)
  (permission : YulangClosure.ComputationPermissionEntryR39.Permission Id) (providerFamily consumedFamily : Id),
  YulangClosure.NativePermissionDecoderR118.readFamily views endpoint = Option.some providerFamily →
    YulangClosure.NativePermissionDecoderR118.readPermission permissions registration storage = Option.some permission →
      YulangClosure.PermissionMemberWitnessR119.orderedSearch permission.concrete providerFamily =
          Option.some permissionMember →
        permission.concrete[permissionMember]? = Option.some consumedFamily →
          (∃ allowed,
              views[endpoint.view]? = Option.some (endpoint.view, allowed) ∧
                allowed[endpoint.member]? = Option.some providerFamily) ∧
            YulangClosure.NativePermissionDecoderR118.matching permissions registration = [(storage, permission)] ∧
              consumedFamily = providerFamily ∧ providerFamily ∈ permission.concrete
'YulangClosure.PermissionMemberWitnessR119.selected_retained_member' depends on axioms: [propext]
THEOREM_KIND_AND_WHITELIST_OK YulangClosure.PermissionMemberWitnessR119.selected_retained_member
AUDIT_OUTPUT_END
AUDIT_EXIT 0 AUDIT_SECONDS 1.8503745180205442

```

## Build output

```text
⚠ [11/13] Replayed YulangClosure.SuppressionPermissionR116
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
⚠ [12/13] Built YulangClosure.NativePermissionDecoderR118 (3.0s)
warning: YulangClosure/NativePermissionDecoderR118.lean:77:0: automatically included section variable(s) unused in theorem `YulangClosure.NativePermissionDecoderR118.read_family_exact`:
  [DecidableEq Id]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Id] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: YulangClosure/NativePermissionDecoderR118.lean:104:8: `simp` already closes the goal

Hint: Use `simp` instead of `simpa`:
  [apply] simp only [equal]

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: YulangClosure/NativePermissionDecoderR118.lean:90:0: automatically included section variable(s) unused in theorem `YulangClosure.NativePermissionDecoderR118.read_permission_exact`:
  [DecidableEq Id]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Id] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
info: YulangClosure/NativePermissionDecoderR118.lean:166:0: @YulangClosure.NativePermissionDecoderR118.contains_member : ∀ {Id : Type} [inst : DecidableEq Id] (xs : List Id)
  (family : Id), YulangClosure.NativePermissionDecoderR118.contains xs family = true → family ∈ xs
info: YulangClosure/NativePermissionDecoderR118.lean:167:0: 'YulangClosure.NativePermissionDecoderR118.contains_member' depends on axioms: [propext]
info: YulangClosure/NativePermissionDecoderR118.lean:168:0: @YulangClosure.NativePermissionDecoderR118.read_family_exact : ∀ {Id : Type} [DecidableEq Id]
  (views : List (Nat × List Id)) (endpoint : YulangClosure.NativePermissionDecoderR118.Endpoint) (family : Id),
  YulangClosure.NativePermissionDecoderR118.readFamily views endpoint = some family →
    ∃ allowed, views[endpoint.view]? = some (endpoint.view, allowed) ∧ allowed[endpoint.member]? = some family
info: YulangClosure/NativePermissionDecoderR118.lean:169:0: 'YulangClosure.NativePermissionDecoderR118.read_family_exact' depends on axioms: [propext]
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
info: YulangClosure/NativePermissionDecoderR118.lean:173:0: 'YulangClosure.NativePermissionDecoderR118.decode_member' depends on axioms: [propext, Quot.sound]
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
⚠ [13/13] Built YulangClosure.PermissionMemberWitnessR119 (402ms)
warning: YulangClosure/PermissionMemberWitnessR119.lean:57:0: automatically included section variable(s) unused in theorem `YulangClosure.PermissionMemberWitnessR119.indexed_read_member`:
  [DecidableEq Id]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Id] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
info: YulangClosure/PermissionMemberWitnessR119.lean:143:0: @YulangClosure.PermissionMemberWitnessR119.search_index_read : ∀ {Id : Type} [inst : DecidableEq Id] (xs : List Id)
  (family : Id) (member : Nat),
  YulangClosure.PermissionMemberWitnessR119.orderedSearch xs family = some member → xs[member]? = some family
info: YulangClosure/PermissionMemberWitnessR119.lean:144:0: 'YulangClosure.PermissionMemberWitnessR119.search_index_read' depends on axioms: [propext]
info: YulangClosure/PermissionMemberWitnessR119.lean:145:0: @YulangClosure.PermissionMemberWitnessR119.indexed_read_member : ∀ {Id : Type} [DecidableEq Id] (xs : List Id)
  (member : Nat) (family : Id), xs[member]? = some family → family ∈ xs
info: YulangClosure/PermissionMemberWitnessR119.lean:146:0: 'YulangClosure.PermissionMemberWitnessR119.indexed_read_member' depends on axioms: [propext]
info: YulangClosure/PermissionMemberWitnessR119.lean:147:0: @YulangClosure.PermissionMemberWitnessR119.same_record_search_read : ∀ {Id : Type} [inst : DecidableEq Id]
  (permission : YulangClosure.ComputationPermissionEntryR39.Permission Id) (searchedFamily consumedFamily : Id)
  (permissionMember : Nat),
  YulangClosure.PermissionMemberWitnessR119.orderedSearch permission.concrete searchedFamily = some permissionMember →
    permission.concrete[permissionMember]? = some consumedFamily →
      consumedFamily = searchedFamily ∧ searchedFamily ∈ permission.concrete
info: YulangClosure/PermissionMemberWitnessR119.lean:148:0: 'YulangClosure.PermissionMemberWitnessR119.same_record_search_read' depends on axioms: [propext]
info: YulangClosure/PermissionMemberWitnessR119.lean:149:0: @YulangClosure.PermissionMemberWitnessR119.selected_retained_member : ∀ {Id : Type} [inst : DecidableEq Id]
  (views : List (Nat × List Id)) (permissions : List (Nat × YulangClosure.ComputationPermissionEntryR39.Permission Id))
  (endpoint : YulangClosure.NativePermissionDecoderR118.Endpoint) (registration storage permissionMember : Nat)
  (permission : YulangClosure.ComputationPermissionEntryR39.Permission Id) (providerFamily consumedFamily : Id),
  YulangClosure.NativePermissionDecoderR118.readFamily views endpoint = some providerFamily →
    YulangClosure.NativePermissionDecoderR118.readPermission permissions registration storage = some permission →
      YulangClosure.PermissionMemberWitnessR119.orderedSearch permission.concrete providerFamily =
          some permissionMember →
        permission.concrete[permissionMember]? = some consumedFamily →
          (∃ allowed,
              views[endpoint.view]? = some (endpoint.view, allowed) ∧ allowed[endpoint.member]? = some providerFamily) ∧
            YulangClosure.NativePermissionDecoderR118.matching permissions registration = [(storage, permission)] ∧
              consumedFamily = providerFamily ∧ providerFamily ∈ permission.concrete
info: YulangClosure/PermissionMemberWitnessR119.lean:150:0: 'YulangClosure.PermissionMemberWitnessR119.selected_retained_member' depends on axioms: [propext]
info: YulangClosure/PermissionMemberWitnessR119.lean:151:0: @YulangClosure.PermissionMemberWitnessR119.certificate_member_if_extracted : ∀ {Id : Type} [inst : DecidableEq Id]
  {Artifact Term Fact : Type} [inst_1 : DecidableEq Artifact] [inst_2 : DecidableEq Term] [inst_3 : DecidableEq Fact]
  (e : YulangClosure.InternalPermissionIncidenceR45.Inputs Artifact Id Term Fact)
  (q : YulangClosure.InternalPermissionIncidenceR45.Query Artifact Id)
  (probe : YulangClosure.InternalPermissionIncidenceR45.Probe Artifact Id Term Fact)
  (out : YulangClosure.InternalPermissionIncidenceR45.Certificate Artifact Id Term Fact)
  (providerFamily consumedFamily : Id) (permissionMember : Nat),
  YulangClosure.InternalPermissionIncidenceR45.extract e q probe = some out →
    YulangClosure.PermissionMemberWitnessR119.orderedSearch probe.permission.concrete providerFamily =
        some permissionMember →
      probe.permission.concrete[permissionMember]? = some consumedFamily → providerFamily ∈ out.permission.concrete
info: YulangClosure/PermissionMemberWitnessR119.lean:152:0: 'YulangClosure.PermissionMemberWitnessR119.certificate_member_if_extracted' depends on axioms: [propext]
info: YulangClosure/PermissionMemberWitnessR119.lean:153:0: YulangClosure.PermissionMemberWitnessR119.distinct_coordinates_and_duplicates : YulangClosure.PermissionMemberWitnessR119.orderedSearch
      YulangClosure.PermissionMemberWitnessR119.examplePermission.concrete 9 =
    some 1 ∧
  YulangClosure.PermissionMemberWitnessR119.examplePermission.concrete[1]? = some 9 ∧
    YulangClosure.NativePermissionDecoderR118.readPermission
          [(0, YulangClosure.PermissionMemberWitnessR119.examplePermission)] 7 0 =
        some YulangClosure.PermissionMemberWitnessR119.examplePermission ∧
      YulangClosure.NativePermissionDecoderR118.readFamily [(0, [9])] { view := 0, member := 0 } = some 9 ∧
        7 ≠ 0 ∧ 1 ≠ 7 ∧ 1 ≠ 9
info: YulangClosure/PermissionMemberWitnessR119.lean:154:0: 'YulangClosure.PermissionMemberWitnessR119.distinct_coordinates_and_duplicates' depends on axioms: [propext]
Build completed successfully (13 jobs).

BUILD_EXIT 0 BUILD_SECONDS 4.440981350984657

```

## Dependency and source-search receipts

```text
DEPENDENCY notes/theory/lean/YulangClosure/PermissionMemberWitnessR119.lean f0d3d9c51a270b19f24acaf6edecec0885dda1fd1b2718db88dd4105db6a343f BASELINE_EQUAL True
SOURCE_SEARCH notes/theory/lean/YulangClosure/PermissionMemberWitnessR119.lean 5 types or axiom results have been observed. Audit commands below are future work.
SOURCE_SEARCH notes/theory/lean/YulangClosure/PermissionMemberWitnessR119.lean 142 -- Future audits only. No output or axiom list has been observed.
DEPENDENCY notes/theory/lean/YulangClosure/NativePermissionDecoderR118.lean f976e0b3b5e8b2b70ee902bdca30ce140db503a4972e8cf1b621892b57bf5d27 BASELINE_EQUAL False
SOURCE_SEARCH notes/theory/lean/YulangClosure/NativePermissionDecoderR118.lean 4 R118 CONSTRUCTED / UNCHECKED: no Lean/Lake/checker execution or axiom receipt.
SOURCE_SEARCH notes/theory/lean/YulangClosure/NativePermissionDecoderR118.lean 165 -- FUTURE audit commands: no outputs or axiom sets have been observed.
DEPENDENCY notes/theory/lean/YulangClosure/SuppressionPermissionR116.lean 2aed350468964d90d8d83714177fff77d477e3df0846ae23150194bd76270e3a BASELINE_EQUAL True
SOURCE_SEARCH notes/theory/lean/YulangClosure/SuppressionPermissionR116.lean 5 R116: CONSTRUCTED / UNCHECKED. No Lean, Lake or axiom audit was executed.
DEPENDENCY notes/theory/lean/YulangClosure/OwnedResidualProjectionR54.lean cc5d0b01485560e5091ce454b066ca2fc41eb350eee24ae525133a13bed401c9 BASELINE_EQUAL True
SOURCE_SEARCH notes/theory/lean/YulangClosure/OwnedResidualProjectionR54.lean 224 retained value. The property is not an input equivalence/extraction axiom. -/
DEPENDENCY notes/theory/lean/YulangClosure/WholePublicationResidualR53.lean dc9c89e562f905c2c6284fd15eb82e9482a82bc9b2881f567c3454198318f391 BASELINE_EQUAL True
DEPENDENCY notes/theory/lean/YulangClosure/PerCallResidualPublicationR52.lean d0ffaad36139148c3898d70c9da2e03d1b0e17cbb8b71841f751a8720570e73e BASELINE_EQUAL True
DEPENDENCY notes/theory/lean/YulangClosure/NativeResidualPublicationR51.lean 78a729b25e95812ba292c4e625ec69e46ff5eb70ff3ac2ae5b85dd1b33214d61 BASELINE_EQUAL True
DEPENDENCY notes/theory/lean/YulangClosure/AuthenticatedResidualConsumerR49.lean 4fc4380f3ad1827ecf155f982e5186b32d6d66d91909039fb118063d8f1e2df2 BASELINE_EQUAL True
DEPENDENCY notes/theory/lean/YulangClosure/ProviderEntryArrivalR48.lean b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575 BASELINE_EQUAL True
DEPENDENCY notes/theory/lean/YulangClosure/CurrentEmissionOwnershipR47.lean d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c BASELINE_EQUAL True
DEPENDENCY notes/theory/lean/YulangClosure/InternalPermissionIncidenceR45.lean 9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f BASELINE_EQUAL True
DEPENDENCY notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean 748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e BASELINE_EQUAL True

EXACT_PROOF_ONLY_DELTA True
GOVERNING notes/theory/lean/lean-toolchain ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c BASELINE_EQUAL True
GOVERNING notes/theory/lean/lakefile.toml 212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4 BASELINE_EQUAL True
GOVERNING notes/theory/lean/lake-manifest.json 058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3 BASELINE_EQUAL True
GOVERNING notes/design/2026-10-10-annotation-effect-hygiene-integration.md a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18 BASELINE_EQUAL True
GOVERNING notes/design/2026-10-15-compose-scoped-effect-release.md fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679 BASELINE_EQUAL True
GOVERNING notes/theory/2026-10-13-intrusion-source-preservation-proof.md 3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271 BASELINE_EQUAL True
GOVERNING notes/design/2026-10-24-birth-level-scc-intrusion.md ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae BASELINE_EQUAL True
GOVERNING docs/yulang-whole-proof-closure-ja.md 17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5 BASELINE_EQUAL True

```

## Generated outputs and stop receipt

Existing .lake regular data before: 48734666 bytes in 199 files.
After build and after stdin audit: 49408795 bytes in 214 files.
Net growth 674129 bytes (<16 MiB). Audit caused no cache change.
Deleted files: none. Modified existing/new outputs, with complete SHA-256 and sizes:
```json
[
  {
    "path": "notes/theory/lean/.lake/build/ir/YulangClosure/PermissionMemberWitnessR119.c",
    "size": 13058,
    "sha256": "44e062f74858b1c6c6e7659f984ba55081d879098d8426e02f72faf7a9690e8a",
    "previous": null
  },
  {
    "path": "notes/theory/lean/.lake/build/ir/YulangClosure/PermissionMemberWitnessR119.c.hash",
    "size": 16,
    "sha256": "31dba3816abf817b2fdb6dc7e62b85cde51fd501851b5e405e243fab5f7ed6f1",
    "previous": null
  },
  {
    "path": "notes/theory/lean/.lake/build/ir/YulangClosure/NativePermissionDecoderR118.c",
    "size": 33105,
    "sha256": "a8900bdb1a4c2fff98f75e8cb1deb256dfeb2e6ad289df18d8441eaa01a2840f",
    "previous": null
  },
  {
    "path": "notes/theory/lean/.lake/build/ir/YulangClosure/PermissionMemberWitnessR119.setup.json",
    "size": 2070,
    "sha256": "e2d7e334c00edf7cb6d816533e954cfcc6ca9fe5f45b5b916a4b2afb2883f008",
    "previous": null
  },
  {
    "path": "notes/theory/lean/.lake/build/ir/YulangClosure/NativePermissionDecoderR118.c.hash",
    "size": 16,
    "sha256": "d7c1e123b90006b82fcc2c23bcfe4fd7bd8a89220297d4e831ced3d1064f1a9c",
    "previous": null
  },
  {
    "path": "notes/theory/lean/.lake/build/lib/lean/YulangClosure/NativePermissionDecoderR118.trace",
    "size": 8223,
    "sha256": "33a848278ff95d3caf984f457004e8621dc0f7776af42fe3a92cb87180e8cbb2",
    "previous": null
  },
  {
    "path": "notes/theory/lean/.lake/build/lib/lean/YulangClosure/NativePermissionDecoderR118.ilean",
    "size": 21223,
    "sha256": "edad5b40318993f79a7c47cf74992cdea9cdc5ee300a49cf7b95a071b0e55f89",
    "previous": null
  },
  {
    "path": "notes/theory/lean/.lake/build/lib/lean/YulangClosure/PermissionMemberWitnessR119.trace",
    "size": 8153,
    "sha256": "7de81075d75da4a37eeceaaada4681979d4fbe82d9046cd7d5ef5c5ac12a8184",
    "previous": null
  },
  {
    "path": "notes/theory/lean/.lake/build/lib/lean/YulangClosure/PermissionMemberWitnessR119.olean",
    "size": 185784,
    "sha256": "d55418d9719828254bf1eedb9cab0fd1bb4a2d3ec1a2d72e8702a7febd51dac6",
    "previous": null
  },
  {
    "path": "notes/theory/lean/.lake/build/lib/lean/YulangClosure/NativePermissionDecoderR118.olean.hash",
    "size": 16,
    "sha256": "cd3bcbea6e26bcf65cc7c06b6c173c2ccd5d1fa22d6fd0cdaab83b32e9940803",
    "previous": null
  },
  {
    "path": "notes/theory/lean/.lake/build/lib/lean/YulangClosure/PermissionMemberWitnessR119.olean.hash",
    "size": 16,
    "sha256": "71ccf565001f89793ba20888cbc57beef242b15ee6f58ef5913bee2627284b4f",
    "previous": null
  },
  {
    "path": "notes/theory/lean/.lake/build/lib/lean/YulangClosure/NativePermissionDecoderR118.ilean.hash",
    "size": 16,
    "sha256": "e921fe17dc6ddba244996e0930571879865273a64ce9ea13bca276a4dbdb5a15",
    "previous": null
  },
  {
    "path": "notes/theory/lean/.lake/build/lib/lean/YulangClosure/PermissionMemberWitnessR119.ilean.hash",
    "size": 16,
    "sha256": "861f91c681f62b7729291245212f9161498c8bd5b292ef1f75905f915baef667",
    "previous": null
  },
  {
    "path": "notes/theory/lean/.lake/build/lib/lean/YulangClosure/PermissionMemberWitnessR119.ilean",
    "size": 17889,
    "sha256": "db7b9256e3b4af902168ab8c72ae015093c84f6b47975dd95a35fff39bafdb84",
    "previous": null
  },
  {
    "path": "notes/theory/lean/.lake/build/lib/lean/YulangClosure/NativePermissionDecoderR118.olean",
    "size": 384528,
    "sha256": "bff9cdc9e04183f5555083b1303bbb746f1b822e1b9761fb956d1dfbeb2e94a2",
    "previous": null
  }
]
```

Verification cache ownership returns to Luna with these frozen bytes. All author work and writes STOPPED after this handoff revision. No descendants or unresolved author-created leases. No independent-review receipt is claimed; primary must appoint/consume fresh review and decide integration. No production authority is claimed.
