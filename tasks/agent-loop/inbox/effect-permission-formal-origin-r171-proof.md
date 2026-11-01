# R171 formal registration origin proof

Status: **KERNEL_ACCEPTED CONDITIONAL MATHEMATICS; SOURCE APPLICATION BLOCKED**.
Independent review pending. No inference-soundness gate is closed.
Module writes stopped. Both permitted proof-check invocations are spent.

## Authority, dependencies, and original goal

Packet: `tasks/agent-loop/sprints/effect-permission-formal-origin-r171.md`,
SHA-256 `8289f460cb3a3057118bda0337722699714c1debe3b349db51691cae2d7e541e`.
Source handoff: `tasks/agent-loop/inbox/effect-permission-formal-origin-r171-source.md`,
SHA-256 `8db9a9730932aedd162ad4c918000c6c73176323eae797be022a197db2174f22`.
R169 module SHA-256
`bb0aaffe95f99881b089807a202991c4349a7c61e9ebb0f42f56d7f080a7baf4`.
Frozen output module SHA-256
`03e727c104e2773ec3bbe1589c5dfb61ddb2df40d40a54de6be45583d01506f6`.
All four Rust/HIR source hashes are the unchanged hashes in the packet/source
handoff; this lane inspected only those admitted inputs and governing Lean sources.

The current user clarification fixes the target as **soundness of Yulang type
inference, including inferred effect rows, for the source typing rules**.
Correctness or safety of the Rust program evaluator/machine is outside that target.
The original parent is `YulangClosure.SourceProblem.InferenceSoundness`,
`Contracts.lean:127`: for every supported source `s`, source scope `x`, generated
constraint object `d`, and solution `a`, `generates s x d` and `solves d a` must
produce one shared witness `e` with both `sourceJudgment s x e` and
`sameScoped s x e a`. This file neither changes those quantifiers nor supplies
that witness. Governing sources read: `docs/yulang-whole-proof-closure-ja.md`
§§1,4; source preservation manuscript `2026-10-13-intrusion-source-preservation-proof.md`
§1; Authoritative top-level inference principles §§1–3; actual Contracts and
R39/R169 definitions; the frozen R171 source mapping. The manuscript's older
cross-level qualification is not reactivated; no intrusion theorem is claimed.

R171 contributes a possible local **inference-construction** premise: the
annotation consumed by the FormalEntry inference constructor comes from the
same source Lambda as its retained registration. It does not establish a
source typing rule or the actual inference `generates`/`solves` judgments.

## Checked mathematical content and exact construction boundaries

Namespace: `YulangClosure.FormalEntryOriginR171`.
The nine theorem types and full transitive axiom results appear verbatim below.

- `construction_keys`: checked finite branded ordinal allocation, skipped
  ordinals, whole-expression permutation imply distinct Lambda parameter keys
  and an ordinal bound. No final-map uniqueness premise is assumed.
- `scan_prefix`, `formal_read_preserved`, `recipe_read_preserved`: finite
  append events preserve arbitrary existing formal/recipe prefixes and reads.
- `lookup_unchanged`: a scan that never inserts a selected key preserves its
  old lookup. Writes are prepended, matching last-write-wins insertion with
  R169's first-match list lookup, including duplicate overwrite behavior.
- `scan_origin`: distinct keys and a finite scan identify the exact appended
  owner, Lambda index, parameter, scope, and recipe. Its distinctness premise is
  discharged by `construction_keys` in `constructed_scan_origin`.
- `collected_origin`: under explicit equality with one collector snapshot,
  action selection/annotation reads transport that origin into exact R169
  Raw/action fields and the selected source annotation.
- `successful_annotation_origin`: kernel-accepted conditional composition with
  R169's existing successful_nonempty theorem. **Its advertised source
  application is currently uninhabited for newly scanned registrations**, as
  explained immediately below. Do not count it as an applied soundness lemma.

`Construction` represents the initial owner-branded header interval, record or
receiver allocations that do not get Lambda registrations, checked u32
increment, and a permutation that retains the entire immutable expression,
parameter, and annotation. All non-Lambda source constructors remain opaque
`Expression.other`; no inference or source typing case for them is proved.
The concrete SourceRootId-to-Brand embedding, native source/entry encoding,
HIR work-stack realization of the allocation-to-expression permutation, and
all crate-internal mutations are not formalized. In particular the model does
not pretend that `set_at_range` dynamically checks single assignment.

## Two blocking application defects discovered after kernel acceptance

1. **Preparation updates the selected formal.** `newFormal` sets `entry = none`.
   `collected_origin` and `successful_annotation_origin` require literal
   `x.formals = afterScan.formals`. R169 successful entry requires the selected
   formal's `entry = some port`. The scan-origin theorem identifies that
   selected formal with the new record whose entry is none, so these literal
   snapshot equations exclude the intended nonempty successful application.
   The exact missing inference-preparation input is
   `candidate_source.rs:2303–2325`,
   `InferenceSession::initialize_candidate_source_levels`: it checks the retained
   parameter recipe/native-root precondition, constructs the native parameter
   root, allocates an entry effect for computation-role formals, and updates
   `native_root` and `entry_effect` in place. A next packet must model those
   successful updates and prove preservation of owner, Lambda index, parameter,
   recipe, scope, role, registration ordinal, and registry/source snapshot.
   R169 should receive the **prepared** formals, joined to collector origins by
   a proved projection. Removing the entry requirement or pretending the two
   entire formal vectors are literally equal would be incorrect.

2. **Record-pattern recipe appends are missing from Scan.**
   `candidate_source.rs:1119–1123` appends each record field binder recipe after
   appending the Lambda formal, before scanning later expressions. Current
   `Scan` appends only the Lambda parameter recipe. `Construction.skip` accounts
   for ID-allocation gaps, but does not account for these recipe-vector writes.
   Thus equality with the actual collector recipe vector is not established
   for record-formal sources. The next packet must include exact field-recipe
   append events (and the explicit duplicate-rejection result), preserving the
   formal's saved recipe position across these events and the next Lambda.
   Record parameters remain part of the accepted parent source language.

The allocation/permutation relation is itself conditional on the real HIR
retained-work traversal; a textual constructor inspection is not that Lean
realization theorem. These are precise missing model-construction premises,
not a demonstrated reachable Rust defect and not permission to shrink the
source domain or insert a new runtime annotation check.

## Parent application and next missing inference judgment

The intended application is to discharge the local annotation-origin premise
when interpreting FormalEntry constraint generation. First repair and realize
the finite collector/preparation relation above, then connect its annotation
and retained permission/effect-row fields to the **actual** source-rule-based
inference judgment. No concrete theorem currently turns a successful
`Trace`/`prepare`/publication into `p.generates s x d`, proves that the actual
solver result satisfies `p.solves d a`, or constructs the parent shared witness
`e` and `sameScoped` interpretation. The next parent bridge is that inference
judgment/constraint-generation and solution-to-source-derivation connection,
including the original effect-row rules. R116 selected-operation/endpoint
interpretation and the dependent hygiene consumer premises also remain open.
No Rust evaluator correctness or whole program execution guarantee is needed
or claimed by this packet.

## Execution prerequisites, commands, and resources

Read `.agents/skills/yulang-lean-proofs/SKILL.md`, its sources/execution
references, root AGENTS and sprint rules, pinned project toolchain,
`lakefile.toml`, `lake-manifest.json`, and the relevant README sections.
Installed native Lake resolved by `elan which lake` to
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
`lake --version` returned `Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)`.
Native `lean --version` returned `Lean (version 4.35.0,
x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`.
Version queries were read-only; two proof-check processes were run.

Before execution, the existing R116 import closure was authenticated read-only
using Python ctypes and the pinned `libleanshared.so` string/byte-array hash
primitives plus Lake.Build.Trace's `mix nil (hash ...)` formula. Runtime SHA-256:
`efef27df56f2197139afe12f1a2b63913a05f1aba81ce88824c44100431ed8c4`.
Each normalized source Lake hash and binary olean hash matched its Lake trace
and `.olean.hash`. No import was built or refreshed. Ten imports were covered:

| Module suffix | Source Lake hash | Olean Lake hash |
| --- | --- | --- |
| SuppressionPermissionR116 | f1627e55d503c891 | d7b1a26e193e633c |
| InternalPermissionIncidenceR45 | 32cdd0fe8e9b3ea0 | d5e1b6e5d0304f49 |
| ComputationPermissionEntryR39 | b63d4294b527f1e1 | 255a584c844384db |
| OwnedResidualProjectionR54 | 4383a1c667636605 | 238b65ed9a2a4f1b |
| WholePublicationResidualR53 | 9d4b84a0ea893366 | bc6f829a42b79380 |
| PerCallResidualPublicationR52 | dd8967765451c9a6 | 4944366f9be8f817 |
| NativeResidualPublicationR51 | a4f7c4f1d3613962 | 8070fda240bbdaf5 |
| AuthenticatedResidualConsumerR49 | 9e5830b41bb2c530 | 62ae7e0ea8a57d39 |
| ProviderEntryArrivalR48 | 24eb86a31d8ccc7f | 4ce600da5832739f |
| CurrentEmissionOwnershipR47 | 0799c249ecf5bac7 | 75e54b9c9d11b774 |

R169 has no olean. With primary approval, each check passed a deterministic
in-memory stream to the installed native executable, from `notes/theory/lean`:

```text
LEAN_PATH=/home/momota1029/rust/yulang/notes/theory/lean/.lake/build/lib/lean
LEAN_NUM_THREADS=1
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --stdin
```

The stream is exact frozen R169 bytes, one LF byte, R171 bytes with only its
first `import YulangClosure.FormalEntryPrestateBridgeR169` line removed, then
one LF and `#check @FULLY.QUALIFIED.NAME` / `#print axioms FULLY.QUALIFIED.NAME`
for all nine theorem names in the order listed above. No other transformation,
source temporary, output path, setup generation, helper or Lake build was used.
Both stdout and stderr were captured in memory; final stdout/stderr was then
written into this leased handoff, not into a generated Lean output.
Each subprocess had a 180-second wall cap, one Lean thread and `-M1024`.

First proof check: exit 1, 5.3871255639824085 seconds, peak child RSS 792700 KiB.
Source SHA `eb2643241f218fbc67a7dc3b3a837a557f0ae886b6e0b6d6e762660ef7d9e4a7`;
stream SHA `2e4ef453349a78060b1963a3c802eb543583f103800b3d27c789bf66197aea6b`.
Material diagnostics, in combined-stdin line numbers:

```text
<stdin>:499:6: error: Type mismatch: After simplification, term ih.left
has type (List.filterMap parameterKey expressions).Nodup
but the target also requires the singleton append disjointness condition.
<stdin>:507:51: error: Type mismatch: After simplification, term ih
still has a filterMap singleton for Expression.other on the target side.
<stdin>:617:50: error: Type mismatch: After simplification, term distinct
has a filterMap of (Expression.other occurrence' :: rest), not rest.
<stdin>:628:60: error(lean.unknownIdentifier): Unknown identifier `parameter.id`
<stdin>:628:87: error(lean.unknownIdentifier): Unknown identifier `parameter`
```

These errors were repaired by an explicit append disjointness proof, explicit
`List.filterMap_cons` reduction, and directed substitution of constructor
parameters. First-check audits contained elaboration-generated `sorryAx` for
construction_keys, scan_origin and their dependents; they were a failed check,
not delivered accepted results. No explicit hole was inserted in source.
The second check below is the final module check and complete audit. It passed
with only two unused-section-variable linter warnings. No third check occurred.
The helper/default build was not run because the fixed packet forbids generated
outputs/builds. This also means there is no new R171 import artifact.

Source search across R171, exact R169, and all ten authenticated project imports
for sorry/admit/project axioms/skipKernelTC/native_decide returned no matches.
This search supplements the transitive axiom audits; it does not replace them.

`.lake` inventory before and after: 424 files / 100516779 bytes. No environment,
cache, target, scratch, Cargo/build/test or Git action was taken. Only the new
Lean module and this handoff were written. The two check times totaled about
7.12 seconds; maximum measured child RSS was 806628 KiB. Whole assignment wall
elapsed and parent/worker model/effort metadata are not tool-observed, and are
not invented. Requested role was lean_prover; effective model/effort UNKNOWN.
No descendants were started.

## Frozen output / STOP

- `notes/theory/lean/YulangClosure/FormalEntryOriginR171.lean`: frozen, SHA above.
- `tasks/agent-loop/inbox/effect-permission-formal-origin-r171-proof.md`: this
  handoff; final SHA sent to primary after writing.
- Scratch/generated paths: none. Module and handoff writes STOPPED after the
  final hash receipt. No independently reviewed or production authority claim.

## Second and final stdin verification

Module SHA-256: `03e727c104e2773ec3bbe1589c5dfb61ddb2df40d40a54de6be45583d01506f6`.
Stream SHA-256: `4166f5c2213ca55ce406d8f2286cbe292c66ff0fee3228c699140855b44b8bc1`.
Exit: 0. Elapsed seconds: 1.7314810889947694. Peak child RSS KiB: 806628.

```text
<stdin>:480:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.FormalEntryOriginR171.construction_keys`:
  [DecidableEq Brand]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Brand] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:556:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.FormalEntryOriginR171.scan_prefix`:
  [DecidableEq Id]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Id] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
@YulangClosure.FormalEntryOriginR171.construction_keys : ∀ {Brand : Type} [DecidableEq Brand] (owner : Brand)
  (next : Nat)
  (expressions :
    List (YulangClosure.FormalEntryPrestateBridgeR169.Expression (YulangClosure.FormalEntryOriginR171.Identity Brand))),
  YulangClosure.FormalEntryOriginR171.Construction owner next expressions →
    (YulangClosure.FormalEntryOriginR171.keys expressions).Nodup ∧
      ∀ (key : YulangClosure.FormalEntryOriginR171.Identity Brand),
        key ∈ YulangClosure.FormalEntryOriginR171.keys expressions →
          ∃ ordinal, ordinal < next ∧ key = YulangClosure.FormalEntryOriginR171.Identity.parameter owner ordinal
'YulangClosure.FormalEntryOriginR171.construction_keys' depends on axioms: [propext, Quot.sound]
@YulangClosure.FormalEntryOriginR171.scan_prefix : ∀ {Id : Type} [DecidableEq Id] (owner : Id) (scope : Id → Id)
  (index : Nat) (expressions : List (YulangClosure.FormalEntryPrestateBridgeR169.Expression Id))
  (before after : YulangClosure.FormalEntryOriginR171.ScanState Id),
  YulangClosure.FormalEntryOriginR171.Scan owner scope index expressions before after →
    (∃ suffix, after.formals = before.formals ++ suffix) ∧ ∃ suffix, after.recipes = before.recipes ++ suffix
'YulangClosure.FormalEntryOriginR171.scan_prefix' depends on axioms: [propext]
@YulangClosure.FormalEntryOriginR171.lookup_unchanged : ∀ {Id : Type} [inst : DecidableEq Id] (owner : Id)
  (scope : Id → Id) (index : Nat) (expressions : List (YulangClosure.FormalEntryPrestateBridgeR169.Expression Id))
  (before after : YulangClosure.FormalEntryOriginR171.ScanState Id),
  YulangClosure.FormalEntryOriginR171.Scan owner scope index expressions before after →
    ∀ (key : Id),
      ¬key ∈ YulangClosure.FormalEntryOriginR171.keys expressions →
        YulangClosure.FormalEntryPrestateBridgeR169.readRegistration after.registry key =
          YulangClosure.FormalEntryPrestateBridgeR169.readRegistration before.registry key
'YulangClosure.FormalEntryOriginR171.lookup_unchanged' depends on axioms: [propext, Quot.sound]
@YulangClosure.FormalEntryOriginR171.formal_read_preserved : ∀ {Id : Type} [DecidableEq Id] (owner : Id)
  (scope : Id → Id) (index : Nat) (expressions : List (YulangClosure.FormalEntryPrestateBridgeR169.Expression Id))
  (before after : YulangClosure.FormalEntryOriginR171.ScanState Id),
  YulangClosure.FormalEntryOriginR171.Scan owner scope index expressions before after →
    ∀ (registration : Nat) (formal : YulangClosure.ComputationPermissionEntryR39.Registration Id),
      before.formals[registration]? = some formal → after.formals[registration]? = some formal
'YulangClosure.FormalEntryOriginR171.formal_read_preserved' depends on axioms: [propext]
@YulangClosure.FormalEntryOriginR171.recipe_read_preserved : ∀ {Id : Type} [DecidableEq Id] (owner : Id)
  (scope : Id → Id) (index : Nat) (expressions : List (YulangClosure.FormalEntryPrestateBridgeR169.Expression Id))
  (before after : YulangClosure.FormalEntryOriginR171.ScanState Id),
  YulangClosure.FormalEntryOriginR171.Scan owner scope index expressions before after →
    ∀ (recipe : Nat) (parameter : Id),
      before.recipes[recipe]? = some parameter → after.recipes[recipe]? = some parameter
'YulangClosure.FormalEntryOriginR171.recipe_read_preserved' depends on axioms: [propext]
@YulangClosure.FormalEntryOriginR171.scan_origin : ∀ {Id : Type} [inst : DecidableEq Id] (owner : Id) (scope : Id → Id)
  (index : Nat) (expressions : List (YulangClosure.FormalEntryPrestateBridgeR169.Expression Id))
  (before after : YulangClosure.FormalEntryOriginR171.ScanState Id),
  YulangClosure.FormalEntryOriginR171.Scan owner scope index expressions before after →
    (YulangClosure.FormalEntryOriginR171.keys expressions).Nodup →
      ∀ (offset : Nat) (occurrence : Id) (parameter : YulangClosure.FormalEntryPrestateBridgeR169.Parameter Id),
        expressions[offset]? =
            some (YulangClosure.FormalEntryPrestateBridgeR169.Expression.lambda occurrence parameter) →
          ∃ registration formal,
            YulangClosure.FormalEntryPrestateBridgeR169.readRegistration after.registry parameter.id =
                some registration ∧
              after.formals[registration]? = some formal ∧
                formal.owner = owner ∧
                  formal.lambda = index + offset ∧
                    formal.parameter = parameter.id ∧
                      formal.scope = scope parameter.id ∧ after.recipes[formal.recipe]? = some parameter.id
'YulangClosure.FormalEntryOriginR171.scan_origin' depends on axioms: [propext, Quot.sound]
@YulangClosure.FormalEntryOriginR171.constructed_scan_origin : ∀ {Brand : Type} [inst : DecidableEq Brand]
  (brand : Brand) (next : Nat)
  (expressions :
    List (YulangClosure.FormalEntryPrestateBridgeR169.Expression (YulangClosure.FormalEntryOriginR171.Identity Brand))),
  YulangClosure.FormalEntryOriginR171.Construction brand next expressions →
    ∀ (scope : YulangClosure.FormalEntryOriginR171.Identity Brand → YulangClosure.FormalEntryOriginR171.Identity Brand)
      (before after :
        YulangClosure.FormalEntryOriginR171.ScanState (YulangClosure.FormalEntryOriginR171.Identity Brand)),
      YulangClosure.FormalEntryOriginR171.Scan (YulangClosure.FormalEntryOriginR171.Identity.owner brand) scope 0
          expressions before after →
        ∀ (index : Nat) (occurrence : YulangClosure.FormalEntryOriginR171.Identity Brand)
          (parameter :
            YulangClosure.FormalEntryPrestateBridgeR169.Parameter (YulangClosure.FormalEntryOriginR171.Identity Brand)),
          expressions[index]? =
              some (YulangClosure.FormalEntryPrestateBridgeR169.Expression.lambda occurrence parameter) →
            ∃ registration formal,
              YulangClosure.FormalEntryPrestateBridgeR169.readRegistration after.registry parameter.id =
                  some registration ∧
                after.formals[registration]? = some formal ∧
                  formal.owner = YulangClosure.FormalEntryOriginR171.Identity.owner brand ∧
                    formal.lambda = index ∧
                      formal.parameter = parameter.id ∧
                        formal.scope = scope parameter.id ∧ after.recipes[formal.recipe]? = some parameter.id
'YulangClosure.FormalEntryOriginR171.constructed_scan_origin' depends on axioms: [propext, Quot.sound]
@YulangClosure.FormalEntryOriginR171.collected_origin : ∀ {Brand : Type} [inst : DecidableEq Brand] (brand : Brand)
  (next : Nat)
  (expressions :
    List (YulangClosure.FormalEntryPrestateBridgeR169.Expression (YulangClosure.FormalEntryOriginR171.Identity Brand))),
  YulangClosure.FormalEntryOriginR171.Construction brand next expressions →
    ∀ (scope : YulangClosure.FormalEntryOriginR171.Identity Brand → YulangClosure.FormalEntryOriginR171.Identity Brand)
      (before after :
        YulangClosure.FormalEntryOriginR171.ScanState (YulangClosure.FormalEntryOriginR171.Identity Brand)),
      YulangClosure.FormalEntryOriginR171.Scan (YulangClosure.FormalEntryOriginR171.Identity.owner brand) scope 0
          expressions before after →
        ∀ (x : YulangClosure.FormalEntryPrestateBridgeR169.Raw (YulangClosure.FormalEntryOriginR171.Identity Brand))
          (a : YulangClosure.ComputationPermissionEntryR39.Action (YulangClosure.FormalEntryOriginR171.Identity Brand)),
          x.formals = after.formals →
            x.recipes = after.recipes →
              x.formalRegistrations = after.registry →
                YulangClosure.FormalEntryPrestateBridgeR169.readSource x.sources
                      (YulangClosure.FormalEntryOriginR171.Identity.owner brand) =
                    some expressions →
                  ∀ (index : Nat)
                    (parameter :
                      YulangClosure.FormalEntryPrestateBridgeR169.Parameter
                        (YulangClosure.FormalEntryOriginR171.Identity Brand)),
                    expressions[index]? =
                        some (YulangClosure.FormalEntryPrestateBridgeR169.Expression.lambda a.occurrence parameter) →
                      parameter.annotation = some a.annotation →
                        YulangClosure.FormalEntryPrestateBridgeR169.readRegistration x.formalRegistrations
                              parameter.id =
                            some a.registration →
                          ∃ formal,
                            x.formals[a.registration]? = some formal ∧
                              formal.owner = YulangClosure.FormalEntryOriginR171.Identity.owner brand ∧
                                formal.lambda = index ∧
                                  formal.parameter = parameter.id ∧
                                    x.recipes[formal.recipe]? = some parameter.id ∧
                                      ∃ sourceParameter,
                                        YulangClosure.FormalEntryPrestateBridgeR169.readSource x.sources formal.owner =
                                            some expressions ∧
                                          expressions[formal.lambda]? =
                                              some
                                                (YulangClosure.FormalEntryPrestateBridgeR169.Expression.lambda
                                                  a.occurrence sourceParameter) ∧
                                            sourceParameter.id = formal.parameter ∧
                                              sourceParameter.annotation = some a.annotation
'YulangClosure.FormalEntryOriginR171.collected_origin' depends on axioms: [propext, Quot.sound]
@YulangClosure.FormalEntryOriginR171.successful_annotation_origin : ∀ {Brand : Type} [inst : DecidableEq Brand]
  (brand : Brand) (next : Nat)
  (expressions :
    List (YulangClosure.FormalEntryPrestateBridgeR169.Expression (YulangClosure.FormalEntryOriginR171.Identity Brand))),
  YulangClosure.FormalEntryOriginR171.Construction brand next expressions →
    ∀ (scope : YulangClosure.FormalEntryOriginR171.Identity Brand → YulangClosure.FormalEntryOriginR171.Identity Brand)
      (before afterScan :
        YulangClosure.FormalEntryOriginR171.ScanState (YulangClosure.FormalEntryOriginR171.Identity Brand)),
      YulangClosure.FormalEntryOriginR171.Scan (YulangClosure.FormalEntryOriginR171.Identity.owner brand) scope 0
          expressions before afterScan →
        ∀ (x : YulangClosure.FormalEntryPrestateBridgeR169.Raw (YulangClosure.FormalEntryOriginR171.Identity Brand))
          (a : YulangClosure.ComputationPermissionEntryR39.Action (YulangClosure.FormalEntryOriginR171.Identity Brand)),
          x.formals = afterScan.formals →
            x.recipes = afterScan.recipes →
              x.formalRegistrations = afterScan.registry →
                YulangClosure.FormalEntryPrestateBridgeR169.readSource x.sources
                      (YulangClosure.FormalEntryOriginR171.Identity.owner brand) =
                    some expressions →
                  ∀ (index : Nat)
                    (parameter :
                      YulangClosure.FormalEntryPrestateBridgeR169.Parameter
                        (YulangClosure.FormalEntryOriginR171.Identity Brand)),
                    expressions[index]? =
                        some (YulangClosure.FormalEntryPrestateBridgeR169.Expression.lambda a.occurrence parameter) →
                      parameter.annotation = some a.annotation →
                        YulangClosure.FormalEntryPrestateBridgeR169.readRegistration x.formalRegistrations
                              parameter.id =
                            some a.registration →
                          ∀
                            (f :
                              YulangClosure.ComputationPermissionEntryR39.Registration
                                (YulangClosure.FormalEntryOriginR171.Identity Brand))
                            (r :
                              YulangClosure.ComputationPermissionEntryR39.Row
                                (YulangClosure.FormalEntryOriginR171.Identity Brand))
                            (port : YulangClosure.FormalEntryOriginR171.Identity Brand)
                            (pending :
                              Option
                                (YulangClosure.ComputationPermissionEntryR39.Permission
                                  (YulangClosure.FormalEntryOriginR171.Identity Brand)))
                            (after :
                              YulangClosure.ComputationPermissionEntryR39.State
                                (YulangClosure.FormalEntryOriginR171.Identity Brand)),
                            YulangClosure.FormalEntryPrestateBridgeR169.Trace x a
                                (YulangClosure.FormalEntryPrestateBridgeR169.Phase.ok f r port pending) after →
                              r.concrete ≠ [] →
                                (∃ sourceParameter,
                                    YulangClosure.FormalEntryPrestateBridgeR169.readSource x.sources f.owner =
                                        some expressions ∧
                                      expressions[f.lambda]? =
                                          some
                                            (YulangClosure.FormalEntryPrestateBridgeR169.Expression.lambda a.occurrence
                                              sourceParameter) ∧
                                        sourceParameter.id = f.parameter ∧
                                          sourceParameter.annotation = some a.annotation) ∧
                                  ∃ p,
                                    pending = some p ∧
                                      p.concrete = r.concrete ∧ after.permissions = x.before.permissions ++ [p]
'YulangClosure.FormalEntryOriginR171.successful_annotation_origin' depends on axioms: [propext, Quot.sound]
```
