# C438 scope-specific verification and additional controls

Technique pin: `efecd0ba5ce1a63c184edaba75637f2e9a7cec44`; exact Lean tree `2bba5d89d1e8d9c2d94c5fc3a8a359c3b3b63421`. Physical independent build command for each new production module in dependency order: `lean --trust=0 -DwarningAsError=true -o <production-only-cache>/Yulang/<module>.olean Yulang/<module>.lean`. For each named Audit the source was the only source file in its own clean directory and the compiled imports were production-only: `LEAN_PATH=<production-only-cache> lean --trust=0 -DwarningAsError=true <name>.lean`. Official Lean 4.35.0. Existing bounded 182 dependency sources matched immutable `0512c698732a0aeeb444f869f586bccc0a15866d` and were independently built. No overall Lake build, repository-wide script, Rust or human-supervisor gate ran in this lane.

For the second independent readback, exactly the 10 public Git source bodies were passed one per process as `LEAN_PATH=<production-only-cache> lean --trust=0 -DwarningAsError=true --stdin`. They all exited 0; source paths, hashes, and full Audit diagnostics below. The old Audit/README content was not read; IDs and all existing production/audit tree entries remained unchanged, old barrel exact bytes + five imports. Source-policy and changed-path checks applied separately, not represented as a claim that `tools/verify-lean.sh` ran.

## Exact publication replay

```text
lean/Yulang/GeneralDeclarativeI65I74CompletedLowerRule438.lean 902883eb9c68410213bd78895e9b76d0981e859d exit 0

lean/Audit/Cycle438I74CompletedLowerRule.lean 2888117b722c0eeca21d737001520ffed9a43534 exit 0
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.completed_head_has_literal_original_meaning438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.completed_selected_evidence438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.dictionary_sound_of_prior438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.raw_root_K2_has_priority438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

lean/Yulang/GeneralDeclarativeI65I74CompletedLowerPorts438.lean deebced65525ccf7854348ca0ba3255c435a5782 exit 0

lean/Audit/Cycle438I74CompletedLowerPorts.lean 10af2732f70684d435b7ae506bdb7faddd93bc74 exit 0
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.readSingleton438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.readSeedBasis438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.readTypedUnary438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.readGate438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.checked_gate_cannot_use_wrong_target438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.checked_gate_uses_independent_authored_upper438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

lean/Yulang/GeneralDeclarativeI65I74CompletedLowerReplay438.lean 8e92685d4456c0b1e485ce0b8656d2141475b3b6 exit 0

lean/Yulang/GeneralDeclarativeI65I74CompletedLowerEntry438.lean e528002702a3e75a3d72fda55e08e10632ad07db exit 0

lean/Audit/Cycle438I74CompletedLowerEntry.lean b319b37da730ea1b5e96d241eeb9d28b732a0109 exit 0
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.replaySeed438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.replay438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.replay_completed_keeps_exact_original_addresses438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.dictionary_sound_R18' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.previous_R17_entry_is_unchanged438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.checked_completed_reads_exact_report438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.check_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.verified_R18_result_classifies_in_same_State438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.real_raw_K2_refuses_completed_witness438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

lean/Audit/Cycle438I74CompletedLowerEndToEnd.lean a45334fc6abc41bfd7b016d4781b67bdd16e1401 exit 0
'Yulang.C438CompletedEntryAudit.public_entry_accepts_original_completed_lower438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C438CompletedEntryAudit.checked_public_path_is_same_B6_source_and_selected_root438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C438CompletedEntryAudit.public_entry_checks_wrong_fixed_row_center_and_request438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C438CompletedEntryAudit.original_report_does_not_reissue_producer_or_change_dictionary438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C438CompletedEntryAudit.exact_raw_K2_still_enters_in_original_public_branch438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C438CompletedEntryAudit.actual_lower_has_no_independent_authored_route438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C438CompletedEntryAudit.public_completed_report_has_one_model_without_authored_lower438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

lean/Yulang/GeneralDeclarativeI65I74CompletedLowerSameModel438.lean dc3e7210153dc41f19a7a6eb1800672a9780d0da exit 0

lean/Audit/Cycle438I74CompletedLowerSameModel.lean f1990d179a21bc6ba08ff97967add7a66119236a exit 0
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.actual_producer_and_consumer_share_one_model438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.checked_completed_has_original_same_model_dictionary438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

```

## Additional controls, strict stdin only

These are reproducible additions to verification, **not imported or registered Lean production/Audit modules**. Each ran with the same 4.35 strict flags and production-only imports, exit 0, only the standard three axioms. Coverage count rests on the separately compiled/audited five plus five files above, not on these add-ons.

1. If the actual producer's typed B6 read is absent at every original declaration/output/body address, no amount of retained ordinary equations allows either Seed replay or the new check. This does not claim any language diagnosis on absence.
2. Two **new-lane** accepted witnesses for the same Problem necessarily have the same exact report, since the whole visible list independently yields a singleton. Not a cross-lane confluence, completeness or solver claim.
3. Concrete same-raw-rows/contents and same fitting model, but atlas derives no plan: source replay and completed check both false. Adding the consumer-root raw cycle instead, with the real typed atlas present: the independently selected exact Seed still replays, the consumer new positive fails, and the original raw rejection still passes.

For 1 and 2, run each snippet separately under the same strict stdin command. For 3, append the suffix below only to the input stream of the original EndToEnd Audit path at the technology pin.

### 1: No original typed plan

```lean
import Yulang.GeneralDeclarativeI65I74CompletedLowerEntry438

namespace Yulang.GeneralDeclarativeI65.I72.CompletedEntry438
open GeneralDeclarativeI65
open Checker408 (Problem Result)

theorem any_retained_rows_without_original_B6_do_not_replay_seed438
    {s : I72.State} {w : Wire438}
    (lack : ∀ d i body, s.b6.read w.producer d i body = none) :
    replaySeed438 s w = none := by
  cases replaySeed438 s w with
  | none => rfl
  | some seed =>
    let out := seed.outputs seed.read.i
    have denied := lack seed.basis.frame.ordinal seed.read.i out.body
    have seen := out.originalTyped
    rw [denied] at seen
    cases seen

theorem public_completed_witness_cannot_invent_typed_B6_438
    (p : Problem) (r : Result) (w : Wire438)
    (lack : ∀ d i body, p.state.b6.read w.producer d i body = none) :
    check p r (.completedLower w) = false := by
  cases good : check p r (.completedLower w) with
  | false => rfl
  | true =>
    obtain ⟨read,_,_⟩ := checked_completed_reads_exact_report438 good
    let chosen := read.selected.invocation.chosen
    let sourceRequest := chosen.need.producer
    let actual := chosen.producer
    let out := actual.event.outputs chosen.need.ordinal
    have matchRequest : w.producer = sourceRequest := read.producer.symm
    have hi : ∀ d i body, p.state.b6.read sourceRequest d i body = none :=
      Eq.ndrec (motive := fun req => ∀ d i body, p.state.b6.read req d i body = none)
        lack matchRequest
    have denied := hi actual.event.frame.ordinal chosen.need.ordinal out.body
    have seen := out.originalTyped
    rw [denied] at seen
    cases seen

end Yulang.GeneralDeclarativeI65.I72.CompletedEntry438

open Yulang.GeneralDeclarativeI65.I72.CompletedEntry438
#print axioms any_retained_rows_without_original_B6_do_not_replay_seed438
#print axioms public_completed_witness_cannot_invent_typed_B6_438
```

### 2: Exact same-branch reports

```lean
import Yulang.GeneralDeclarativeI65I74CompletedLowerEntry438

namespace Yulang.GeneralDeclarativeI65.I72.CompletedEntry438
open GeneralDeclarativeI65
open Checker408 (Problem Result)

/-- Two valid completions may carry different literal supports. They
cannot choose different visible classes or change writes on the
same one-candidate consumer. This is a new/new assertion, not a
claim of global confluence or of existence of either witness. -/
theorem two_completed_source_proofs_have_one_exact_report438 {s q}
    (a b : Selected18 s q) : a.report = b.report := by
  have same : a.invocation.row = b.invocation.row :=
    (List.cons.inj
      (a.invocation.chosen.gate.only.symm.trans b.invocation.chosen.gate.only)).1
  simp only [Selected18.report,Selected18.dictionary,same]

theorem accepted_completed_reports_are_unique438 (p : Problem) (x y : Result)
    (a b : Wire438) (first : check p x (.completedLower a) = true)
    (second : check p y (.completedLower b) = true) : x = y := by
  obtain ⟨left,_,readLeft⟩ := checked_completed_reads_exact_report438 first
  obtain ⟨right,_,readRight⟩ := checked_completed_reads_exact_report438 second
  exact readLeft.trans ((two_completed_source_proofs_have_one_exact_report438
    left.selected right.selected).trans readRight.symm)

end Yulang.GeneralDeclarativeI65.I72.CompletedEntry438

open Yulang.GeneralDeclarativeI65.I72.CompletedEntry438
#print axioms two_completed_source_proofs_have_one_exact_report438
#print axioms accepted_completed_reports_are_unique438
```

### 3: Exact fixture suffix

```lean
namespace Yulang.C438CompletedEntryAudit
open GeneralDeclarativeI65
open GeneralDeclarativeI65.I72
open GeneralDeclarativeI65.I72.CompletedEntry438
open Checker408 (Problem)

def missingPlanState : I72.State :=
  ⟨core, ⟨fun _ _ _ _ => none⟩⟩

/-- Exactly the same ordinary rows, source book, origins and fitting
model. The solver's stored equation is not enough to select the
producer when the actual original B6 occurrence is unavailable. -/
theorem retained_row_alone_is_not_a_completed_B6_source438 :
    I72.Fits missingPlanState sample ∧
    missingPlanState.core.current.ordinary.equations[0]? = some output0 ∧
    (replaySeed438 missingPlanState wire).isSome = false ∧
    check ⟨missingPlanState,query⟩ desired (.completedLower wire) = false := by
  refine ⟨original_fixture_fits438,rfl,?_⟩
  decide +kernel

theorem same_seed_still_replays_when_only_consumer_has_raw_K2438 :
    (replaySeed438 certifiedRawProblem.state wire).isSome = true ∧
    check certifiedRawProblem desired (.completedLower wire) = false ∧
    check certifiedRawProblem Check408.rawReport originalRawWitness = true := by
  decide +kernel

#print axioms retained_row_alone_is_not_a_completed_B6_source438
#print axioms same_seed_still_replays_when_only_consumer_has_raw_K2438
end Yulang.C438CompletedEntryAudit
```

Supplementary process output (first two and the two new axioms of the fixture):
```text
no typed authority exit 0
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.any_retained_rows_without_original_B6_do_not_replay_seed438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.public_completed_witness_cannot_invent_typed_B6_438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

within-lane result uniqueness exit 0
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.two_completed_source_proofs_have_one_exact_report438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.accepted_completed_reports_are_unique438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

counterfactual real fixture exit 0
'Yulang.C438CompletedEntryAudit.retained_row_alone_is_not_a_completed_B6_source438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C438CompletedEntryAudit.same_seed_still_replays_when_only_consumer_has_raw_K2438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

```

## Extra runtime and scope readback

The exact EndToEnd input stream can also evaluate the public Bool directly (the addition is **not** in the Audit source; no production metaprogramming). A fourth and fifth result on the reconstructed raw-cycle State distinguish the new and previous branches:

```lean
open Yulang.C438CompletedEntryAudit
open Yulang.GeneralDeclarativeI65.I72 Yulang.GeneralDeclarativeI65.I72.CompletedEntry438
#eval [check problem desired (.completedLower wire),
  check problem desired (.completedLower {wire with seedRetainedRow := 1}),
  check problem desired (.completedLower {wire with centerOrigin := 3}),
  check certifiedRawProblem desired (.completedLower wire),
  check certifiedRawProblem Check408.rawReport originalRawWitness]
```

Output under the same Lean 4.35 strict stdin command: `[true, false, false, false, true]`, exit 0.

One more independent strict stdin control checks, for every accepted new report, that no where requests or actual output can be hidden by the empty report (the exact `WhereForest` is empty) and that the seed frame reads the selected book declaration and original B6 plan at its own ordinal, not a coincident body:

```lean
import Yulang.GeneralDeclarativeI65I74CompletedLowerEntry438
import Yulang.GeneralDeclarativeI65I74CompletedLowerSameModel438

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.CompletedEntry438
open GeneralDeclarativeI65
open Checker408 (Problem Result)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

private theorem where_forest_empty_tree_has_no_requests438
    {s : I72.State} {requests}
    (f : WhereForest PriorSource406 s requests []) :
    requests = [] := by
  cases f
  rfl

theorem exact_completed_report_has_no_hidden_children_or_writes438
    (p : Problem) (r : Result) (w : Wire438)
    (yes : check p r (.completedLower w) = true) :
    ∃ a : Replay438 p.state p.root w,
      r = a.selected.report ∧ a.selected.invocation.kids = [] ∧ p.root.demand.outputs = [] ∧ r.writes = [] := by
  obtain ⟨a,_,same⟩ := checked_completed_reads_exact_report438 yes
  exact ⟨a,same,where_forest_empty_tree_has_no_requests438 a.selected.invocation.children,
    a.noOutputs,congrArg (fun r : Result => r.writes) same⟩

theorem exact_seed_frame_reads_selected_visible_declaration_and_literal_B6438
    {s q ordinal} (a : SeedReplay438 s q ordinal) :
    (authoredRegistry s.core.current).declarations[a.basis.frame.ordinal]? = some a.row ∧
    s.b6.read q a.basis.frame.ordinal a.read.i (a.outputs a.read.i).body =
      some (a.outputs a.read.i).plan ∧
    a.read.kept.payload.rowOrdinal = ordinal :=
  ⟨a.basis.inRegistry,(a.outputs a.read.i).originalTyped,a.exactRow⟩

#print axioms exact_completed_report_has_no_hidden_children_or_writes438
#print axioms exact_seed_frame_reads_selected_visible_declaration_and_literal_B6438
end Yulang.GeneralDeclarativeI65.I72.CompletedEntry438
```

```text
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.exact_completed_report_has_no_hidden_children_or_writes438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.exact_seed_frame_reads_selected_visible_declaration_and_literal_B6438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Original declaration address vs identical retained rows

Two modest extra controls, again only in the stdin stream of the original EndToEnd Audit. The original typed plan moved to declaration ordinal 1 is present at that address and absent at original declaration ordinal 0; the public check is false even though raw rows and source book stay the same. Conversely, adding another literally identical retained row for the same actual typed output lets either exact address pass with the same result; it is the wrongly encoded decoy row that still fails. Neither control says the physical row of an original declared output is globally unique. The actual source declaration/output occurrence is never moved.

```lean
namespace Yulang.C438CompletedEntryAudit
open GeneralDeclarativeI65
open GeneralDeclarativeI65.I72
open GeneralDeclarativeI65.I72.CompletedEntry438
open Checker408 (Problem)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeOutputs320 (bodyPattern)

def swappedDeclarationAtlas : B6OccurrenceAtlas401 core :=
  ⟨fun q d i b => atlas.read q (if d = 1 then 0 else 1) i b⟩

def wrongDeclarationProblem : Problem := ⟨⟨core,swappedDeclarationAtlas⟩,query⟩

theorem same_typed_B6_at_wrong_decl_is_not_original438 :
    swappedDeclarationAtlas.read seedRequest 1 seedIndex originalBody = some originalPlan ∧
    swappedDeclarationAtlas.read seedRequest 0 seedIndex originalBody = none ∧
    check wrongDeclarationProblem desired (.completedLower wire) = false := by
  refine ⟨rfl,rfl,?_⟩
  decide +kernel

def duplicateRaw : GeneralDeclarativeHead320.State :=
  {raw with equations := raw.equations ++ [output0]}

def duplicatedCore : GeneralDeclarativeI65.State :=
  { core with current := { core.current with ordinary := duplicateRaw } }

def duplicatePlan : B6MixedRhs401 duplicatedCore false (normalize (bodyPattern originalBody)) :=
  .declaredApp (params := [coValue]) 20 mode (by decide +kernel) (by decide +kernel)
    (.cons (.valuePoint 8 rfl (by decide +kernel) ()) .nil)

def duplicatedAtlas : B6OccurrenceAtlas401 duplicatedCore :=
  ⟨fun q d i b =>
    match q.demand.arguments, q.demand.outputs with
    | [a],[o] =>
      if q.occurrence = [101] ∧ q.demand.role = 11 ∧ a.lower = 10 ∧ a.center = 10 ∧ a.upper = 10 ∧
          o.name = 6 ∧ o.target = 40 ∧ d = 0 ∧ i.val = 0 then
        if source : b = originalBody then some (source.symm ▸ duplicatePlan) else none
      else none
    | _,_ => none⟩

def duplicatedReceiptProblem : Problem := ⟨⟨duplicatedCore,duplicatedAtlas⟩,query⟩

theorem literal_duplicate_row_can_be_read_without_changing_report438 :
    check duplicatedReceiptProblem desired (.completedLower wire) = true ∧
    check duplicatedReceiptProblem desired (.completedLower { wire with seedRetainedRow := 2 }) = true ∧
    check duplicatedReceiptProblem desired (.completedLower { wire with seedRetainedRow := 1 }) = false := by
  decide +kernel

#print axioms same_typed_B6_at_wrong_decl_is_not_original438
#print axioms literal_duplicate_row_can_be_read_without_changing_report438
end Yulang.C438CompletedEntryAudit
```

```text
'Yulang.C438CompletedEntryAudit.same_typed_B6_at_wrong_decl_is_not_original438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C438CompletedEntryAudit.literal_duplicate_row_can_be_read_without_changing_report438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

```

## The same lower name in one fitting model

If two independently derived new selections for the same original demand use different literal producer receipts, their values are equivalent in any one fitting model: both receipts interpret that request's same original lower target. This is after selection, and does **not** replace any source, choose one receipt from semantics, or imply identical names. The following isolated strict stdin run passed using the exact published production import only.

```lean
import Yulang.GeneralDeclarativeI65I74CompletedLowerEntry438

namespace Yulang.GeneralDeclarativeI65.I72.CompletedEntry438
open GeneralDeclarativeI65
open Checker408 (Problem Result)
open CommonNominalFullCarrier (Ty Equivalent subtype_trans)

/-- An equality of meanings after both separately justified
selections, not permission to use the other source's ordinal or
infer a second selected event. Distinct payload names are allowed. -/
theorem public_two_literal_completions_agree_in_one_model438
    {s q} (a b : Selected18 s q) (m : I72.Model) (fit : Fits s m) :
    ∃ lo hi : Ty,
      let outA := a.invocation.chosen.producer.event.outputs a.invocation.chosen.need.ordinal
      let outB := b.invocation.chosen.producer.event.outputs b.invocation.chosen.need.ordinal
      outA.receipt.actualEquation m = some (a.invocation.chosen.gate.arg.lower,lo) ∧
      outB.receipt.actualEquation m = some (b.invocation.chosen.gate.arg.lower,hi) ∧
      Equivalent lo hi := by
  obtain ⟨lo,_,_,first,leftValue⟩ := completed_head_has_literal_original_meaning438 a.head m fit
  obtain ⟨hi,_,_,second,rightValue⟩ := completed_head_has_literal_original_meaning438 b.head m fit
  have same := congrArg GeneralDeclarativeWhere319.Capture.lower
    (List.cons.inj (a.invocation.chosen.gate.exactArg.symm.trans b.invocation.chosen.gate.exactArg)).1
  rw [← same] at rightValue
  exact ⟨lo,hi,first,second,subtype_trans leftValue.2 rightValue.1,subtype_trans rightValue.2 leftValue.1⟩

#print axioms public_two_literal_completions_agree_in_one_model438
end Yulang.GeneralDeclarativeI65.I72.CompletedEntry438
```

```text
'Yulang.GeneralDeclarativeI65.I72.CompletedEntry438.public_two_literal_completions_agree_in_one_model438' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
