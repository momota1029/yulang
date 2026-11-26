# C439 verification of immutable source, runtime, and controls

The completed-science work pin is `b13e03bb1f21fd33bd8153365eea811cc3ea286b`, Lean `3fa551ff461d24ab106f9dca1f55cdefd742b49e`. Existing 7,670 Yulang and 2,055 Audit entries all unchanged; the frozen root Audit/README were checked by blob ID only. The exact old barrel is a byte prefix followed by five imports. New production source and Audit import names were also checked, with no peer Audit import. Total publicly audited declarations: 33.

Official Lean: 4.35.0 (eb6cafb7290e8bd5f2937522d8d804f58f02bafc). Separate physical production command for each of the five new modules: `LEAN_PATH=<verified-production-only> lean --trust=0 -DwarningAsError=true -o <work>/Yulang/<module>.olean <module>.lean`. Each of the six Audits ran as the only source checked from its own clean working directory, using only those production oleans and the proven pre-existing cache. All exit 0. The same Git-fetched bytes (not a new variant with weaker flags) were independently rebuilt. No full Lake, supervisor `verify-lean.sh`, or Rust was run. The existing cache dependencies were checked against the exact authoritative source bytes, not globally rebuilt.

## Independent exact public bytes and all Audit diagnostics

Below: exact Git blob, then the individual ordinary `LEAN_PATH=<verified-production-only> lean --trust=0 -DwarningAsError=true --stdin` readback for that blob.

```text
lean/Yulang/GeneralDeclarativeI65I74MergedOutputSource439.lean 59d54225daeee48cc6d7a2ae148d1729289ca3a9 exit 0

lean/Audit/Cycle439I74MergedOutputSource.lean c6ef50466f22dbe374b1b5fac94652e0ac207e82 exit 0
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.report_summarizes_merged_rejection439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.same_unnamed_inputs_on_original_children439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.literal_forest_cannot_shorten_to_merged_child439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.producer_rows_give_separate_meanings_and_merge_conflicts439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.no_fitting_extension_equalizes_the_named_output439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.source_codes_and_compiler_rows439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

lean/Yulang/GeneralDeclarativeI65I74MergedOutputHeader439.lean 183169a168adab95c7b03c1d5ca8652b65e5b709 exit 0

lean/Audit/Cycle439I74MergedOutputHeader.lean a6316682ca4b95399e99440a329f9b4e0be44926 exit 0
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.closed_nullary_descent_sound439' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.checks_declaration_sound439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.checked_header439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

lean/Yulang/GeneralDeclarativeI65I74MergedOutputRead439.lean f1c41c6bd50ee2b19fb452eda81bb0264fb93839 exit 0

lean/Audit/Cycle439I74MergedOutputRead.lean ba155bfd2f9a49762df149891779ae3d28330277 exit 0
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.print_request_injective439' depends on axioms: [propext]
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.request_list_eq439' depends on axioms: [propext]
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.replay439' depends on axioms: [propext, Classical.choice, Quot.sound]

lean/Yulang/GeneralDeclarativeI65I74MergedOutputEntry439.lean 1548de70fecb83448e273cb49e7f199d432b774e exit 0

lean/Audit/Cycle439I74MergedOutputEntry.lean 47249609bf3442d61398775be915bf5ca488494d exit 0
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.dictionary_sound_R19' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.every_previous_R18_Bool_is_unchanged439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.checked_merged_replay_matches_exact_tree439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.check_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.verified_R19_result_classifies_in_same_State439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.original_raw_root_K2_distinct_from_merged_rejection439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.actual_visible_rival_prevents_new_conflict_report439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

lean/Audit/Cycle439I74MergedOutputEndToEnd.lean e57ee538b8cd0717a0bbee248bdf0b485bfae3ac exit 0
'Yulang.C439MergedAudit.actual_old_raw_K2_still_uses_its_own_location439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C439MergedAudit.literal_int_raw_rows_do_not_supply_nonint_source439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C439MergedAudit.scoped_header_recognizes_actual_closed_nullary_child439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C439MergedAudit.real_public_check_rejects_only_at_the_merged_child439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C439MergedAudit.actual_compiler_child_and_report_addresses439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C439MergedAudit.original_separate_output_cells_have_a_real_model439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C439MergedAudit.tested_public_report_is_supported_and_only_merging_is_impossible439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C439MergedAudit.actual_rival_and_different_name_not_this_conflict439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C439MergedAudit.original_child_location_cannot_be_replaced_or_duplicated439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

lean/Yulang/GeneralDeclarativeI65I74MergedOutputEquation439.lean 97e9d81ee853c96bfbfcbae0d29c9d95e9e07265 exit 0

lean/Audit/Cycle439I74MergedOutputEquation.lean 45ad3f506ee6b623644b83f19b84abdaad963f45 exit 0
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.sites_project_exact_ordered_requests439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.emitted_nullary_sites_have_same_inputs439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.emitted_merge_equations_are_exact439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.actual_output_merge_atoms_mean_same_named_equation439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.accepted_merged_report_rules_out_old_operation_atoms439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

```

## Direct executable C19 entry

To the exact Git-pinned `lean/Audit/Cycle439I74MergedOutputEndToEnd.lean` input stream only, append this runtime diagnostic. Do not append it to the published Lean source.

```lean
open Yulang.C439MergedAudit
open Yulang.GeneralDeclarativeI65.I72
open Yulang.GeneralDeclarativeI65.I72.MergedOutput439
#eval [check problem expected (.mergedOutput witness),
  check problem Check408.rawReport (.mergedOutput witness),
  check problem ⟨.selected 37 [.rejected,.rejected],.rejected,[]⟩ (.mergedOutput witness),
  check problem ⟨.selected 99 [.rejected],.rejected,[]⟩ (.mergedOutput witness),
  check problem expected (.mergedOutput {witness with originalInput := 1}),
  check withRival expected (.mergedOutput witness),
  check withRenamed expected (.mergedOutput witness),
  check wronglyReusedParentCell expected (.mergedOutput witness),
  check wrongCoreTranslation expected (.mergedOutput witness),
  check actualRawCycle expected (.mergedOutput witness),
  check actualRawCycle Check408.rawReport oldRawRoot,
  check problem Check408.rawReport oldRawRoot]
```

Output: `[true, false, false, false, false, false, false, false, false, false, true, false]`, exit 0. Thus the actual merged-child report passed. Root-only, duplicated children, wrong parent, wrong issuer at same slot, actual valid rival, different associated name, aliasing input/output cell, and constructor metadata inconsistent with the ordinary int rows failed. On the actual cyclic State only the old raw-root report passed; on the original noncyclic case the old raw-root report did not pass.

## Additional proof controls (not public Lean module changes)

Each following suffix was appended to the exact end-to-end Audit **input stream separately** under the same strict 4.35 flags. Both passed, and each additional axiom output used only the standard trio. The true rival proof keeps both candidate heads as actual live matches of the source-based tape; the negative check is not attributable to an invalid declaration. The compatible case changes the actual original last authored request and retained row to int, verifies a genuine fitting model equates both output cells, and still gets no conflict report. Neither claims the general checker generates an ambiguity/selection witness.

```lean
namespace Yulang.C439MergedAudit
open GeneralDeclarativeI65 GeneralDeclarativeI65.I72.MergedOutput439
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)

def mergedChildRequest : GeneralDeclarativeI65.Request :=
  ⟨[7,0],⟨1,[],[⟨0,1⟩,⟨0,2⟩]⟩⟩

private def actualNullaryCandidate (d : Declaration)
    (atBook : d ∈ (authoredRegistry withRival.state.core.current).declarations)
    (inScope : d ∈ visible withRival.state.core mergedChildRequest)
    (nullary : d.head = []) :
    AuthoredCandidate withRival.state.core mergedChildRequest d := by
  have both := checked_header439 (s := withRival.state.core.current) (by decide +kernel)
  have sourceHead : SourceHead withRival.state.core mergedChildRequest d := by
    refine .ordered (fun _ => point 0) ?_
    rw [nullary]
    exact .nil
  exact ⟨inScope,both.2.1 d atBook,(both.1.2 d atBook).signature,sourceHead⟩

def actualChildAndRival : CandidateTape withRival.state.core mergedChildRequest
    (visible withRival.state.core mergedChildRequest) := by
  have exactTape : visible withRival.state.core mergedChildRequest = [child,rival] := by decide +kernel
  let first := actualNullaryCandidate child (by decide +kernel) (by decide +kernel) rfl
  let last := actualNullaryCandidate rival (by decide +kernel) (by decide +kernel) rfl
  exact exactTape.symm ▸ .next (.matched first) (.next (.matched last) .nil)

theorem actual_full_tape_keeps_both_nullary_candidate_heads439 :
    actualChildAndRival.live = [child,rival] ∧
    actualChildAndRival.waits = false ∧
    ∀ d, ¬ TapedMatch withRival.state.core mergedChildRequest actualChildAndRival d := by
  have live : actualChildAndRival.live = [child,rival] := by decide +kernel
  refine ⟨live,by decide +kernel,?_⟩
  intro d wronglySelected
  have shorter := wronglySelected.one
  rw [live] at shorter
  have count := congrArg List.length shorter
  cases count

#print axioms actual_full_tape_keeps_both_nullary_candidate_heads439
end Yulang.C439MergedAudit
```
```text
Classical.choice,
 Quot.sound]
```

```lean
namespace Yulang.C439MergedAudit
open GeneralDeclarativeI65
open GeneralDeclarativeI65.I72.MergedOutput439
open CommonNominalFullCarrier (Equivalent subtype_refl)
open GeneralDeclarations (Clause Declaration)
open GeneralDeclarativeI65.I72
open GeneralDeclarativeI65.I72.Checker408 (Problem Result)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)

def compatibleTail : Clause :=
  {GeneralNominalCenteredHeadAllocMergeSource.lastClause with outputs := [⟨43,0,.app 2 []⟩]}

def compatibleParent : Declaration :=
  {parent with requirements :=
    [GeneralNominalCenteredHeadAllocMergeSource.firstClause,compatibleTail]}

def compatibleEnv : Environment := (env? [compatibleParent,child]).get (by decide +kernel)

def compatibleRaw : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[⟨0,intCode⟩,⟨1,intCode⟩,⟨2,intCode⟩]⟩

def compatibleProblem : Problem :=
  ⟨state (core compatibleEnv compatibleRaw),request⟩

def allInt : GeneralDeclarativeI65.Model :=
  ⟨fun _ => (.base .int,Common.rowEmpty),fun _ => none,
    fun n => if n = 0 then some (.ordinary (.base .int)) else none⟩

theorem real_compatible_sources_do_not_get_a_false_conflict439 :
    I72.Fits compatibleProblem.state allInt ∧
    Equivalent (allInt.assignment 1).1 (allInt.assignment 2).1 ∧
    checkHeader439 compatibleEnv = true ∧
    check compatibleProblem expected (.mergedOutput witness) = false := by
  refine ⟨?_,⟨subtype_refl _,subtype_refl _⟩,by decide +kernel,by decide +kernel⟩
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro x h; change x ∈ [] at h; cases h
  · intro x h; change x ∈ [] at h; cases h
  · intro e h
    change e ∈ [⟨0,intCode⟩,⟨1,intCode⟩,⟨2,intCode⟩] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
  · intro x h; change x ∈ [] at h; cases h
  · intro x h
    change x ∈ [origin,otherIssuer] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;> rfl

#print axioms real_compatible_sources_do_not_get_a_false_conflict439
end Yulang.C439MergedAudit
```
```text
Classical.choice,
 Quot.sound]
```

## Semantic controls for exact source parameters and equalities

The following independent strict checks are reproducible from the same published production objects. They add no proof premises, public audits, or accepted shape. First check the standalone source below; it proves the original nullary compiler demands are unchanged if we choose arbitrary fallback capture and compound-argument table. Those parameters are genuinely unused for closed literal output equations and no unnamed inputs.

```lean
import Yulang.GeneralDeclarativeI65I74MergedOutputEquation439
namespace Yulang.GeneralDeclarativeI65.I72.MergedOutput439
open GeneralDeclarativeI65
open GeneralDeclarativeWhere319 (Capture)

theorem closed_where_demands_ignore_the_fallback_capture439 {s q} (a : Original439 s q)
    (unused : Nat → Capture) (compound : GeneralDeclarations.Clause → Nat → Capture) :
    frameWhereKids400 {a.frame with input := unused, placement := {a.frame.placement with compound := compound}} = frameWhereKids400 a.frame := by
  simp [frameWhereKids400,AuthoredBodyFrame393.clauses,AuthoredBodyFrame393.whereFor,
    a.originalClauses,GeneralDeclarativeSourceEmission322.demand,GeneralDeclarativeSourceEmission322.inputs,
    GeneralDeclarativeSourceEmission322.useOutput,GeneralDeclarationDemands.outputTarget,
    a.firstArgs,a.lastArgs,a.firstOutput,a.lastOutput,a.firstRhs,a.lastRhs,
    GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.normalizeArgs]

#print axioms closed_where_demands_ignore_the_fallback_capture439
end Yulang.GeneralDeclarativeI65.I72.MergedOutput439
```
```text
'Yulang.GeneralDeclarativeI65.I72.MergedOutput439.closed_where_demands_ignore_the_fallback_capture439' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The next suffix uses the exact EndToEnd Audit, with its Entry import replaced in the input stream by the published Equation module (which imports it). It verifies the actual two atoms are the two directions between the two original cells 1 and 2. The last suffix uses the exact unmodified EndToEnd Audit import set and verifies that with actually distinct authored associated names, the two literal source demands still exist but the established merger emits no equality. Those controls are not substitutes for the original branch's pre-merge fitting model or all-model negative proof.

```lean
namespace Yulang.C439MergedAudit
open GeneralDeclarativeI65.I72.MergedOutput439
open GeneralNominalDemandMerging (outputAtoms)
open PresenceNormalForm (Atom)

theorem actual_pinned_conflict_emits_both_directions_at_original_cells439 :
    outputAtoms (projectNullarySite439 original true) (projectNullarySite439 original false) =
      [Atom.tyLe (.var 1) (.var 2),Atom.tyLe (.var 2) (.var 1)] := by
  rw [emitted_merge_equations_are_exact439]
  decide +kernel

#print axioms actual_pinned_conflict_emits_both_directions_at_original_cells439
end Yulang.C439MergedAudit
```
```text
Classical.choice,
 Quot.sound]
```

```lean
namespace Yulang.C439MergedAudit
open GeneralDeclarativeI65
open GeneralDeclarativeI65.I72
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralNominalDemandMerging (Site outputAtoms)

def namesControlFrame : AuthoredBodyFrame393 withRenamed.state.core request :=
  frameAtSource395 (row := renamedParent) (by decide +kernel) 0 (by decide +kernel)
    ⟨fun _ _ => point 0,fun c _ => if c.id = 42 then 1 else 2⟩ (fun _ => point 0)

abbrev namesControlRoles := (authoredRegistry withRenamed.state.core.current).roles

def leftDifferent : Site namesControlRoles :=
  ⟨⟨42,⟨1,fun _ => (0,0),[⟨0,1⟩], by
    intro output position
    obtain rfl := List.mem_singleton.mp position
    exact ⟨none,rfl⟩⟩⟩,[],rfl⟩

def rightDifferent : Site namesControlRoles :=
  ⟨⟨44,⟨1,fun _ => (0,0),[⟨1,2⟩], by
    intro output position
    obtain rfl := List.mem_singleton.mp position
    exact ⟨none,rfl⟩⟩⟩,[],rfl⟩

theorem distinct_authored_named_outputs_emit_no_equality439 :
    frameWhereKids400 namesControlFrame =
      [⟨[7,0],⟨1,[],leftDifferent.occurrence.demand.outputs⟩⟩,
       ⟨[7,1],⟨1,[],rightDifferent.occurrence.demand.outputs⟩⟩] ∧
    outputAtoms leftDifferent rightDifferent = [] :=
  ⟨rfl,by decide +kernel⟩

#print axioms distinct_authored_named_outputs_emit_no_equality439
end Yulang.C439MergedAudit
```
```text
Classical.choice,
 Quot.sound]
```
