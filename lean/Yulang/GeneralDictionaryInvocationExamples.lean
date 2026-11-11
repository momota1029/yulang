import Yulang.GeneralDictionaryPlanLookupExamples

/-!
# Repeated implementation keys at distinct source invocations

The checked Wrap declaration is reused with two supplied captures. Pointwise
frames retain distinct ordinary source endpoints and named output targets.
The negative regression shows why one declaration-indexed frame cannot express
both instances. Nothing here derives captures, allocates fresh IDs, or decides
whether revisiting one source obligation must retain its local binders.
-/
namespace Yulang.GeneralDictionaryInvocationExamples
open GeneralDeclarations GeneralDeclarationDemands GeneralDeclarationExamples
open GeneralSourceDictionaries GeneralDictionaryEmissionPlans GeneralDictionaryPlanLookup
open GeneralCanonicalChildOrder

abbrev first : Occurrence roles := GeneralDictionaryEmissionPlanExamples.root
abbrev second : Occurrence roles :=
  ⟨10, { GeneralDictionaryEmissionPlanExamples.rootDemand with arguments := fun _ => (50, 51) }⟩

abbrev firstCapture : Capture := ⟨fun _ => (100, 101), fun _ => 200⟩
abbrev secondCapture : Capture := ⟨fun _ => (500, 501), fun _ => 600⟩

/-- Selection is by an already supplied source occurrence, not declaration key.
The identity expression is an example only, not a claimed fresh allocator. -/
abbrev frames (root : Occurrence roles) : Frame roles where
  capture := fun _ => if root.identity = 9 then firstCapture else secondCapture
  allocation := fun _ _ => ⟨fun _ => (300, 301), fun _ => 400⟩
  identity := fun invocation _ clause => invocation * 100 + clause

abbrev firstDemand := childDemand wrap containerChild
  (wrap_checked.signature.2.2.2 containerChild (by simp)) firstCapture wrapAllocation
abbrev secondDemand := childDemand wrap containerChild
  (wrap_checked.signature.2.2.2 containerChild (by simp)) secondCapture wrapAllocation

private theorem wrap_children (frame : Frame roles) (root : Occurrence roles) :
    children frame root wrap wrap_checked =
      [⟨frame.identity root.identity wrap.id containerChild.id,
        childDemand wrap containerChild (wrap_checked.signature.2.2.2 containerChild (by simp))
          (frame.capture wrap.id) (frame.allocation wrap.id containerChild)⟩] := by
  have original : emitAll root.identity wrap wrap_checked.signature
      (frame.capture wrap.id) (frame.allocation wrap.id) =
      [emit root.identity wrap containerChild (wrap_checked.signature.2.2.2 containerChild (by simp))
        (frame.capture wrap.id) (frame.allocation wrap.id containerChild)] := rfl
  have permuted := canonicalEmit_perm root.identity wrap wrap_checked
    (frame.capture wrap.id) (frame.allocation wrap.id)
  rw [original] at permuted
  have canonical := permuted.symm.eq_singleton
  unfold children
  rw [canonical]
  rfl

theorem first_children : children (frames first) first wrap wrap_checked = [⟨920, firstDemand⟩] := by
  rw [wrap_children]
  rfl

theorem second_children : children (frames second) second wrap wrap_checked = [⟨1020, secondDemand⟩] := by
  rw [wrap_children]
  rfl

/-- Input endpoints and output targets belong to separate invocations, despite
selecting exactly the same checked declaration ID. -/
theorem actual_distinct_source_demands :
    firstDemand.arguments ⟨0, by decide⟩ = (100, 101) ∧
    firstDemand.outputs = [⟨1, 200⟩] ∧
    secondDemand.arguments ⟨0, by decide⟩ = (500, 501) ∧
    secondDemand.outputs = [⟨1, 600⟩] :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem first_lookup : lookup registry registry_checked (frames first) first 2 =
    some [⟨920, firstDemand⟩] := by
  apply (lookup_exact registry registry_checked (frames first) first 2 _).mpr
  rw [← first_children]
  exact visible_plan registry registry_checked (frames first) first wrap (by simp) rfl

theorem second_lookup : lookup registry registry_checked (frames second) second 2 =
    some [⟨1020, secondDemand⟩] := by
  apply (lookup_exact registry registry_checked (frames second) second 2 _).mpr
  rw [← second_children]
  exact visible_plan registry registry_checked (frames second) second wrap (by simp) rfl

/-- In a fixed frame, changing the source invocation cannot change these child
outputs. The invocation enters identity metadata, not capture or allocation. -/
theorem fixed_frame_outputs (frame : Frame roles) (one two : Occurrence roles) :
    (children frame one wrap wrap_checked).map (fun child => child.demand.outputs) =
      (children frame two wrap wrap_checked).map (fun child => child.demand.outputs) := by
  rw [wrap_children, wrap_children]
  rfl

/-- One fixed declaration-indexed frame cannot encode these two required output
targets. Distinct occurrence identity metadata alone does not repair this. -/
theorem fixed_frame_cannot_represent_both :
    ¬ ∃ frame : Frame roles,
      children frame first wrap wrap_checked = [⟨920, firstDemand⟩] ∧
      children frame second wrap wrap_checked = [⟨1020, secondDemand⟩] := by
  rintro ⟨frame, one, two⟩
  have same := fixed_frame_outputs frame first second
  rw [one, two] at same
  simp [firstDemand, secondDemand, childDemand, outputTarget, GeneralDeclarationPatterns.normalize,
    Declaration.outputNames, firstCapture, secondCapture] at same

/-- Pointwise reuse of the existing lookup-order theorem needs no global sharing
policy. Both invocations retain their complete results after registry reordering. -/
theorem both_reordered_lookups :
    lookup GeneralDictionaryEmissionPlanExamples.reversed
      GeneralDictionaryEmissionPlanExamples.reversed_checked (frames first) first 2 =
        some [⟨920, firstDemand⟩] ∧
    lookup GeneralDictionaryEmissionPlanExamples.reversed
      GeneralDictionaryEmissionPlanExamples.reversed_checked (frames second) second 2 =
        some [⟨1020, secondDemand⟩] := by
  constructor
  · rw [← lookup_reorders constructors roles [display, wrap] [wrap, display]
      registry_checked GeneralDictionaryEmissionPlanExamples.reversed_checked
      GeneralDictionaryEmissionPlanExamples.reversed_order (frames first) first 2]
    exact first_lookup
  · rw [← lookup_reorders constructors roles [display, wrap] [wrap, display]
      registry_checked GeneralDictionaryEmissionPlanExamples.reversed_checked
      GeneralDictionaryEmissionPlanExamples.reversed_order (frames second) second 2]
    exact second_lookup

end Yulang.GeneralDictionaryInvocationExamples
