import Yulang.GeneralDeclarativeRepeatedSource323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRepeatedReads323
open GeneralDeclarativeRepeatedSource323
open GeneralDeclarativeExampleSource320 (interp point int)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeLowerKnown321 (Ready knows_row alias_refl Alias)
open GeneralDeclarativeTrace321 (Trace Occurrence)
open GeneralDeclarativeTraceExpand323 (convert)
open GeneralDeclarativeTraceCapture323 (reuse OrdinarySharing aliases_suffice anchored)
open GeneralDeclarativeEndpointProbe321 (Matches HeadMatches)
open GeneralDeclarativeNominalTrace323 (from_lower_trace)
open GeneralDeclarativeRigidProbe323 (direct_variable)
open GeneralDeclarativeRigidSource323 (Ordered Scanned)
open GeneralDeclarativeRigidLocal323 (RigidReads)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeEmissionClause322 (Ready)
open GeneralDeclarativeEmissionOperands322 (Compound)
open GeneralDeclarativeEntailment320 (literal)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeProducerFixture322 (nominal_use)
open GeneralDeclarationPatterns (Pattern)
open CommonRoleOutermostResolver (All₂)

abbrev code : Expr := .nominal 0 [.variable 0]
abbrev observed : List Occurrence := [⟨0,.actual,3⟩,⟨0,.actual,7⟩]
abbrev capA : Nat → Capture := reuse observed (fun _ => point 3)
abbrev capB : Nat → Capture := fun _ => point 3
abbrev parentNames : Names := ⟨capA,fun _ => 3⟩
abbrev childNames : Names := ⟨capB,fun _ => 3⟩
abbrev place : Placement := ⟨fun _ _ => point 998,fun _ _ => 999⟩

theorem a_bounds : Bounds state a := ⟨.interval (by decide +kernel),.interval (by decide +kernel)⟩
theorem b_bounds : Bounds state b := ⟨.interval (by decide +kernel),.interval (by decide +kernel)⟩
theorem point_bounds (n : Nat) : Bounds state (point n) := ⟨.refl _,.refl _⟩

theorem named_A : Trace (restriction support) .lower 0 code [⟨0,.actual,3⟩] :=
  .nominal (args := [3]) (alias_refl _) (row (by simp [eqs])) (.cons .capture .nil)
theorem named_A_hi : Trace (restriction support) .upper 2 code [⟨0,.actual,4⟩] :=
  .nominal (args := [4]) (alias_refl _) (row (by simp [eqs])) (.cons .capture .nil)
theorem named_B : Trace (restriction support) .lower 10 code [⟨0,.actual,7⟩] :=
  .nominal (args := [7]) (alias_refl _) (row (by simp [eqs])) (.cons .capture .nil)
theorem named_B_hi : Trace (restriction support) .upper 12 code [⟨0,.actual,8⟩] :=
  .nominal (args := [8]) (alias_refl _) (row (by simp [eqs])) (.cons .capture .nil)

theorem probes : HeadMatches (restriction support) registry.constructors interp goal parent :=
  .cons ⟨a_bounds,code,_,_,rfl,named_A,named_A_hi⟩
    (.cons ⟨b_bounds,code,_,_,rfl,named_B,named_B_hi⟩ .nil)

theorem child_probe : HeadMatches (restriction support) registry.constructors interp emitted child :=
  .cons ⟨point_bounds 3,.variable 0,[⟨0,.lower,3⟩],[⟨0,.upper,3⟩],rfl,.capture,.capture⟩ .nil

theorem parent_ready : GeneralDeclarativeLowerKnown321.Ready support goal := by
  intro arg found
  rcases List.mem_cons.mp found with rfl|later
  · exact ⟨_,knows_row (row (show (⟨0,nominalCode 3⟩ : Equation) ∈ eqs by simp [eqs])) rfl⟩
  · cases List.mem_singleton.mp later
    exact ⟨_,knows_row (row (show (⟨10,nominalCode 7⟩ : Equation) ∈ eqs by simp [eqs])) rfl⟩

theorem child_ready : GeneralDeclarativeLowerKnown321.Ready support emitted := by
  intro arg found
  cases List.mem_singleton.mp found
  exact ⟨_,knows_row (row (show (⟨3,scalar⟩ : Equation) ∈ eqs by simp [eqs])) rfl⟩

theorem scanned : Ordered state registry.constructors interp goal.arguments parent.head (observed.map convert) :=
  .cons (from_lower_trace (c := registry.constructors) (interp := interp) (p := pat) a_bounds ⟨nominal_use,trivial,trivial⟩ rfl (.cons .variable .nil)
    named_A (literal (show (⟨2,nominalCode 4⟩ : Equation) ∈ eqs by simp [eqs])))
    (.cons (from_lower_trace (c := registry.constructors) (interp := interp) (p := pat) b_bounds ⟨nominal_use,trivial,trivial⟩ rfl (.cons .variable .nil)
      named_B (literal (show (⟨12,nominalCode 8⟩ : Equation) ∈ eqs by simp [eqs]))) .nil)

theorem shared : OrdinarySharing state observed := by
  intro x one y two _
  simp only [observed,List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl|rfl <;> rcases two with rfl|rfl
  · exact alias_refl _
  · exact .backward (show (⟨7,.variable 3⟩ : Equation) ∈ eqs by simp [eqs])
  · exact .forward (show (⟨7,.variable 3⟩ : Equation) ∈ eqs by simp [eqs])
  · exact alias_refl _

theorem capture_exact : capA 0 = point 3 := rfl
theorem actual_child : children parent parentNames place = [emitted] := rfl

theorem parent_reads : RigidReads state registry interp goal parent parentNames place := by
  refine ⟨⟨observed.map convert,scanned,anchored state observed _,aliases_suffice shared⟩,?_,?_,?_,?_⟩
  · intro x used
    change x ∈ [0,0] at used
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with rfl|rfl <;> exact point_bounds 3
  · intro arg present
    rcases List.mem_cons.mp present with rfl|tail
    · exact a_bounds
    · cases List.mem_singleton.mp tail
      exact b_bounds
  · intro _ impossible
    cases impossible
  · intro clause there
    cases List.mem_singleton.mp there
    constructor
    · refine ⟨[.variable 0],.cons rfl .nil,?_⟩
      intro i pat exp idx code compound
      cases List.mem_singleton.mp (List.mem_of_getElem? idx)
      exact False.elim (compound 0 rfl)
    · intro _ impossible
      cases impossible

theorem child_reads : RigidReads state registry interp emitted child childNames place := by
  let data : List GeneralDeclarativeTermWalk322.Occurrence := [⟨0,.actual,.variable 3⟩]
  refine ⟨⟨data,.cons (direct_variable (c := registry.constructors) (interp := interp) (p := .var 0) (point_bounds 3) trivial rfl) .nil,?_,?_⟩,
    fun _ _ => point_bounds 3,?_,?_,?_⟩
  · intro n o found m _
    by_cases h : n = 0
    · subst n
      have same := Option.some.inj (show some (⟨0,.actual,.variable 3⟩ : GeneralDeclarativeTermWalk322.Occurrence) = some o from found)
      cases same
      exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl (m 3).1
    · simp [GeneralDeclarativeTermCapture322.first,data,Ne.symm h] at found
  · intro x one y two _ m _
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
  · intro arg belongs
    cases List.mem_singleton.mp belongs
    exact point_bounds 3
  · intro _ impossible
    cases impossible
  · intro _ impossible
    cases impossible

end Yulang.GeneralDeclarativeRepeatedReads323
