import Yulang.GeneralDeclarativeLateProviderDecl326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeLateProvider326
open GeneralDeclarativeLateProviderDecl326
open GeneralDeclarativeCovariantState326 (final root_range sourceRows lo old_row)
open GeneralDeclarativeCovariantSupport326 (controlled source_outer scalarRow)
open GeneralDeclarativeCovariantProbe326 (no_cycles)
open GeneralDeclarativeHead320 (Equation Models)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeProjectedFrame326 (Frame Rule sound)
open GeneralDeclarativeLowerKnown321 (Ready knows_row)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeExampleSource320 (point)
open GeneralDeclarationExamples (constructors)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeOutputSource323 (Declared)
open CommonRoleOutermostResolver (Classify Dictionary)

def tests (done : Nat → Prop) : Candidates :=
  ⟨HeadMatches (restriction (controlled done)) constructors interpretation,
   fun d decl => ¬ HeadMatches (restriction (controlled done)) constructors interpretation d decl⟩

abbrev branch (done : Nat → Prop) := Rule final reg interpretation (controlled done) (tests done)

theorem safe (done : Nat → Prop) (d : Demand) : ¬ Recurs final reg interpretation (tests done) d := by
  rintro (⟨arg,_,cycle⟩|⟨_,_,_,_,_,_,_,_,_,p,_,cycle⟩)
  · exact no_cycles arg.lower cycle
  · exact no_cycles p cycle

abbrev inputBase (_ : Nat) := point 0
abbrev place : Placement := ⟨fun _ _ => point 900,fun _ _ => 901⟩
abbrev dict : Dictionary := .node provider.id []

theorem range : Bounds final (point 0) := ⟨.refl _,.refl _⟩

theorem ready (done : Nat → Prop) : Ready (controlled done) call := by
  intro actual appears
  cases List.mem_singleton.mp appears
  exact ⟨_,knows_row (source_outer done (show (⟨0,lo⟩ : Equation) ∈ sourceRows from List.mem_cons_self)
    (by decide +kernel)) rfl⟩

theorem probe (done : Nat → Prop) :
    HeadMatches (restriction (controlled done)) constructors interpretation call provider :=
  .cons ⟨range,.variable 0,[⟨0,.lower,0⟩],[⟨0,.upper,0⟩],rfl,.capture,.capture⟩ .nil

theorem frame (done : Nat → Prop) :
    Frame final reg interpretation (controlled done) call provider inputBase place := by
  refine ⟨.cons ⟨range,.ordinary (.actual rfl .capture ?_)⟩ .nil,fun _ _ => range,
    fun _ impossible => False.elim (List.not_mem_nil impossible),[scalarRow],rfl,?_⟩
  · intro o belongs
    cases List.mem_singleton.mp belongs
    exact .refl _
  · intro e belongs
    cases List.mem_singleton.mp belongs
    exact old_row (by simp [sourceRows])

theorem provider_only (d) (visible : d ∈ reg.declarations) (role : d.role = call.role) :
    d = provider := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with h|h|h
  · cases h
    cases role
  · cases h
    cases role
  · exact h

theorem selected (done : Nat → Prop) : branch done call (.selected provider.id []) := by
  refine .selected (ready done) (safe done _) ?_
    ⟨⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),rfl⟩,probe done⟩ ?_
    ⟨inputBase,place,frame done,rfl⟩
  · rintro ⟨d,⟨visible,role⟩,blocks⟩
    cases provider_only d visible role
    exact blocks (probe done)
  · rintro d ⟨⟨visible,role⟩,_⟩
    rw [provider_only d visible role]

theorem selected_without_own_output : Classify (branch (fun _ => False)) call (.selected dict) :=
  ⟨.selected provider.id [],.selected (selected _) .nil,.selected .nil (.selected rfl)⟩

def completed (n : Nat) : Prop :=
  n = 42 ∧ Classify (branch (fun _ => False)) call (.selected dict)

theorem certified (m) (holds : Models final m) : Evidence reg interpretation m call dict := by
  apply sound checked ?_ holds selected_without_own_output
  intro request h
  cases List.mem_singleton.mp h
  exact ⟨none,rfl⟩

theorem earlier_complete : completed 42 := ⟨rfl,selected_without_own_output⟩

end Yulang.GeneralDeclarativeLateProvider326
