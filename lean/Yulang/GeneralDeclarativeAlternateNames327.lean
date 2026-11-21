import Yulang.GeneralDeclarativeRepeatModels327

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15000
set_option maxHeartbeats 7600000
namespace Yulang.GeneralDeclarativeAlternateNames327
open GeneralDeclarativeRepeatDecl327
open GeneralDeclarativeRepeatState327
open GeneralDeclarativeRepeatProbe327
open GeneralDeclarativeRepeatFrame327
open GeneralDeclarativeRepeatGraph327
open GeneralDeclarativeRepeatResolve327
open GeneralDeclarativeHead320 (Equation Models)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeLowerKnown321 (Ready knows_row)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeProjectedFrame326 (Frame Generated)
open GeneralDeclarativePriority321 (Local)
open GeneralDeclarativeExampleSource320 (leaf)
open CommonRoleOutermostResolver (Classify)
open CommonNominalFullCarrier (Equivalent)

abbrev alternateArg : Capture := ⟨21,21,21⟩
abbrev alternate : Demand := ⟨child.role,[alternateArg],child.outputs⟩
abbrev alternatePlace : Placement := ⟨fun _ _ => alternateArg,place.targets⟩

theorem different : child ≠ alternate := by
  intro equality
  have arg := List.cons.inj (congrArg Demand.arguments equality)
  have n := congrArg Capture.lower arg.1
  cases n

theorem alternate_emits : children impl (sourceNames impl alternatePlace base) alternatePlace = [alternate] := rfl

theorem alternate_parent (done : Nat → Prop) :
    Frame result reg interp (supported done) root impl base alternatePlace := by
  have original := parent_frame done
  refine ⟨original.head,original.ranges,?_,original.returned⟩
  intro cl present
  have old := original.clauses cl present
  refine ⟨?_,old.output⟩
  cases List.mem_singleton.mp present
  refine ⟨[compoundCode],rfl,?_⟩
  intro pos pattern e somePat someExp _
  cases pos with
  | zero =>
    have h : compound = pattern := Option.some.inj somePat
    have k : compoundCode = e := Option.some.inj someExp
    subst pattern; subst e
    exact ⟨compound_read.2.1,compound_read.2.1,compound_read.2.1⟩
  | succ n => simp at somePat

theorem alternate_selected (done : Nat → Prop) :
    branch done root (.selected impl.id [alternate]) := by
  refine .selected (root_support done) (safe done _) ?_
    ⟨⟨List.mem_cons_self,rfl⟩,root_matches done⟩ ?_
    ⟨base,alternatePlace,alternate_parent done,alternate_emits⟩
  · rintro ⟨d,⟨vis,role⟩,deferred⟩
    cases root_only d vis role
    exact deferred (root_matches done)
  · rintro d ⟨⟨vis,role⟩,_⟩
    rw [root_only d vis role]

theorem alternate_ready (done : Nat → Prop) : Ready (supported done) alternate := by
  intro a here
  cases List.mem_singleton.mp here
  have member : (⟨21,.nominal 0 [.variable 13]⟩ : Equation) ∈ presentRows ++ inputRows := by
    apply List.mem_append_right
    rw [input_exact]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  exact ⟨_,knows_row (authored done member) rfl⟩

theorem alternate_leaf (done : Nat → Prop) : branch done alternate (.selected leaf.id []) := by
  have point : Bounds result alternateArg := ⟨.refl _,.refl _⟩
  have probe : HeadMatches (GeneralDeclarativeOrigins321.restriction (supported done))
      reg.constructors interp alternate leaf :=
    .cons ⟨point,.variable 0,[⟨0,.lower,21⟩],[⟨0,.upper,21⟩],rfl,.capture,.capture⟩ .nil
  have frame : Frame result reg interp (supported done) alternate leaf (fun _ => alternateArg) alternatePlace := by
    refine ⟨.cons ⟨point,.ordinary (.actual rfl .capture ?_)⟩ .nil,
      fun _ _ => point,fun _ nothing => False.elim (List.not_mem_nil nothing),[childRow],rfl,?_⟩
    · intro o read; cases List.mem_singleton.mp read; exact .refl _
    · intro row h; exact List.mem_append_right _ h
  refine .selected (alternate_ready done) (safe done _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,probe⟩ ?_
    ⟨_,alternatePlace,frame,rfl⟩
  · rintro ⟨d,⟨vis,role⟩,deferred⟩
    cases child_only d vis role
    exact deferred probe
  · rintro d ⟨⟨vis,role⟩,_⟩
    rw [child_only d vis role]

theorem same_dictionary (done : Nat → Prop) : Classify (branch done) root (.selected dict) :=
  ⟨.selected impl.id [.selected leaf.id []],
    .selected (alternate_selected done) (.cons (.selected (alternate_leaf done) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

/-- Proof that the unrefined generated-child relation cannot be the
graph of a function on *literal names*. This is not a rival meaning,
declaration, result type or dictionary. -/
theorem no_literal_producer (done : Nat → Prop) :
    ¬∃ choose : Option (List Demand),
      ∀ actual, choose = some actual ↔ Generated result reg interp (supported done) root impl actual := by
  rintro ⟨choose,eq⟩
  have x := (eq [child]).mpr ⟨base,place,parent_frame done,emitted⟩
  have y := (eq [alternate]).mpr ⟨base,alternatePlace,alternate_parent done,alternate_emits⟩
  exact different (List.cons.inj (Option.some.inj (x.symm.trans y))).1

end Yulang.GeneralDeclarativeAlternateNames327
