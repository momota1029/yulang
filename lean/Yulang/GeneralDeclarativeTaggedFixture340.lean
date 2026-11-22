import Yulang.GeneralDeclarativeTaggedDictionary340
import Yulang.GeneralDeclarativePlainFixture323
import Yulang.GeneralDeclarativeRecordReplay330

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 2000000
namespace Yulang.GeneralDeclarativeTaggedFixture340
open GeneralDeclarations (Registry Declaration DeclarationChecked Checked)
open GeneralDeclarationExamples (roles)
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs variablesArgs ArgsWellScoped WellScoped)
open GeneralDeclarativePlainFixture323 (source merged)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds Demand)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralDeclarativeTaggedSources340 (BoundsRead)
open GeneralDeclarativeTaggedPatch340 (captured)
open GeneralDeclarativeTaggedWhole340 (fullState copied existing_head)
open GeneralDeclarativeTaggedInputs340 (Inputs)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty variant)

abbrev body := GeneralDeclarativeRecordDecl326.body
abbrev chosen : Declaration := ⟨97,1,[source],[],[body],[]⟩
abbrev registry : Registry := ⟨catalogue,roles,[chosen]⟩
abbrev a : Capture := ⟨0,1,2⟩
abbrev d : Demand := ⟨1,[a],[⟨0,6⟩]⟩
abbrev eInt : Expr := .primitive (.scalar .int) []
abbrev eBool : Expr := .primitive (.scalar .bool) []
abbrev outer : Expr := .join (.variant 7 eInt) (.variant 7 eBool)
abbrev whole : Expr := .join eInt eBool
abbrev initial : State := ⟨⟨[],[(0,1),(1,2)]⟩,[⟨0,outer⟩,⟨2,outer⟩]⟩

def p : Supported initial (fun _ => False) :=
  ⟨fun e o => e ∈ initial.equations ∧ o = .source,And.left⟩

theorem read : BoundsRead p a 7 whole whole := by
  refine ⟨⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩,?_,?_⟩
  · exact ⟨outer,⟨0,alias_refl _,from_source _ ⟨List.mem_cons_self,rfl⟩⟩,rfl⟩
  · exact ⟨outer,⟨2,alias_refl _,from_source _ ⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩⟩,rfl⟩

theorem lower_same_tag :
    GeneralDeclarativeTaggedSources340.merge 7 outer = some whole := rfl

/-- There is no authored normalized variant row available to the old
constructor-tag read on this fixture. The new observer actually reads
the original joined syntax, not its expected normal form as support. -/
theorem old_not_ready : ¬GeneralDeclarativeLowerKnown321.Ready p d := by
  intro old
  obtain ⟨tag,row,backed,_,dec⟩ := old a List.mem_cons_self
  have written := p.ordinary ((GeneralDeclarativeOrigins321.backed_iff p row).mp backed).choose_spec.1
  change row ∈ [⟨0,outer⟩,⟨2,outer⟩] at written
  rcases List.mem_cons.mp written with rfl|other
  · cases dec
  · cases List.mem_singleton.mp other
    cases dec

theorem checked_decl : DeclarationChecked catalogue roles chosen := by
  have previous := GeneralDeclarativeRecordDecl326.checked_decl
  constructor
  · refine ⟨rfl,previous.signature.2.1,previous.signature.2.2.1,?_⟩
    intro req absent; cases absent
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames,Pattern.variables,variablesArgs]
  · refine ⟨?_,?_,?_⟩
    · intro req empty; cases empty
    · intro e found name used
      cases List.mem_singleton.mp found
      change name ∈ [1] at used
      cases List.mem_singleton.mp used
      exact .inl (by decide +kernel)
    · intro req empty; cases empty
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped]
  all_goals intro c unavailable; cases unavailable

theorem checked : Checked registry := by
  refine ⟨by decide,?_⟩
  intro c selected
  cases List.mem_singleton.mp selected
  exact checked_decl

theorem covered : Coverage registry interpretation := by
  refine ⟨?_,GeneralDeclarativeRecordReplay330.covered.2⟩
  intro c occurs
  cases List.mem_singleton.mp occurs
  refine ⟨⟨⟨trivial,trivial⟩,trivial⟩,?_,?_⟩
  · intro req absent; cases absent
  · intro row existsIn; cases List.mem_singleton.mp existsIn; trivial

theorem wanted : Declared registry d := GeneralDeclarativeRecordResolve326.declared

abbrev keep : List Nat := [6]
abbrev payloadCode : Expr := .join (.variable 0) (.variable 1)
abbrev named := fullState initial a 7 whole whole keep payloadCode
abbrev selectedCap := captured initial a 7 whole whole keep
abbrev spans := copied selectedCap [0,1]
abbrev fallback : Nat → Capture := fun _ => ⟨6,6,6⟩
abbrev targets : GeneralDeclarations.Clause → Nat → Nat := fun _ _ => 6

theorem inputs : Inputs p catalogue interpretation keep initial d.arguments chosen.head named spans [] := by
  simpa only [List.cons_append,List.nil_append,List.append_nil] using
    (Inputs.cons (a := a) (pat := source) (p := p) (c := catalogue) (i := interpretation)
      (.whole read GeneralDeclarativePlainFixture323.normalized rfl rfl) Inputs.nil)

theorem exact_same_address : spans = [(0,selectedCap),(1,selectedCap)] := rfl
theorem keep_old_model : GeneralDeclarativeOpaqueConserve328.Retains initial named keep := (existing_head read keep GeneralDeclarativePlainFixture323.normalized rfl
  (rfl : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation merged = some payloadCode)).1

abbrev write : Equation := ⟨6,.variable selectedCap.center⟩
abbrev endState : State := GeneralDeclarativeEntailment320.appendFacts (GeneralDeclarativeStableAssemble329.merged named keep spans fallback).state [write]

theorem actual_compile : compileBody registry interpretation d chosen named spans keep fallback targets =
    some (endState,[]) := rfl

end Yulang.GeneralDeclarativeTaggedFixture340
