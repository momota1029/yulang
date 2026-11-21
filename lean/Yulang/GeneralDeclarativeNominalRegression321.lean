import Yulang.GeneralDeclarativeNominalHead321
import Yulang.GeneralDeclarativeExampleSource320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNominalRegression321
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeExampleSource320 (input point interp nApp int)
open GeneralDeclarationExamples (constructors)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeTrace321 (Trace Links Occurrence)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeEntailment320 (Entails)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeArgumentFacts320 (headFact)
open GeneralDeclarativeNominalHead321 (supported_nominal_head)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonNominalFullCarrier (nominal)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

def state : State := ⟨⟨[],[(0,1),(1,2)]⟩,[⟨0,nApp 3⟩,⟨2,nApp 4⟩]⟩
def support : Supported state (fun _ => False) :=
  ⟨fun row origin => row = ⟨0,nApp 3⟩ ∧ origin = .source,
    fun h => h.1.symm ▸ List.mem_cons_self⟩
def capture : Nat → GeneralDeclarativeWhere319.Capture := fun _ => point 3

theorem lower : (⟨0,nApp 3⟩ : Equation) ∈ (restriction support).equations :=
  from_source support ⟨rfl,rfl⟩

theorem upper : (⟨2,nApp 4⟩ : Equation) ∈ state.equations :=
  List.mem_cons_of_mem _ List.mem_cons_self

theorem bounds : Bounds state input := ⟨.interval List.mem_cons_self,
  .interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩

theorem head_from_one_walk :
    Result state (headFact constructors interp capture input (.app 0 [.var 0])) := by
  let occurrence : Occurrence := ⟨0,.actual,3⟩
  have walk : Trace (restriction support) .actual 0 (.nominal 0 [.variable 0]) [occurrence] :=
    .nominal (args := [3]) (alias_refl _) lower (.cons .capture .nil)
  have links : Links (restriction support) capture [occurrence] := by
    intro found member
    cases List.mem_singleton.mp member
    exact alias_refl _
  exact supported_nominal_head support (arg := input) bounds lower upper rfl rfl walk links

theorem upper_is_not_expansion_support : (⟨2,nApp 4⟩ : Equation) ∉ (restriction support).equations := by
  intro h
  obtain ⟨o,⟨wrong,_⟩,_⟩ := (GeneralDeclarativeOrigins321.backed_iff _ _).mp h
  cases wrong

theorem read_upper_parameter_not_needed :
    Entails state ⟨input.center,nApp 3⟩ := by
  obtain ⟨rows,generated,trueRows⟩ := head_from_one_walk
  change some [⟨1,nApp 3⟩] = some rows at generated
  cases generated
  exact trueRows _ List.mem_cons_self

def model : Assignment := fun n => (if n ≤ 2 then nominal 0 [.inl int] else int, Common.rowEmpty)

theorem inhabited : Models state model := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro pr found
    change pr ∈ [(0,1),(1,2)] at found
    rcases List.mem_cons.mp found with rfl|tail
    · exact CommonNominalFullCarrier.subtype_refl _
    · cases List.mem_singleton.mp tail
      exact CommonNominalFullCarrier.subtype_refl _
  · intro row there
    change row ∈ ([⟨0,nApp 3⟩,⟨2,nApp 4⟩] : List Equation) at there
    rcases List.mem_cons.mp there with rfl|tail
    · exact eqv_refl _
    · cases List.mem_singleton.mp tail
      exact eqv_refl _

end Yulang.GeneralDeclarativeNominalRegression321
