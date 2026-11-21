import Yulang.GeneralDeclarativeFiniteTrees327
import Yulang.GeneralDeclarativeAliasChecker327
import Yulang.GeneralDeclarativeRelation327
import Yulang.GeneralDeclarativeMixedReplay327
import Yulang.GeneralDeclarativeAlternateNames327
import Yulang.GeneralDeclarativeAliasStatus327
import Yulang.GeneralDeclarativeMixedClause327
import Yulang.GeneralDeclarativeInPlace327

set_option maxRecDepth 12000
namespace Yulang.Cycle327Independent
open GeneralDeclarativeRelationalCheck327 (guard check Flags)
open GeneralDeclarativeRepeatDecl327 (reg root impl)
open GeneralDeclarativeRepeatState327 (child)
open GeneralDeclarativeAlternateNames327 (alternate)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeRepeatModels327 (genuine_two_models)
open GeneralDeclarativeFiniteCheck327 (Annotated validate validateMany)

def observed (known cycle wait : Bool) : Flags :=
  ⟨known,cycle,fun d => d.id == impl.id,fun d => d.id == impl.id && wait⟩

example : guard reg root (observed false false false) = some .pending := rfl
example : guard reg root (observed false true false) = none := rfl
example : guard reg root (observed true true true) = some .rejected := rfl
example : guard reg root (observed true false true) = some .pending := rfl
example : guard reg root (observed true false false) = some (.elected 97) := rfl

-- Bounded check of two known good literal witness choices, not a
-- decision procedure for every frame that could exist in this state.
def names (d : Demand) :=
  d.arguments.map (fun a => (a.lower,a.center,a.upper))
def returns (d : Demand) :=
  d.outputs.map (fun out => (out.name,out.target))
def acceptKnown (k : Nat) : List Demand → Bool
  | [call] => decide (k = 97 ∧ call.role = 2 ∧ returns call = [(1,5)] ∧
    (names call = [(20,21,22)] ∨ names call = [(21,21,21)]))
  | _ => false

example : check reg root (observed true false false) acceptKnown (.selected 97 [child]) = true := rfl
example : check reg root (observed true false false) acceptKnown (.selected 97 [alternate]) = true := rfl
example : check reg root (observed true false false) acceptKnown
    (.selected 97 [{ child with outputs := [⟨1,8⟩] }]) = false := rfl
example : check reg root (observed true false true) acceptKnown (.selected 97 [alternate]) = false := rfl

def marker (_ : Demand) : CommonRoleOutermostResolver.Frontier Demand → Bool
  | .selected key kids => if key = 3 then kids.isEmpty else acceptKnown key kids
  | _ => false
def sample : Annotated := .selected 97 [child] [.selected 3 [] []]
def sampleAlt : Annotated := .selected 97 [alternate] [.selected 3 [] []]
def broken : Annotated := .selected 97 [child] []

example : validate marker root sample = true := by
  simp [sample,validate,validateMany,marker]
  rfl
example : validate marker root sampleAlt = true := by
  simp [sampleAlt,validate,validateMany,marker]
  rfl
example : validate marker root broken = false := by
  simp [broken,validate,validateMany]

#print axioms GeneralDeclarativeRepeatModels327.genuine_two_models
#print axioms GeneralDeclarativeAlternateNames327.no_literal_producer
#print axioms GeneralDeclarativeAliasStatus327.real_comparison
#print axioms GeneralDeclarativeMixedClause327.fixed_selected_where
#print axioms GeneralDeclarativeFiniteTrees327.classifies_iff
#print axioms GeneralDeclarativeInPlace327.current_sound
#print axioms GeneralDeclarativeAliasChecker327.checked_before
#print axioms GeneralDeclarativeAliasChecker327.checked_after
#print axioms GeneralDeclarativeMixedReplay327.assembled
#print axioms GeneralDeclarativeRelation327.no_functional_view
end Yulang.Cycle327Independent
