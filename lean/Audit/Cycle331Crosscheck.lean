import Yulang.GeneralDeclarativeInlineChildModels331
import Yulang.GeneralDeclarativeInlineRangedModels331
import Yulang.GeneralDeclarativeInlineRepeat331
import Yulang.GeneralDeclarativeInlinePhase331
import Yulang.GeneralDeclarativeInlineOwnerExample331
import Yulang.GeneralDeclarativeInlineFieldProducer331

open Yulang.GeneralDeclarativeHead320 (Equation)
open Yulang.GeneralDeclarativeWhere319 (Capture)
open Yulang.GeneralDeclarativeOpaqueNominal328 (point)

namespace Yulang.Cycle331Crosscheck

example : GeneralDeclarativeInlineChildFrame331.child.arguments = [point 18] := rfl
example : GeneralDeclarativeInlineChildFrame331.frame.rootRows = [⟨6,.variable 19⟩] := rfl
example : GeneralDeclarativeInlineChildFrame331.leafWrite = (⟨5,.variable 18⟩ : Equation) := rfl
example : GeneralDeclarativeInlineRangedFrame331.child.arguments = [(⟨1,3,2⟩ : Capture)] := rfl
example : GeneralDeclarativeInlineRangedFrame331.frame.capture 0 = ⟨1,3,2⟩ := rfl
example : GeneralDeclarativeInlineRangedFrame331.leafWrite = (⟨5,.variable 3⟩ : Equation) := rfl
example : GeneralDeclarativeStableTies329.rows
    (GeneralDeclarativeInlineRepeat331.attempt (fun _ => False)).center
    (GeneralDeclarativeInlineRepeat331.spans.map GeneralDeclarativeStableTies329.pairOf) =
    [(⟨7,.variable 8⟩ : Equation)] := rfl
example (done : Nat → Prop) :
    GeneralDeclarativeInlineOwnerExample331.childRow ∈
      (GeneralDeclarativeOrigins321.restriction (GeneralDeclarativeInlineOwnerExample331.current done)).equations ↔ done 22 :=
  GeneralDeclarativeInlineOwnerExample331.real_gate done

#check GeneralDeclarativeInlineRangedModels331.strictly_internal
#check GeneralDeclarativeInlinePhase331.real_pending
#print axioms GeneralDeclarativeInlineChildModels331.checked_dictionary
#print axioms GeneralDeclarativeInlineRangedModels331.real_nonpoint_child
#print axioms GeneralDeclarativeInlineRepeat331.actual_rejected

end Yulang.Cycle331Crosscheck
