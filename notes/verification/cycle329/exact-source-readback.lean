import Yulang.GeneralDeclarativeStableCrossCut329
import Yulang.GeneralDeclarativeStableWriteVerdict329
import Yulang.GeneralDeclarativeStablePoint329
import Yulang.GeneralDeclarativeStablePendingAnchor329

open Yulang
open GeneralDeclarativeHead320 (Equation)

section ExactSelectionWrites
open GeneralDeclarativeStableFixture329 (frame child cas)
open GeneralDeclarativeStableTies329 (rows pairOf)

example : rows frame.base (frame.spans.map pairOf) = ([⟨7,.variable 8⟩] : List Equation) := rfl
example : frame.rootRows = ([⟨6,.variable 5⟩] : List Equation) := rfl
example : child.outputs = [⟨1,5⟩] := rfl
example : cas = ⟨9,10,11⟩ := rfl
end ExactSelectionWrites

section DistinctArguments
open GeneralDeclarativeStableCrossCompile329 (chosen requested)
open GeneralDeclarativeStableCrossSource329 (spans actual)
open GeneralDeclarativeStableCrossBridge329 (bridge)
open GeneralDeclarativeStableAssemble329 (firsts)
open GeneralDeclarativeStableTies329 (rows pairOf)

example : actual.spans = [(0,⟨3,3,3⟩),(0,⟨7,7,7⟩)] := rfl
example : rows (firsts spans (fun _ => ⟨0,0,0⟩)) (spans.map pairOf) = [⟨3,.variable 7⟩] := rfl
example : requested.arguments = [⟨13,3,14⟩] := rfl
example : chosen.captures 0 = ⟨13,3,14⟩ := rfl
example : bridge.length = 4 := rfl
end DistinctArguments

#print axioms Yulang.GeneralDeclarativeStableResult329.every_model
#print axioms Yulang.GeneralDeclarativeStableModels329.genuine
#print axioms Yulang.GeneralDeclarativeStableCrossResolve329.typed
#print axioms Yulang.GeneralDeclarativeStableCrossCut329.exact_cut
#print axioms Yulang.GeneralDeclarativeStableWriteVerdict329.genuine_type_error
#print axioms Yulang.GeneralDeclarativeStablePendingAnchor329.ordinary_not_backed
