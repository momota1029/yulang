import Yulang.GeneralDeclarativeNestedReplayCases332
import Yulang.GeneralDeclarativeNestedSeekCases332

set_option maxRecDepth 24000
set_option maxHeartbeats 18000000

open Yulang

#check @GeneralDeclarativeNestedDecode332.normalized_sound
#check @GeneralDeclarativeNestedHeadList332.capture_sound
#check @GeneralDeclarativeNestedReplay332.current_after_replay
#check @GeneralDeclarativeNestedSiblingsModels332.exact_siblings_same_model
#check @GeneralDeclarativeNestedBracket332.upper_none_not_clash
#check @GeneralDeclarativeNestedBracket332.lower_none_is_real
#check @GeneralDeclarativeNestedReplayCases332.cross_argument_conflict
#check @GeneralDeclarativeNestedSeekCases332.auto_read
#check @GeneralDeclarativeNestedSeek332.seek_complete_for_path
#print axioms GeneralDeclarativeNestedReplay332.current_after_replay
#print axioms GeneralDeclarativeNestedSiblingsModels332.exact_siblings_same_model
#print axioms GeneralDeclarativeNestedReplayCases332.cross_argument_conflict

open GeneralDeclarativeNestedSiblingsFrame332 (indexed source keep targets parent childList first)
open GeneralDeclarativeNestedSiblingsDecl332 (registry impl)
open GeneralDeclarativeNestedDecl332 (root)
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarativeNestedFrame332 (fallback)

example (done : Nat → Prop) :
    GeneralDeclarativeNestedReplay332.replay registry interpretation root impl (indexed done) source
      keep fallback targets = some (parent,childList) := rfl

example : GeneralDeclarativeOpaqueBatch328.check childList [first] = false := rfl

example :
    GeneralDeclarativeNestedSeek332.seek (GeneralDeclarativeNestedSeekCases332.index true true) 20 1 =
      some [21] := rfl

example :
    GeneralDeclarativeNestedSeek332.seek (GeneralDeclarativeNestedSeekCases332.index true false) 20 1 =
      none := rfl
