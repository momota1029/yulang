import Yulang.GeneralRebaseVersionAliases283
import Yulang.GeneralRebaseLooseAliases283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseAliasTransport283
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralRebaseHistoryOrder282 (history decode preserves_joint)
open GeneralRebaseAliasMemo283 (Aliases cache assignment root define_or_free)
open GeneralRebasePrivateStore282 (Joint)
open GeneralRebaseWholeJournal282 (Observable source_visibility)
open GeneralRebaseWholeRow282 (Projection initialNames)
open GeneralRebaseMixedOwnedTrace277 (raw)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralNominalRebaseEvidenceProjection243 (evidence_congruent)
open GeneralNominalVersionedSourceCongruence238 (source_models_iff)

variable {roles : Roles.RoleDecls} {reg : Registry} {focus : Occurrence roles}
  {state : State roles} {memo : Aliases}

theorem models (seen : Reachable reg focus state) (made : cache (history state) [] = some memo)
    (base : Assignment) : Models state (assignment base memo) ↔ Models state (decode state base) :=
  source_models_iff (GeneralRebaseAliasMemo283.exact _ base _ made) seen

theorem joint (seen : Reachable reg focus state) (made : cache (history state) [] = some memo)
    (r : Registry) (whereAt : Occurrence roles) (data : Payload) (base : Assignment) :
    Joint state r whereAt data (assignment base memo) ↔ Joint state r whereAt data (decode state base) :=
  and_congr (models seen made base)
    (evidence_congruent r state.core whereAt data _ _ (GeneralRebaseAliasMemo283.exact _ base _ made))

theorem absent (made : cache (history state) [] = some memo) (supported : Observable state names)
    (base : Assignment) (n : Nat) (used : n ∈ names) : assignment base memo n = base n := by
  unfold assignment
  rw [define_or_free _ _ _ made (supported n used)]

theorem preserves_source (seen : Reachable reg focus state) (made : cache (history state) [] = some memo)
    (r : Registry) (whereAt : Occurrence roles) (data : Payload) (outer : Assignment) :
    Projection (initialNames (raw state).seed) (fun base => Joint state r whereAt data (assignment base memo)) outer ↔
    Projection (initialNames (raw state).seed) (Joint state r whereAt data) outer := by
  have supported := (source_visibility seen (initialNames (raw state).seed)
    (fun _ h => by have bounded := List.mem_range.mp h; omega)).1
  constructor
  · rintro ⟨base,⟨types,rows⟩,good⟩
    exact ⟨assignment base memo,⟨fun n used => (absent made supported base n used).trans (types n used),rows⟩,good⟩
  · rintro ⟨base,agrees,good⟩
    exact ⟨base,agrees,(joint seen made r whereAt data base).mpr (preserves_joint seen good)⟩

theorem option_query (seen : Reachable reg focus state)
    (made : cache (history state) [] = some memo) (r : Registry) (whereAt : Occurrence roles)
    (data : Payload) (base : Assignment) :
    GeneralRebaseWholeJournal282.View state r whereAt data base ↔
      Joint state r whereAt data (assignment base memo) :=
  (GeneralRebaseWholeJournal282.exact_view seen r whereAt data base).trans (joint seen made r whereAt data base).symm

end Yulang.GeneralRebaseAliasTransport283
