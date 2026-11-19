import Yulang.GeneralRebaseAdministrativeProbe268

namespace Yulang.GeneralRebaseInspectionChecks268
open GeneralDeclarations (Registry Declaration)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCandidates (Context Metadata)
open GeneralNominalRecursiveCandidates (arguments report)
open GeneralNominalRecursiveInspection (bindings Finished)
open GeneralNominalVersionedCandidates231 (inputs HeadModels Prepared Failed)
open GeneralRebaseCandidateChecks267 (linked linked_exact fresh fresh_exact finished finished_exact)
open GeneralRebasePartialBool268 (Answer Reflect both either neg)
open GeneralRebasePartialFinite268 (transfer)
open GeneralRebaseRawK2Probe268 (bool_reflect)

abbrev BoundList (ctx : Context) := List (GeneralNominalInspection.Bounds ctx.state)

def Fresh (registry : Registry) (ctx : Context) (focus : Occurrence roles)
 (d : Declaration) (bounds : BoundList ctx) : Prop :=
 GeneralNominalVersionedAllocation231.Fresh ctx.state registry focus.identity (bindings ctx.state (report ctx d bounds))

def Head (registry : Registry) (ctx : Context) (focus : Occurrence roles)
 (d : Declaration) (bounds : BoundList ctx) : Prop :=
 ∃ model, HeadModels registry ctx focus d bounds model

def computed (registry : Registry) (ctx : Context) (focus : Occurrence roles)
 (d : Declaration) (bounds : BoundList ctx) (metadata head : Answer) : Answer × Answer :=
 let info := report ctx d bounds
 let reservation := some (fresh ctx.state registry focus.identity (bindings ctx.state info))
 let prepared := both metadata (both (some (linked ctx.state (inputs focus).demand))
   (both reservation (both (some (finished info)) head)))
 let failed := both metadata (both reservation (both (some (info.blocked.isEmpty && info.arity.isEmpty))
   (either (some (!info.conflicts.isEmpty)) (neg head))))
 (prepared,failed)

theorem prepared_formula (registry : Registry) (ctx : Context) (focus : Occurrence roles)
 (d : Declaration) (bounds : BoundList ctx) (located : arguments ctx (inputs focus) = some bounds) :
 Prepared registry ctx focus d ↔ Metadata registry ctx ∧ GeneralNominalState.Linked ctx.state (inputs focus).demand ∧
   Fresh registry ctx focus d bounds ∧ Finished (report ctx d bounds) ∧ Head registry ctx focus d bounds := by
 constructor
 · rintro ⟨metaBit,linked,other,found,fresh,finished,model⟩
   cases Option.some.inj (found.symm.trans located)
   exact ⟨metaBit,linked,fresh,finished,model⟩
 · rintro ⟨metaBit,linked,fresh,finished,model⟩
   exact ⟨metaBit,linked,bounds,located,fresh,finished,model⟩

theorem failed_formula (registry : Registry) (ctx : Context) (focus : Occurrence roles)
 (d : Declaration) (bounds : BoundList ctx) (located : arguments ctx (inputs focus) = some bounds) :
 Failed registry ctx focus d ↔ Metadata registry ctx ∧ Fresh registry ctx focus d bounds ∧
 ((report ctx d bounds).blocked = [] ∧ (report ctx d bounds).arity = []) ∧
 ((report ctx d bounds).conflicts ≠ [] ∨ ¬ Head registry ctx focus d bounds) := by
 constructor
 · rintro ⟨metaBit,other,found,fresh,blocked,arity,bad⟩
   cases Option.some.inj (found.symm.trans located)
   exact ⟨metaBit,fresh,⟨blocked,arity⟩,bad⟩
 · rintro ⟨metaBit,fresh,⟨blocked,arity⟩,bad⟩
   exact ⟨metaBit,bounds,located,fresh,blocked,arity,bad⟩

theorem computed_sound (registry : Registry) (ctx : Context) (focus : Occurrence roles)
 (d : Declaration) (bounds : BoundList ctx) (located : arguments ctx (inputs focus) = some bounds)
 (metaBit head : Answer) (metaSound : Reflect (Metadata registry ctx) metaBit) (headSound : Reflect (Head registry ctx focus d bounds) head) :
 Reflect (Prepared registry ctx focus d) (computed registry ctx focus d bounds metaBit head).1 ∧
 Reflect (Failed registry ctx focus d) (computed registry ctx focus d bounds metaBit head).2 := by
 let info := report ctx d bounds
 have reserve : Reflect (Fresh registry ctx focus d bounds)
    (some (fresh ctx.state registry focus.identity (bindings ctx.state info))) :=
   bool_reflect _ _ (fresh_exact ..)
 have finished : Reflect (Finished info) (some (GeneralRebaseCandidateChecks267.finished info)) :=
   bool_reflect _ _ (finished_exact ..)
 have inspected : Reflect (info.blocked = [] ∧ info.arity = []) (some (info.blocked.isEmpty && info.arity.isEmpty)) :=
   bool_reflect _ _ (by simp)
 have conflict : Reflect (info.conflicts ≠ []) (some (!info.conflicts.isEmpty)) :=
   GeneralRebasePartialBool268.neg_sound (bool_reflect _ _ (by simp))
 exact ⟨transfer (prepared_formula registry ctx focus d bounds located).symm
    (GeneralRebasePartialBool268.both_sound metaSound (GeneralRebasePartialBool268.both_sound
      (bool_reflect _ _ (linked_exact ..)) (GeneralRebasePartialBool268.both_sound reserve
        (GeneralRebasePartialBool268.both_sound finished headSound)))),
   transfer (failed_formula registry ctx focus d bounds located).symm
    (GeneralRebasePartialBool268.both_sound metaSound (GeneralRebasePartialBool268.both_sound reserve
      (GeneralRebasePartialBool268.both_sound inspected
        (GeneralRebasePartialBool268.either_sound conflict (GeneralRebasePartialBool268.neg_sound headSound)))))⟩

def check (registry : Registry) (ctx : Context) (focus : Occurrence roles) (d : Declaration)
 (metadata : Answer) (head : BoundList ctx → Answer) : Answer × Answer :=
 match arguments ctx (inputs focus) with
 | none => (some false,some false)
 | some bounds => computed registry ctx focus d bounds metadata (head bounds)

theorem check_sound (registry : Registry) (ctx : Context) (focus : Occurrence roles) (d : Declaration)
 (metadata : Answer) (head : BoundList ctx → Answer)
 (metaSound : Reflect (Metadata registry ctx) metadata)
 (headSound : ∀ bounds, arguments ctx (inputs focus) = some bounds → Reflect (Head registry ctx focus d bounds) (head bounds)) :
 Reflect (Prepared registry ctx focus d) (check registry ctx focus d metadata head).1 ∧
 Reflect (Failed registry ctx focus d) (check registry ctx focus d metadata head).2 := by
 unfold check
 split
 · rename_i missing
   constructor
   · intro ready
     obtain ⟨_,_,_,found,_⟩ := ready
     rw [missing] at found
     cases found
   · intro failed
     obtain ⟨_,_,found,_⟩ := failed
     rw [missing] at found
     cases found
 · rename_i bounds located
   exact computed_sound registry ctx focus d bounds located metadata (head bounds) metaSound (headSound bounds located)

end Yulang.GeneralRebaseInspectionChecks268
