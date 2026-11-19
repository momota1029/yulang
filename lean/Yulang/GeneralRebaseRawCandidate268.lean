import Yulang.GeneralRebaseVersionedK2Probe268

namespace Yulang.GeneralRebaseRawCandidate268
open GeneralDeclarations (Registry Declaration DeclarationChecked)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCandidates (Context Metadata)
open GeneralNominalRecursiveCandidates (arguments report)
open GeneralNominalVersionedCandidates231 (Prepared)
open GeneralNominalVersionedCycles232 (RawCandidateK2)
open GeneralNominalCycleK2 (RecursAt)
open GeneralRebasePartialBool268 (Answer Reflect both neg)
open GeneralRebasePartialFinite268 (any any_sound transfer)
open GeneralRebaseRawK2Probe268 (bool_reflect)
open GeneralRebaseInspectionChecks268 (Head BoundList)
open GeneralRebaseCandidateChecks267 (allKnown allKnown_exact)

def visited (ctx : Context) (focus : Occurrence roles) (decl : Declaration)
 (recurs : Fin ctx.state.base.slots → Answer) : Answer :=
 match arguments ctx focus with
 | none => some false
 | some bounds => any (fun entry => recurs entry.1) (report ctx decl bounds).inspected

theorem visited_sound (ctx : Context) (focus : Occurrence roles) (decl : Declaration)
 (recurs : Fin ctx.state.base.slots → Answer) (evidence : ∀ i, Reflect (RecursAt ctx.state i) (recurs i)) :
 Reflect (∃ bounds, arguments ctx focus = some bounds ∧
    ∃ item ∈ (report ctx decl bounds).inspected, RecursAt ctx.state item.1) (visited ctx focus decl recurs) := by
 unfold visited
 split
 · rename_i absent
   rintro ⟨bounds,loc,_⟩
   rw [absent] at loc
   cases loc
 · rename_i bounds located
   apply transfer (p := ∃ item ∈ (report ctx decl bounds).inspected, RecursAt ctx.state item.1)
   · constructor
     · exact fun facts => ⟨bounds,located,facts⟩
     · rintro ⟨other,found,facts⟩
       cases Option.some.inj (found.symm.trans located)
       exact facts
   · exact any_sound _ _ _ (fun item _ => evidence item.1)

def check (registry : Registry) (ctx : Context) (focus : Occurrence roles) (metadata : Answer)
 (head : Declaration → BoundList ctx → Answer) (recurs : Fin ctx.state.base.slots → Answer) : Answer :=
 both (some (allKnown ctx.state focus.demand))
  (any (fun decl =>
   both (some (decl.role == focus.demand.role))
    (both (GeneralRebaseInspectionChecks268.check registry ctx focus decl metadata (head decl)).1
      (visited ctx focus decl recurs))) registry.declarations)

theorem check_sound (registry : Registry) (ctx : Context) (focus : Occurrence roles) (metadata : Answer)
 (head : Declaration → BoundList ctx → Answer) (recurs : Fin ctx.state.base.slots → Answer)
 (metaKnown : Reflect (Metadata registry ctx) metadata)
 (headSound : ∀ decl ∈ registry.declarations, ∀ bounds,
   arguments ctx (GeneralNominalVersionedCandidates231.inputs focus) = some bounds →
   Reflect (Head registry ctx focus decl bounds) (head decl bounds))
 (recursSound : ∀ i, Reflect (RecursAt ctx.state i) (recurs i))
 (decls : ∀ decl ∈ registry.declarations, DeclarationChecked registry.constructors roles decl) :
 Reflect (RawCandidateK2 registry ctx focus) (check registry ctx focus metadata head recurs) := by
 apply GeneralRebasePartialBool268.both_sound (bool_reflect _ _ (allKnown_exact ..))
 apply transfer (p := ∃ decl ∈ registry.declarations, decl.role = focus.demand.role ∧
   Prepared registry ctx focus decl ∧ ∃ bounds, arguments ctx focus = some bounds ∧
   ∃ item ∈ (report ctx decl bounds).inspected, RecursAt ctx.state item.1)
 · constructor
   · rintro ⟨decl,listed,h⟩
     exact ⟨decl,listed,decls decl listed,h⟩
   · rintro ⟨decl,listed,_,h⟩
     exact ⟨decl,listed,h⟩
 · apply any_sound
   intro decl listed
   exact GeneralRebasePartialBool268.both_sound (bool_reflect _ _ (beq_iff_eq ..))
     (GeneralRebasePartialBool268.both_sound
       (GeneralRebaseInspectionChecks268.check_sound registry ctx focus decl metadata
          (head decl) metaKnown (headSound decl listed)).1 (visited_sound ctx focus decl recurs recursSound))

end Yulang.GeneralRebaseRawCandidate268
