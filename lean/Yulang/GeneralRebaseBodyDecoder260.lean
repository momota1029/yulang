import Yulang.GeneralDefaultRebasePublic260
namespace Yulang.GeneralRebaseBodyDecoder260
open GeneralRebaseStep258
open GeneralNominalCenters
open GeneralDictionaryAssociatedProvenance

inductive Failure where
 | missingBody
 | untranslatedBody
 deriving DecidableEq, Repr

/-- A requested class-output obligation, retaining its actual target and the
explicit/default variable scope. This alone is not a complete packet decoder. -/
def compile (plan : Plan roles) (owner : Nat) (output : GeneralSourceState.Output) : Except Failure Proposal :=
 match lookup roles plan.packet.declaration output.name with
 | none => .error .missingBody
 | some body =>
   let schema := GeneralNominalCenteredHeadMatEffects.bodySchema plan output.target body
   if schema.unknown then .error .untranslatedBody
   else .ok (.installed owner :: GeneralRebaseOwnedOutputKeys260.keys owner schema)

theorem successful (plan : Plan roles) (owner : Nat) (output : GeneralSourceState.Output) (proposal : Proposal) :
 compile plan owner output = .ok proposal ↔
 ∃ body, lookup roles plan.packet.declaration output.name = some body ∧
 (GeneralNominalCenteredHeadMatEffects.bodySchema plan output.target body).unknown = false ∧
 proposal = .installed owner :: GeneralRebaseOwnedOutputKeys260.keys owner
   (GeneralNominalCenteredHeadMatEffects.bodySchema plan output.target body) := by
 unfold compile
 split
 · rename_i absent
   constructor
   · intro impossible; cases impossible
   · rintro ⟨body,found,_⟩; rw [absent] at found; cases found
 · rename_i body found
   dsimp only
   split
   · rename_i unknown
     constructor
     · intro impossible; cases impossible
     · rintro ⟨other,otherFound,translated,_⟩
       rw [found] at otherFound
       cases Option.some.inj otherFound
       simp_all
   · rename_i known
     have translated : (GeneralNominalCenteredHeadMatEffects.bodySchema plan output.target body).unknown = false := by
       simpa only [Bool.not_eq_true] using known
     constructor
     · intro same; exact ⟨body,found,translated,(Except.ok.inj same).symm⟩
     · rintro ⟨other,otherFound,_,same⟩
       rw [found] at otherFound
       cases Option.some.inj otherFound
       rw [same]

theorem equation_meaning (plan : Plan roles) (owner : Nat) (output : GeneralSourceState.Output)
 (body : Body) (assignment : GeneralNominalCommonBridge.Assignment) :
 (∀ fact ∈ GeneralRebaseOwnedOutputKeys260.keys owner (GeneralNominalCenteredHeadMatEffects.bodySchema plan output.target body),
 GeneralRebaseOwnedOutputKeys260.Holds owner (GeneralNominalCenteredHeadMatEffects.bodySchema plan output.target body)
  (GeneralNominalVersionedEffects231.bodyVariables plan assignment body) assignment fact) ↔
 GeneralNominalVersionedEffects231.BodyHolds plan output.target assignment body :=
 GeneralRebaseOwnedOutputKeys260.all_exact ..
end Yulang.GeneralRebaseBodyDecoder260
