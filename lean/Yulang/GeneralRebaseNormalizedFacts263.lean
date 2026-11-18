import Yulang.GeneralRebaseNormalizedBody263
import Yulang.GeneralRebaseQuadraticBudget262

namespace Yulang.GeneralRebaseNormalizedFacts263
open GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceState (Output)
open GeneralRebaseStep258 (Fact)
open GeneralRebaseNormalizedBody263 (Compatible)

/-- An address in a zero-or-one-equation table denotes exactly that table's
whole equation, not an arbitrary conjunction shared across multiple addresses. -/
theorem singleton_holds (owner : Nat) (schema : GeneralNominalCenteredHeadMatSchemas.Schema)
 (variables) (assignment : Assignment) (fact : Fact)
 (small : schema.equations.length ≤ 1) :
 GeneralRebaseOwnedOutputKeys260.Holds owner schema variables assignment fact ↔
 fact ∈ GeneralRebaseOwnedOutputKeys260.keys owner schema ∧ schema.Holds variables assignment := by
 constructor
 · rintro ⟨index,key,valid⟩
   refine ⟨(GeneralRebaseOwnedOutputKeys260.member ..).mpr ⟨index,key⟩,?_⟩
   intro equation member
   obtain ⟨position,bound,equal⟩ := List.mem_iff_getElem.mp member
   have same : index.val = position := by have h := index.isLt; omega
   subst position
   rw [equal] at valid
   exact valid
 · rintro ⟨member,valid⟩
   obtain ⟨index,key⟩ := (GeneralRebaseOwnedOutputKeys260.member ..).mp member
   exact ⟨index,key,valid _ (List.getElem_mem index.isLt)⟩

theorem local_meaning (plan : Plan roles) (owner : Nat) (output : Output)
 (assignment : Assignment) (fact : Fact) :
 GeneralRebaseBodyTable261.localHolds plan owner output assignment fact ↔
 fact ∈ GeneralRebaseBodyTable261.keys plan owner output ∧
 ∀ body, GeneralDictionaryAssociatedProvenance.lookup roles plan.packet.declaration output.name = some body →
 GeneralNominalVersionedEffects231.BodyHolds plan output.target assignment body :=
 (singleton_holds _ _ _ assignment fact (GeneralRebaseQuadraticBudget262.schema_bound plan output)).trans
   (and_congr Iff.rfl (GeneralRebaseBodyTable261.schema_meaning plan output assignment))

theorem local_holds (first last : Plan roles) (assignment : Assignment)
 (compatible : Compatible first last assignment) (owner : Nat) (output : Output) (fact : Fact) :
 GeneralRebaseBodyTable261.localHolds first owner output assignment fact ↔
 GeneralRebaseBodyTable261.localHolds last owner output assignment fact := by
 rw [local_meaning,local_meaning,GeneralRebasePlanSemantic262.keys_eq first last compatible.layout owner output]
 apply and_congr Iff.rfl
 constructor
 · intro valid body found
   have original : GeneralDictionaryAssociatedProvenance.lookup roles first.packet.declaration output.name = some body := by
     rw [compatible.layout.declaration]; exact found
   exact (GeneralRebaseNormalizedBody263.lookup_body first last assignment compatible output.name output.target body original).mp
     (valid body original)
 · intro valid body found
   have other : GeneralDictionaryAssociatedProvenance.lookup roles last.packet.declaration output.name = some body := by
     rw [← compatible.layout.declaration]; exact found
   exact (GeneralRebaseNormalizedBody263.lookup_body first last assignment compatible output.name output.target body found).mpr
     (valid body other)

theorem stable_body_holds (first last : Plan roles) (assignment : Assignment)
 (compatible : Compatible first last assignment) (owner : Nat) (fact : Fact) :
 GeneralRebaseStableBody261.Holds first owner assignment fact ↔
 GeneralRebaseStableBody261.Holds last owner assignment fact := by
 constructor
 · intro valid output member
   exact (local_holds first last assignment compatible owner output fact).mp
     (valid output ((GeneralRebasePlanSemantic262.keys_eq first last compatible.layout owner output).symm ▸ member))
 · intro valid output member
   exact (local_holds first last assignment compatible owner output fact).mpr
     (valid output ((GeneralRebasePlanSemantic262.keys_eq first last compatible.layout owner output) ▸ member))

theorem stable_class_holds (first last : Plan roles) (assignment : Assignment)
 (compatible : Compatible first last assignment) (owner : Nat) (fact : Fact) :
 GeneralRebaseStableClass261.Holds first owner assignment fact ↔
 GeneralRebaseStableClass261.Holds last owner assignment fact :=
 and_congr (stable_body_holds first last assignment compatible owner fact) Iff.rfl

theorem of_global (first last : Plan roles) (assignment : Assignment)
 (compatible : GeneralRebasePlanSemantic262.Compatible first last assignment) : Compatible first last assignment :=
 ⟨compatible.layout,fun _ _ name _ => compatible.binders name,compatible.centers⟩
end Yulang.GeneralRebaseNormalizedFacts263
