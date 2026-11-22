import Yulang.GeneralDeclarativeTxnNormalized348

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTxnComplete348
open GeneralDeclarations (Registry)
open GeneralNominalCenters (Plan)
open GeneralNominalCandidates (Context)
open GeneralWhereVersionInstall317 (Journal Models install)
open GeneralDeclarativeWhereTxn348 (Txn)
open GeneralDeclarativeTxnReceipt348 (receipt)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalVersionedEffects231 (class_effects_iff)
open GeneralNominalCommonBridge (Assignment)

def Done (r : Registry) (j : Journal rs) (ctx : Context) (p : Plan rs) (id : Nat) : Prop :=
  id = p.packet.site.occurrence.identity ∧ Txn r j ctx p ∧ Ready (install j ctx p).mixed.core p.packet.site.occurrence p

/-- This predicate is tied to the checked transaction, not merely
prepared candidate or raw equality. It authorizes the exact captured
class outputs in every accepted model. -/
theorem actual_outputs {r : Registry} {j : Journal rs} {ctx : Context} {p : Plan rs}
    (complete : Done r j ctx p p.packet.site.occurrence.identity)
    (m : Assignment) (fit : Models (install j ctx p) m) :
    ∀ out ∈ requests (install j ctx p).mixed.core p.packet.site.occurrence,
      GeneralDictionaryDefaultEvidence204.OutputWitness p m out := by
  have closed := receipt complete.2.1 m fit
  exact fun out requested =>
    GeneralDictionaryDefaultEvidence204Laws.output_of_class_effects complete.2.2
      ((class_effects_iff ..).mp closed.effects) requested

theorem carry_by_literal {r : Registry} {j : Journal rs} {ctx : Context} {p : Plan rs}
    (checked : Txn r j ctx p)
    (silence : GeneralWhereOriginSuccessor318.SilentChildren p)
    (ready : Ready j.mixed.core p.packet.site.occurrence p) :
    Done r j ctx p p.packet.site.occurrence.identity := by
  refine ⟨rfl,checked,?_⟩
  unfold Ready
  rw [GeneralDeclarativeTxnEffects348.literal_requests j ctx p silence]
  exact ready

end Yulang.GeneralDeclarativeTxnComplete348
