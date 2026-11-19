import Yulang.GeneralRebaseLooseEvidence278
import Yulang.GeneralDictionaryRebaseFacts259

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseLooseRetained278
open GeneralDictionaryLooseLoopSource240 (snapshot)
open GeneralDictionaryLooseIterationIteration240 (state)
open GeneralDictionaryLooseIterationBook240 (plan)
open GeneralDictionaryLooseLoopPacket240 (actual)
open GeneralRebaseRoundMicro278 (Tick)
open GeneralRebaseLooseMicro278 (raw)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryInitialProjection257 (Agree)
open GeneralDictionaryUniformFill258 (fill actual_fixed)

abbrev Settled (m : Assignment) :=
  GeneralDictionaryRebaseFacts259.Models GeneralDictionaryRebaseStep258.finalState m

theorem retain_public (m : Assignment) : Agree (fill m) m :=
  ⟨fun id small => GeneralDictionaryUniformFill258.initial m id small,GeneralDictionaryUniformFill258.rows m⟩

theorem stages_retained (m : Assignment) (valid : Settled m) (n : Nat) : Models (state n) (fill m) := by
  have published := (GeneralDictionaryRebaseFacts259.prior_final_exact m).mp valid
  exact (GeneralDictionaryUniformJournal258.all_stages m).mpr
    ((GeneralDictionaryRebasePublic258.final_exact m).mp published) n

theorem micro_retained (m : Assignment) (valid : Settled m) (t : Tick) : Models (raw t) (fill m) := by
  rcases t with ⟨n,p⟩
  cases p
  · exact stages_retained m valid n
  · exact (GeneralRebaseLoosePrivate278.refreshed_exact n _).mp
      ((GeneralRebaseLoosePrivate278.reobserved_exact n _).mp (stages_retained m valid (n+1)))
  · exact (GeneralRebaseLoosePrivate278.reobserved_exact n _).mp (stages_retained m valid (n+1))

theorem packet_retained (m : Assignment) (valid : Settled m) (n : Nat) :
    Holds (plan n) (fill m) :=
  ((GeneralRebaseLoosePrivate278.installed_exact n _).mp (micro_retained m valid ⟨n,.installed⟩)).2

theorem exact_retention (m : Assignment) :
    Settled m ↔ ∃ old, Agree old m ∧ old actual = m actual ∧ ∀ t, Models (raw t) old := by
  constructor
  · intro held
    exact ⟨fill m,retain_public m,actual_fixed m,micro_retained m held⟩
  · rintro ⟨old,on,binder,whole⟩
    have source := (GeneralDictionarySourceExtension258.stage_models 0 m).mp ⟨old,on,whole ⟨0,.enter⟩⟩
    have final := GeneralDictionaryUniformJournal258.recovered 0 old (whole ⟨1,.enter⟩)
    have bind := ((GeneralDictionaryFiniteJournal257.models_exact 1 old).mp final).2
    unfold GeneralDictionaryBinderFact257.Holds at bind
    rw [binder,on.1 2 (by decide)] at bind
    exact (GeneralDictionaryRebaseFacts259.final_exact m).mpr ⟨source,bind⟩

end Yulang.GeneralRebaseLooseRetained278
