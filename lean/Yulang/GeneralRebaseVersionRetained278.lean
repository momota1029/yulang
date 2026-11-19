import Yulang.GeneralRebaseVersionEvidence278

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseVersionRetained278
open GeneralDictionaryVersionLoopSource237 (model snapshot F)
open GeneralDictionaryVersionLoopIteration239 (state reachable)
open GeneralDictionaryVersionLoopBook239 (plan)
open GeneralDictionaryVersionLoopPacket237 (actual actual_value origin0)
open GeneralVersionBoundaryCompletion259 (Agree complete agrees)
open GeneralRebaseRoundMicro278 (Tick)
open GeneralRebaseVersionMicro278 (raw installed refreshed)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalAssignmentCongruence238 (Same)
open CommonNominalFullCarrier

abbrev Settled (m : Assignment) :=
  GeneralVersionRebaseModels259.Models GeneralVersionRebaseStep259.finalState m

def retain (m : Assignment) : Assignment := fun id =>
  if id = actual then m id else complete m id

theorem actual_large : 3 < actual := GeneralNominalIdentities.source_above_seed ..

theorem retain_public (m : Assignment) : Agree (retain m) m := by
 constructor
 · intro id small
   have outside : id ≠ actual := by have high := actual_large; omega
   change (if id = actual then m id else complete m id) = m id
   rw [ite_eq_right outside]
   exact (agrees m).1 id small
 · intro id
   unfold retain
   split
   · rfl
   · exact (agrees m).2 id

theorem retain_actual (m : Assignment) : retain m actual = m actual := by simp [retain]

theorem equivalent (m : Assignment) (valid : Settled m) : Same (retain m) (complete m) := by
 have stateValid := (GeneralVersionRebaseModels259.final_exact m).mp valid
 intro id
 refine ⟨?_,(retain_public m).2 id |>.trans ((agrees m).2 id).symm⟩
 by_cases same : id = actual
 · subst id
   have target : (complete m actual).1 = F := by
     simp only [complete,show ¬ actual ≤ 3 by have high := actual_large; omega,ite_false]
     exact actual_value
   rw [retain_actual,target]
   have foo := GeneralDictionaryVersionLoopInitial238.foo_fixed m stateValid.1
   exact ⟨subtype_trans stateValid.2.1 foo.1,subtype_trans foo.2 stateValid.2.2⟩
 · simp only [retain,same,ite_false]
   exact ⟨subtype_refl _,subtype_refl _⟩

theorem stages_retained (m : Assignment) (valid : Settled m) (n : Nat) :
    Models (state n) (retain m) := by
  have raw := (GeneralVersionRebaseModels259.final_exact m).mp valid
  exact (GeneralNominalVersionedSourceCongruence238.source_models_iff (equivalent m valid) (reachable n)).mpr
    (GeneralVersionBoundaryCompletion259.all_stages m raw.1 n)

theorem micro_retained (m : Assignment) (valid : Settled m) (t : Tick) : Models (raw t) (retain m) := by
  rcases t with ⟨n,p⟩
  cases p
  · exact stages_retained m valid n
  · exact (GeneralRebaseVersionPrivate278.refreshed_exact n _).mp
      ((GeneralRebaseVersionPrivate278.reobserved_exact n _).mp (stages_retained m valid (n+1)))
  · exact (GeneralRebaseVersionPrivate278.reobserved_exact n _).mp (stages_retained m valid (n+1))

theorem packet_retained (m : Assignment) (valid : Settled m) (n : Nat) :
    Holds (plan n) (retain m) :=
  ((GeneralRebaseVersionPrivate278.installed_exact n _).mp (micro_retained m valid ⟨n,.installed⟩)).2

theorem packet_binder (m : Assignment) (n : Nat)
    (source : GeneralNominalState.Models snapshot m) (held : Holds (plan n) m) :
    Equivalent (m actual).1 (m 2).1 := by
  have schema := held.2.1.2.2.2.2.1
  rw [GeneralDictionaryVersionLoopFamilyFull238.head_schema] at schema
  have entry := schema.2 ⟨0,origin0,.actual⟩ (by simp)
  simp only [ite_true] at entry
  rw [GeneralNominalVersionedFrame231.binder_eq,GeneralDictionaryVersionLoopFamilyFull238.binder_exact] at entry
  have root := GeneralDictionaryVersionLoopInitial238.root_fixed m source
  have seen : GeneralNominalRecursiveInspection.Observes m origin0 F :=
    .nominal (.source 3) root (by rfl)
  have binder : Equivalent F (m actual).1 := entry.2.2 _ _ seen (.source actual)
  have foo := GeneralDictionaryVersionLoopInitial238.foo_fixed m source
  exact ⟨subtype_trans binder.2 foo.2,subtype_trans foo.1 binder.1⟩

/-- Public endpoint agreement and the entire retained binder component are
literal. One explicit witness satisfies every microstate and every old packet. -/
theorem exact_retention (m : Assignment) :
    Settled m ↔ ∃ old, Agree old m ∧ old actual = m actual ∧ ∀ t, Models (raw t) old := by
  constructor
  · intro held
    exact ⟨retain m,retain_public m,retain_actual m,micro_retained m held⟩
  · rintro ⟨old,on,binder,whole⟩
    have source := GeneralVersionPublicProjection259.model_source 0 old (whole ⟨0,.enter⟩)
    have small := (GeneralVersionPublicProjection259.source_agree old m on).mp source
    have packet := ((GeneralRebaseVersionPrivate278.installed_exact 0 old).mp (whole ⟨0,.installed⟩)).2
    have valid := packet_binder old 0 source packet
    rw [binder,on.1 2 (by decide)] at valid
    exact (GeneralVersionRebaseModels259.final_exact m).mpr ⟨small,valid⟩

end Yulang.GeneralRebaseVersionRetained278
