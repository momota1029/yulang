import Yulang.GeneralRebaseDepthExactEnd286

/-! The observational result is genuinely weaker than raw endpoint identity.
One certified scalar refresh also retains an explicit reflexive atom, so two
actual stable snapshots have different raw ordinary-list lengths. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseDepthNonunique286
open GeneralDictionaryOutputDepth252 (roles registry root initial)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralRebaseDepthPathAnchor285 (snapshot)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedObservations233 (Refresh CacheSound)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralRebaseDepthScalar285 (old target cert refreshed new_zero new_one)
open GeneralRebaseDepthSchedule286 (Halted)
open GeneralRebaseDepthConfluence286 (ReadbackSame)
open GeneralRebaseDepthPhase286 (Hop)
open GeneralCanonicalObservations (Recorded)

def trivial : PresenceNormalForm.Atom Nat := .tyLe (.base .int) (.base .int)

theorem trivial_holds (m : GeneralNominalCommonBridge.Assignment) :
    trivial.Holds CommonNominalFullCarrier.model m := by
  exact CommonNominalFullCarrier.subtype_refl _

noncomputable def extra : GeneralNominalCandidates.Context :=
  { target with state := { target.state with ordinary := target.state.ordinary ++ [trivial] } }

theorem support : GeneralNominalState.sources extra.state = GeneralNominalState.sources old.state := by
  simp only [extra,GeneralNominalState.sources,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [show GeneralNominalState.atomSources trivial = [] from rfl, List.append_nil]
  rfl

theorem extra_cache : CacheSound installed extra.state := by
  intro obs was
  cases was with
  | nominal i d recorded => exact cert.cache _ (Recorded.nominal (snapshot := target.state) i d recorded)
  | scalar i b recorded => exact cert.cache _ (Recorded.scalar (snapshot := target.state) i b recorded)
  | structural i k cs recorded => exact cert.cache _ (Recorded.structural (snapshot := target.state) i k cs recorded)

noncomputable def extra_cert : Refresh installed extra where
  refines := { cert.refines with
    ordinary := fun a held => List.mem_append_left _ (cert.refines.ordinary a held) }
  interpretation := rfl
  support := fun _ held => support ▸ held
  constraints := by
    intro m valid
    have old := cert.constraints m valid
    refine ⟨old.1,?_⟩
    intro a member
    rcases List.mem_append.mp member with held|added
    · exact old.2 a held
    · cases List.mem_singleton.mp added
      exact trivial_holds m
  cache := extra_cache

noncomputable def varied := refresh installed extra

theorem last_move : Hop installed varied :=
  .refresh extra extra_cert 0 (GeneralRebaseDepthScalar285.present 0 (by decide))
    (GeneralRebaseDepthScalar285.previously_unknown 0 (by decide)) new_zero

theorem alternative : ActualPath initial varied 2 ∧ Halted varied := by
  have first : ActualPath initial installed 1 := .more (.empty _) GeneralDictionaryOutputDepthInstall252.step
  exact ⟨.more first (GeneralRebaseDepthSchedule286.hop_step last_move),
    GeneralRebaseDepthSchedule286.halt_of_done
      (GeneralRebaseDepthPhase286.post_refresh GeneralRebaseDepthPhase286.installed_post last_move)
      ⟨new_zero,new_one⟩⟩

theorem different : varied ≠ refreshed := by
  intro eq
  have lengths := congrArg (fun s : State roles => (snapshot s).ordinary.length) eq
  change (target.state.ordinary ++ [trivial]).length = target.state.ordinary.length at lengths
  simp only [List.length_append,List.length_cons,List.length_nil] at lengths
  omega

theorem not_raw_unique :
    ∃ a b, ActualPath initial a 2 ∧ ActualPath initial b 2 ∧ Halted a ∧ Halted b ∧
      a ≠ b ∧ ReadbackSame a b := by
  have first := alternative
  have second := GeneralRebaseDepthExactEnd286.short_maximal
  exact ⟨varied,refreshed,first.1,second.1,first.2,second.2,different,
    GeneralRebaseDepthConfluence286.maximal_same first.1 second.1 first.2 second.2⟩

end Yulang.GeneralRebaseDepthNonunique286
