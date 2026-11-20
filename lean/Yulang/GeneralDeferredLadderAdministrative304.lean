import Yulang.GeneralDeferredLadderResnapshot304
import Yulang.GeneralNominalVersionedMixedTerminalStable234

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderAdministrative304
open GeneralDeferredLadderResnapshot304 (HeadView)
open GeneralDeferredLadderOperationalView304 (alias_forward frame_forward)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedTerminalStable234 (HeadlessUnknown EqualityClosed)
open GeneralNominalVersionedCycles232 (Cyclic full_models_only)
open GeneralNominalVersionedDiagnostic232 (AdministrativeReady)

variable {roles : Roles.RoleDecls} {a b : State roles}

theorem model_eq (ab : HeadView a b) : Models a = Models b :=
  funext fun m => propext (ab.raw.models m)

theorem headless_forward (ab : HeadView a b) (given : HeadlessUnknown a) : HeadlessUnknown b := by
  obtain ⟨m,ma,props⟩ := given
  refine ⟨m,(ab.raw.models m).mp ma,?_⟩
  rw [ab.context] at props
  exact props

theorem equality_forward (ab : HeadView a b) (given : EqualityClosed a) : EqualityClosed b := by
  intro first last one two equal
  have old : GeneralNominalVersionedMixedKernel234.Equal a first last :=
    fun m ma => equal m ((ab.raw.models m).mp ma)
  have closed := given first last (ab.context.symm ▸ one) (ab.context.symm ▸ two) old
  intro m valid
  exact closed m (ab.context.symm ▸ valid)

theorem administrative_forward (ab : HeadView a b) (given : AdministrativeReady a root) :
    AdministrativeReady b root := by
  unfold AdministrativeReady at given ⊢
  rw [ab.centers] at given
  refine ⟨given.1,?_⟩
  intro first ha same last hb eq
  rw [← model_eq ab] at eq
  exact alias_forward ab.raw (given.2 first ha same last hb eq)

theorem root_cycle_backward (ab : HeadView a b) (given : GeneralNominalVersionedCycles232.RootCycle b root) :
    GeneralNominalVersionedCycles232.RootCycle a root := by
  rcases given with ⟨i,hit⟩ | ⟨s,member,eq,i,hit⟩
  · exact Or.inl ⟨i,(full_models_only (model_eq ab)).mpr hit⟩
  · exact Or.inr ⟨s,ab.centers.symm ▸ member,eq,i,(full_models_only (model_eq ab)).mpr hit⟩

theorem candidate_cycle_backward (ab : HeadView a b)
    (given : GeneralNominalVersionedCycles232.CandidateCycle registry b root) :
    GeneralNominalVersionedCycles232.CandidateCycle registry a root := by
  obtain ⟨plan,f,position,listed,cyclic⟩ := given
  exact ⟨plan,frame_forward ab.raw.symm ab.context.symm ab.centers.symm f,
    position,listed,(full_models_only (model_eq ab)).mpr cyclic⟩

theorem known_forward (ab : HeadView a b)
    (given : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry a root) :
    B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry b root := by
  obtain ⟨linked,notRoot,notCandidate,notPending⟩ := given
  refine ⟨?_,?_,?_,?_⟩
  · intro pending
    apply linked
    change GeneralNominalState.RootPending a.core.erased.current.context.state
      (GeneralNominalVersionedCandidates231.inputs root).demand
    rw [ab.context]
    exact pending
  · rintro (raw | semantic)
    · exact notRoot (Or.inl (ab.context.symm ▸ raw))
    · exact notRoot (Or.inr (root_cycle_backward ab semantic))
  · rintro (raw | semantic)
    · exact notCandidate (Or.inl (ab.context.symm ▸ raw))
    · exact notCandidate (Or.inr (candidate_cycle_backward ab semantic))
  · rintro (pending | notAdmin)
    · exact notPending (Or.inl (ab.context.symm ▸ pending))
    · apply notAdmin
      apply administrative_forward ab
      by_cases ready : AdministrativeReady a root
      · exact ready
      · exact False.elim (notPending (Or.inr ready))

end Yulang.GeneralDeferredLadderAdministrative304
