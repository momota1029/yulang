import Yulang.GeneralDictionarySharingObstruction217
import Yulang.GeneralNominalCenteredHeadMatStepRefresh

/-! Point nominal observations require every type parameter to be represented
by an existing source slot. This is a checkable obstruction to reobservation. -/
namespace Yulang.GeneralDictionaryPointObservation217
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState (Fits FitsAll Denotes)
open GeneralNominalReobservationSteps (PointParameter PointDescriptor)

def Represented (base : GeneralSourceState.State) (model : Assignment) (value : Ty) : Prop :=
  ∃ slot : Fin base.slots, Equivalent (model (base.source slot)).1 value

theorem point_parameter (base : GeneralSourceState.State) (model : Assignment)
    (parameter : GeneralNominalState.Parameter base.slots) (value : Ty)
    (point : PointParameter parameter) (fits : Fits base model parameter (.inl value)) :
    Represented base model value := by
  cases parameter with
  | type bounds =>
    change bounds.1 = bounds.2 at point
    refine ⟨bounds.1,fits.1,?_⟩
    simpa only [← point] using fits.2
  | row bounds => cases fits

theorem point_arguments (base : GeneralSourceState.State) (model : Assignment)
    (parameters : List (GeneralNominalState.Parameter base.slots)) (arguments : List Argument)
    (points : ∀ parameter ∈ parameters, PointParameter parameter)
    (fits : FitsAll base model parameters arguments) (value : Ty) (member : Sum.inl value ∈ arguments) :
    Represented base model value := by
  induction fits with
  | nil => cases member
  | @cons parameter argument parameters arguments first rest ih =>
    rcases List.mem_cons.mp member with equal | tail
    · subst argument; exact point_parameter base model parameter value (points _ (by simp)) first
    · exact ih (fun p hp => points p (List.mem_cons_of_mem _ hp)) tail

theorem denotes_represents (base : GeneralSourceState.State) (model : Assignment)
    (slot : Fin base.slots) (descriptor : GeneralNominalState.Descriptor base.slots)
    (point : PointDescriptor descriptor) (denotes : Denotes base model slot descriptor)
    (name : Nat) (arguments : List Argument)
    (known : Equivalent (model (base.source slot)).1 (nominal name arguments))
    (value : Ty) (member : Sum.inl value ∈ arguments) : Represented base model value := by
  obtain ⟨actual,fits,equal⟩ := denotes
  have invariant := (nominal_regular_invariant_exact _ _ _ _).mp (subtype_trans equal.2 known.1)
  obtain ⟨index,bound,found⟩ := List.mem_iff_getElem.mp member
  have inside : index < actual.length := by rw [invariant.2.1]; exact bound
  have atActual : actual[index]? = some actual[index] := List.getElem?_eq_getElem inside
  have atTarget : arguments[index]? = some (.inl value) := by rw [List.getElem?_eq_getElem bound,found]
  have equivalent := invariant.2.2 index actual[index] (.inl value) atActual atTarget
  cases item : actual[index] with
  | inr row => simp only [item,ArgumentEquivalent] at equivalent
  | inl type =>
    have represented := point_arguments base model descriptor.arguments actual point fits type
      (List.mem_iff_getElem.mpr ⟨index,inside,item⟩)
    obtain ⟨source,sourceEqual⟩ := represented
    have same : Equivalent type value := by simpa only [item,ArgumentEquivalent] using equivalent
    exact ⟨source,subtype_trans sourceEqual.1 same.1,subtype_trans same.2 sourceEqual.2⟩

theorem cached_point_represents {roles : Roles.RoleDecls}
    (state : GeneralNominalCenteredHeadMatStepJournal.State roles) (snapshot : GeneralNominalState.State)
    (model : Assignment) (valid : GeneralNominalCenteredHeadMatStepJournal.Models state model)
    (cache : GeneralNominalCenteredHeadMatStepObservations.CacheSound state snapshot)
    (slot : Fin snapshot.base.slots) (descriptor : GeneralNominalState.Descriptor snapshot.base.slots)
    (recorded : snapshot.nominals slot = some descriptor) (point : PointDescriptor descriptor)
    (name : Nat) (arguments : List Argument)
    (known : Equivalent (model (snapshot.base.source slot)).1 (nominal name arguments))
    (value : Ty) (member : Sum.inl value ∈ arguments) : Represented snapshot.base model value :=
  denotes_represents snapshot.base model slot descriptor point
    (GeneralNominalCenteredHeadMatStepObservations.cache_sound cache (.nominal slot descriptor recorded) valid)
    name arguments known value member

theorem refresh_point_excluded {roles : Roles.RoleDecls}
    (state : GeneralNominalCenteredHeadMatStepJournal.State roles) (context : GeneralNominalCandidates.Context)
    (model : Assignment) (valid : GeneralNominalCenteredHeadMatStepJournal.Models state model)
    (certificate : GeneralNominalCenteredHeadMatStepRefresh.Refresh state context)
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor)
    (name : Nat) (arguments : List Argument)
    (known : Equivalent (model (context.state.base.source slot)).1 (nominal name arguments))
    (value : Ty) (member : Sum.inl value ∈ arguments)
    (missing : ∀ source ∈ GeneralNominalState.sources state.core.erased.current.context.state,
      ¬ Equivalent (model source).1 value) : ¬ PointDescriptor descriptor := by
  intro point
  obtain ⟨source,equal⟩ := cached_point_represents state context.state model valid certificate.cache
    slot descriptor recorded point name arguments known value member
  apply missing (context.state.base.source source) (certificate.support _ ?_) equal
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨source,rfl⟩)))

theorem reobserve_no_improvement {roles : Roles.RoleDecls}
    (state : GeneralNominalCenteredHeadMatStepJournal.State roles)
    (model : Assignment) (valid : GeneralNominalCenteredHeadMatStepJournal.Models state model)
    (missing : ∀ slot, ¬ GeneralNominalReobservationSteps.PointAt state.core.erased.current.context.state slot →
      (∃ descriptor, state.core.erased.current.context.state.nominals slot = some descriptor) →
      ∃ name arguments value,
        Equivalent (model (state.core.erased.current.context.state.base.source slot)).1 (nominal name arguments) ∧
        Sum.inl value ∈ arguments ∧ ¬ Represented state.core.erased.current.context.state.base model value)
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current)
    (certificate : GeneralNominalCenteredHeadMatStepRefresh.Reobserve state revision) :
    ¬ GeneralNominalReobservationSteps.Improves revision := by
  rintro ⟨_,slot,nonpoint,descriptor,recorded,point⟩
  have prior : ∃ descriptor, state.core.erased.current.context.state.nominals slot = some descriptor := by
    cases old : state.core.erased.current.context.state.nominals slot with
    | some prior => exact ⟨prior,rfl⟩
    | none =>
      have none := (revision.domain slot).mpr old
      change revision.entries slot = some descriptor at recorded
      rw [none] at recorded
      cases recorded
  obtain ⟨name,arguments,value,known,member,absent⟩ := missing slot nonpoint prior
  exact absent (cached_point_represents state revision.snapshot model valid certificate.cache
    slot descriptor recorded point name arguments known value member)

end Yulang.GeneralDictionaryPointObservation217
