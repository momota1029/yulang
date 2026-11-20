import Yulang.GeneralRebaseRowLedgerNames288

/-! Characterize the newly certifiable point descriptor by assignment
semantics, not by a fixed layout of the proposed snapshot. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28800
set_option maxHeartbeats 18000000
namespace Yulang.GeneralRebaseRowRefreshShape288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowLedger288 (supplemented models_eq)
open GeneralRebaseRowParentFrame287 (after_model)
open GeneralRebaseRowGeneratedChild287 (current)
open GeneralRebaseRowSemanticMark287 (outputDescriptor)
open GeneralNominalVersionedMixedObservations233 (Refresh cache_sound)
open GeneralDictionaryInspectionHeads215
open GeneralNominalFiniteHeadInversion (head)
open GeneralNominalState (Known Denotes Descriptor Fits FitsAll)
open CommonNominalFullCarrier

abbrev mu := model Common.rowEmpty
abbrev point := F (R Common.rowEmpty)

theorem nominal_reverse (name other : Nat) (first last : List Argument)
    (h : Subtype (nominal name first) (nominal other last)) :
    Subtype (nominal other last) (nominal name first) := by
  obtain ⟨id,size,same⟩ := (nominal_regular_invariant_exact ..).mp h
  apply (nominal_regular_invariant_exact ..).mpr
  refine ⟨id.symm,size.symm,?_⟩
  intro i a b inA inB
  have pair := same i b a inB inA
  cases a <;> cases b
  · exact ⟨pair.2,pair.1⟩
  · exact pair
  · exact pair
  · exact pair.symm

theorem any_comparable_is_middle (n : Nat)
    (comparable : Subtype (mu n).1 point ∨ Subtype point (mu n).1) : n = 1 := by
  by_cases zero : n = 0
  · subst n
    rcases comparable with le | le
    · exact ((by decide : (6 : Nat) ≠ 0) ((nominal_regular_invariant_exact 6 0 _ _).mp le).1).elim
    · exact ((by decide : (0 : Nat) ≠ 6) ((nominal_regular_invariant_exact 0 6 _ _).mp le).1).elim
  by_cases one : n = 1
  · exact one
  by_cases two : n = 2
  · subst n
    have negative : ¬ Subtype (F point) point := by
      intro le
      have inside := ((nominal_regular_invariant_exact 0 0 _ _).mp le).2.2 0
        (.inl point) (.inl (R Common.rowEmpty)) rfl rfl
      exact (by decide : (0 : Nat) ≠ 6) ((nominal_regular_invariant_exact 0 6 _ _).mp inside.1).1
    rcases comparable with le | le
    · exact (negative le).elim
    · exact (negative (nominal_reverse 0 0 _ _ le)).elim
  have compute : (mu n).1 = .base .int := by simp [mu,GeneralRebaseRowChildSource287.model,zero,one,two]
  rw [compute] at comparable
  rcases comparable with le | le
  · exact nomatch (tag_subtype (tagged_scalar .int) (tagged_nominal 0 [.inl (R Common.rowEmpty)]) le)
  · exact nomatch (tag_subtype (tagged_nominal 0 [.inl (R Common.rowEmpty)]) (tagged_scalar .int) le)

theorem catalogue_names_key (key : Nat) (d : GeneralDeclarationPatterns.Constructor)
    (visible : constructors key = some d) : d.name = key := by
  unfold constructors at visible
  split at visible
  · rename_i six
    cases Option.some.inj visible
    exact six.symm
  · cases Option.some.inj visible
    rfl

theorem singleton_type_fits (context : GeneralNominalCandidates.Context)
    (params : List (GeneralNominalState.Parameter context.state.base.slots))
    (value : Ty) (same : Equivalent point value) (fits : FitsAll context.state.base mu params [.inl value]) :
    ∃ bounds, params = [.type bounds] ∧ context.state.base.source bounds.1 = 1 ∧
      context.state.base.source bounds.2 = 1 := by
  cases fits with
  | cons held rest =>
    cases rest
    rename_i param
    cases param with
    | row bounds => cases held
    | type bounds =>
      exact ⟨bounds,rfl,
        any_comparable_is_middle (context.state.base.source bounds.1) (.inl (subtype_trans held.1 same.2)),
        any_comparable_is_middle (context.state.base.source bounds.2) (.inr (subtype_trans same.1 held.2))⟩

theorem only_descriptor (context : GeneralNominalCandidates.Context)
    (certificate : Refresh supplemented context) {site : Fin context.state.base.slots}
    (source : context.state.base.source site = 2) {desc : Descriptor context.state.base.slots}
    (seen : context.state.nominals site = some desc) :
    desc = GeneralNominalRefinements.renameDescriptor certificate.refines.base.embed outputDescriptor := by
  have valid := (models_eq mu).mpr (after_model true Common.rowEmpty)
  obtain ⟨values,fits,described⟩ := cache_sound certificate.cache (.nominal site desc seen) valid
  rw [source] at described
  have invariant := (nominal_regular_invariant_exact 0 desc.declaration.name [.inl point] values).mp described.1
  have key : desc.constructor = 0 := by
    have existing := context.state.catalogue site desc seen
    rw [certificate.refines.constructors] at existing
    exact (catalogue_names_key _ _ existing).symm.trans invariant.1.symm
  have declaration : desc.declaration = outputDescriptor.declaration := by
    have existing := context.state.catalogue site desc seen
    rw [certificate.refines.constructors,key] at existing
    exact (Option.some.inj existing).symm
  have count : values.length = 1 := invariant.2.1.symm
  cases values with
  | nil => cases count
  | cons value rest =>
    have none : rest = [] := List.length_eq_zero_iff.mp (Nat.succ.inj count)
    subst rest
    have equal := invariant.2.2 0 (.inl point) value rfl rfl
    cases value with
    | inr row => cases equal
    | inl value =>
      obtain ⟨bounds,ports,lower,upper⟩ := singleton_type_fits context desc.arguments value equal fits
      have lo : bounds.1 = certificate.refines.base.embed (1 : Fin 3) :=
        context.state.base.source_injective (lower.trans (certificate.refines.base.source (1 : Fin 3)).symm)
      have hi : bounds.2 = certificate.refines.base.embed (1 : Fin 3) :=
        context.state.base.source_injective (upper.trans (certificate.refines.base.source (1 : Fin 3)).symm)
      rw [show bounds = (certificate.refines.base.embed (1 : Fin 3),
        certificate.refines.base.embed (1 : Fin 3)) from Prod.ext lo hi] at ports
      cases desc with
      | mk name decl args layout =>
        change name = 0 at key
        change decl = outputDescriptor.declaration at declaration
        change args = _ at ports
        subst name
        subst decl
        subst args
        rfl

theorem actually_nominal (context : GeneralNominalCandidates.Context)
    (certificate : Refresh supplemented context)
    (known : Known context.state 2) :
    context.state.nominals (certificate.refines.base.embed (2 : Fin 3)) =
      some (GeneralNominalRefinements.renameDescriptor certificate.refines.base.embed outputDescriptor) := by
  obtain ⟨slot,source,readable | ⟨desc,seen⟩⟩ := known
  · cases tested : context.state.view.heads slot with
    | deferred reason =>
      simp [GeneralNormalizedObservation.Snapshot.graph,GeneralNormalizedObservation.Head.node,tested] at readable
    | scalar scalar =>
      let picked := GeneralNominalSupport.Head.scalar slot scalar tested
      have actual := cache_sound certificate.cache (GeneralNominalSupport.head_recorded picked)
        ((models_eq mu).mpr (after_model true Common.rowEmpty))
      have held := GeneralDictionaryGroundCopy218Refresh.head_holds picked actual
      rw [source] at held
      have same := tag_subtype (tagged_test _ held) (tagged_nominal 0 [.inl point]) (subtype_refl _)
      cases same
    | structural kind children =>
      let picked := GeneralNominalSupport.Head.structural slot kind children tested
      have actual := cache_sound certificate.cache (GeneralNominalSupport.head_recorded picked)
        ((models_eq mu).mpr (after_model true Common.rowEmpty))
      have held := GeneralDictionaryGroundCopy218Refresh.head_holds picked actual
      rw [source] at held
      have same := tag_subtype (tagged_test _ held) (tagged_nominal 0 [.inl point]) (subtype_refl _)
      cases shape : context.state.view.shapes kind <;> simp [shape,head] at same
  · have equal := only_descriptor context certificate source seen
    have whereAt : slot = certificate.refines.base.embed (2 : Fin 3) :=
      context.state.base.source_injective (source.trans (certificate.refines.base.source (2 : Fin 3)).symm)
    rwa [← whereAt,← equal]

end Yulang.GeneralRebaseRowRefreshShape288
