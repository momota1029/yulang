import Yulang.GeneralRebaseRowTrustedBoundary287

/-! The output has an existing point endpoint one constructor lower, unlike
the old depth-285 example. The blocked requirement is the trusted cache,
not absence of a denoting descriptor. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseRowSemanticMark287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowChildRaw287 (OutputCheck)
open GeneralRebaseRowGeneratedChild287 (current)
open GeneralRebaseRowParentFrame287 (after after_exact)
open GeneralRebaseRowTrustedBoundary287 (forbidden_known)
open GeneralNominalVersionedMixedObservations233 (Refresh CacheSound)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState (Known Descriptor)
open CommonNominalFullCarrier

abbrev outputDescriptor : Descriptor 3 := ⟨0,⟨[.type],0⟩,[.type (1,1)],rfl⟩

noncomputable def marked (choice : Bool) : GeneralNominalState.State :=
  { (current choice).state with
    nominals := fun slot => if slot.val = 2 then some outputDescriptor else (current choice).state.nominals slot
    catalogue := by
      intro slot d held
      split at held
      · cases Option.some.inj held
        rfl
      · exact (current choice).state.catalogue slot d held
    bodies_opaque := by intro _ _ _; rfl }

noncomputable def target (choice : Bool) : GeneralNominalCandidates.Context :=
  { current choice with state := marked choice }

theorem preserved_nominal (choice : Bool) (slot : Fin 3) (d : Descriptor 3)
    (held : (current choice).state.nominals slot = some d) : (marked choice).nominals slot = some d := by
  have notOutput : slot.val ≠ 2 := by
    intro last
    have same : slot = (2 : Fin 3) := Fin.ext last
    subst slot
    cases held
  change (if slot.val = 2 then some outputDescriptor else (current choice).state.nominals slot) = _
  rwa [ite_eq_right notOutput]

theorem known_output (choice : Bool) : Known (marked choice) 2 :=
  ⟨(2 : Fin 3),rfl,Or.inr ⟨outputDescriptor,rfl⟩⟩

theorem preserved_known (choice : Bool) (n : Nat) :
    Known (current choice).state n → Known (marked choice) n := by
  rintro ⟨slot,keys,head|⟨d,prior⟩⟩
  · exact ⟨slot,keys,Or.inl head⟩
  · exact ⟨slot,keys,Or.inr ⟨d,preserved_nominal choice slot d prior⟩⟩

noncomputable def refines (choice : Bool) :
    GeneralNominalRefinements.Refines (current choice).state (marked choice) where
  base := (GeneralNominalRefinements.refl (current choice).state).base
  heads := (GeneralNominalRefinements.refl (current choice).state).heads
  nominals := by
    intro slot d prior
    exact preserved_nominal choice slot _ ((GeneralNominalRefinements.refl (current choice).state).nominals slot d prior)
  ordinary := fun _ held => held
  known := preserved_known choice
  reserved := fun _ held => held
  allocated := fun _ held => held
  seed := rfl
  constructors := rfl

theorem output_meaning (choice : Bool) (m : Assignment)
    (valid : GeneralNominalVersionedJournal232.Models (after choice) m) :
    GeneralNominalState.Denotes (marked choice).base m (2 : Fin 3) outputDescriptor := by
  have both := (after_exact choice m).mp valid
  have raised : Equivalent (F (m 1).1) (F (F (m 0).1)) :=
    GeneralNominalCenteredHeadMatCompilerSemantics.nominal_congr 0 (.cons both.1.2 .nil)
  exact ⟨[.inl (m 1).1],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,
    subtype_trans both.2.1 raised.2,subtype_trans raised.1 both.2.2⟩

theorem all_models_support (choice : Bool) (m : Assignment)
    (valid : GeneralNominalVersionedJournal232.Models (after choice) m) :
    GeneralNominalState.Models (marked choice) m := by
  refine ⟨valid.1.1.1,?_,valid.1.1.2.2⟩
  intro slot d held
  change (if slot.val = 2 then some outputDescriptor else (current choice).state.nominals slot) = some d at held
  split at held
  · rename_i same
    have id : slot = (2 : Fin 3) := Fin.ext same
    subst slot
    cases Option.some.inj held
    exact output_meaning choice m valid
  · exact valid.1.1.2.1 slot d held

theorem no_cache (choice : Bool) : ¬ CacheSound (after choice) (marked choice) :=
  fun cache => forbidden_known choice (marked choice) cache 2 (by decide) (known_output choice)

theorem not_certified_mark (choice : Bool) : ¬ Nonempty (Refresh (after choice) (target choice)) := by
  rintro ⟨certificate⟩
  exact no_cache choice certificate.cache

theorem all_except_trust (choice : Bool) :
    (∃ _ : GeneralNominalRefinements.Refines (current choice).state (target choice).state, True) ∧
    (target choice).interpretation = (current choice).interpretation ∧
    GeneralNominalState.sources (target choice).state = GeneralNominalState.sources (current choice).state ∧
    (∀ m, GeneralNominalVersionedJournal232.Models (after choice) m →
      GeneralNominalState.Models (target choice).state m) ∧
    ¬ Nonempty (Refresh (after choice) (target choice)) :=
  ⟨⟨refines choice,trivial⟩,rfl,rfl,all_models_support choice,not_certified_mark choice⟩

end Yulang.GeneralRebaseRowSemanticMark287
