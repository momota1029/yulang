import Yulang.GeneralMixedCompoundSourcePrefix308

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralMixedCompoundFiveSlotDescriptor308
open GeneralDictionaryJournalRefinement228Source (base snapshot foo constructors)
open GeneralDictionaryJournalRefinement228Reobserve (exactCopy)
open GeneralDictionaryOptionalInstall229 (model)
open GeneralMixedCompoundSourcePrefix308 (classified)
open GeneralMixedCompoundUpperTypes307 (kind meaning equiv_kind Kind)
open GeneralNominalState (Descriptor Denotes Fits FitsAll Parameter)
open GeneralNominalReobservationSteps (PointParameter PointDescriptor)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)
open CommonNominalFullCarrier

theorem record_exact (i : Fin 5) (value : Equivalent (model i.val).1 .emptyRecord) : i = 2 := by
  have normal := classified i.val (by have h := i.isLt; omega)
  rw [normal] at value
  have label : kind i.val = .width := equiv_kind value
  have width : i.val = 2 := by
    rcases GeneralMixedCompoundSourcePrefix308.initial_names i.val (by have h := i.isLt; omega) with h|h|h|h|h <;>
      rw [h] at label <;> (first | exact h | cases label)
  exact Fin.ext width

theorem argument_exact (p : Parameter 5) (v : Argument)
    (point : PointParameter p) (fits : Fits base model p v)
    (equivalent : ArgumentEquivalent (.inl .emptyRecord) v) :
    p = .type ((2 : Fin 5),2) := by
  cases v with
  | inr row => cases equivalent
  | inl ty =>
    cases p with
    | row bound => cases fits
    | type bounds =>
      have aligned : bounds.1 = bounds.2 := point
      have read : Equivalent (model bounds.1.val).1 .emptyRecord := by
        exact equivalent_trans ⟨fits.1,by rw [aligned]; exact fits.2⟩
          ⟨equivalent.2,equivalent.1⟩
      have first := record_exact bounds.1 read
      have last := aligned.symm.trans first
      rcases bounds with ⟨lower,upper⟩
      simp only at first last
      subst lower; subst upper; rfl

theorem list_two {α : Type} (xs : List α) (equal : xs.length = 2) :
    ∃ one two, xs = [one,two] := by
  cases xs with
  | nil => cases equal
  | cons one rest =>
    cases rest with
    | nil => cases equal
    | cons two tail =>
      have empty : tail = [] := List.length_eq_zero_iff.mp (by simp_all)
      subst tail; exact ⟨one,two,rfl⟩

theorem fits_forced (xs : List Argument) (d : Descriptor 5)
    (same : ArgumentsEquivalent [.inl .emptyRecord,.inl .emptyRecord] xs)
    (length : xs.length = 2) (fits : FitsAll base model d.arguments xs)
    (point : PointDescriptor d) :
    d.arguments = [.type ((2 : Fin 5),2),.type (2,2)] := by
  obtain ⟨one,two,rfl⟩ := list_two xs length
  have first := same 0 (.inl .emptyRecord) one rfl rfl
  have second := same 1 (.inl .emptyRecord) two rfl rfl
  have paramsLen := (GeneralNominalLinearMaterializationFacts.fitsAll_length base model d.arguments [one,two] fits).symm
  obtain ⟨p,q,params⟩ := list_two d.arguments paramsLen
  obtain ⟨u,atU,fitU⟩ := GeneralNominalIntervalLaws.fitsAll_at base model d.arguments [one,two] fits 0 p
    (by rw [params]; rfl)
  obtain ⟨v,atV,fitV⟩ := GeneralNominalIntervalLaws.fitsAll_at base model d.arguments [one,two] fits 1 q
    (by rw [params]; rfl)
  have uEq : one = u := Option.some.inj atU
  have vEq : two = v := Option.some.inj atV
  subst u; subst v
  have pMem : p ∈ d.arguments := by rw [params]; exact List.mem_cons_self
  have qMem : q ∈ d.arguments := by rw [params]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have a := argument_exact _ _ (point _ pMem) fitU first
  have b := argument_exact _ _ (point _ qMem) fitV second
  rw [params,a,b]

theorem descriptor_exact (i : Fin 5) (d : Descriptor 5)
    (what : i = 0 ∨ i = 1) (supported : constructors d.constructor = some d.declaration)
    (points : PointDescriptor d) (sound : Denotes base model i d) : d = exactCopy := by
  obtain ⟨xs,fits,equal⟩ := sound
  have core : (model (base.source i)).1 = foo := by rcases what with rfl|rfl <;> rfl
  rw [core] at equal
  have payload := (nominal_regular_invariant_exact 0 d.declaration.name
    [.inl .emptyRecord,.inl .emptyRecord] xs).mp equal.1
  have args := fits_forced xs d payload.2.2 payload.2.1.symm fits points
  rcases d with ⟨ctor,decl,parameters,layout⟩
  change parameters = _ at args
  subst parameters
  have value : (⟨if ctor = 0 then [.type,.type] else [],ctor⟩ :
      GeneralDeclarationPatterns.Constructor) = decl := Option.some.inj supported
  have names : (0 : Nat) = decl.name := payload.1
  subst decl
  have ctorEq : (0 : Nat) = ctor := names
  subst ctor
  rfl

end Yulang.GeneralMixedCompoundFiveSlotDescriptor308
