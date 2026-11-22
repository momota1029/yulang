import Yulang.GeneralDeclarativeStoredAuthority347

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoredRecordBase347
open GeneralSourceState (equationAtoms equationAtoms_exact)
open GeneralNormalizedObservation (Snapshot Head)
open Core.PresenceGeneration (TyTerm)
open GeneralNominalState (State)
open GeneralDictionaryJournalRefinement228Source (roles constructors)
open GeneralNominalCenters (Site)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty record exactEmpty emptyRecord)

abbrev n := 7
abbrev lo : Fin n := 0
abbrev mid : Fin n := 1
abbrev hi : Fin n := 2
abbrev lf : Fin n := 3
abbrev hf : Fin n := 4
abbrev lt : Fin n := 5
abbrev ht : Fin n := 6

abbrev shapes (k : Fin 3) : GeneralSourceState.Shape n :=
  if k = 0 then .record 7 else if k = 1 then .exactEmpty else .emptyRecord
abbrev lowTerm : TyTerm (Fin n) := .record 7 (.var lf) (.var lt)
abbrev highTerm : TyTerm (Fin n) := .record 7 (.var hf) (.var ht)

def heads (i : Fin n) : GeneralSourceState.Head shapes :=
  if i = lo then .structural 0 (fun j => if j.val = 0 then lf else lt)
  else if i = hi then .structural 0 (fun j => if j.val = 0 then hf else ht)
  else if i = lf ∨ i = lt then .structural 1 (Fin.elim0)
  else if i = hf ∨ i = ht then .structural 2 (Fin.elim0)
  else .unresolved

abbrev parserAtoms : List (PresenceNormalForm.Atom (Fin n)) :=
  equationAtoms lo lowTerm ++ equationAtoms hi highTerm ++ equationAtoms lf .exactEmpty ++
    equationAtoms hf .emptyRecord ++ equationAtoms lt .exactEmpty ++ equationAtoms ht .emptyRecord ++
    [.tyLe (.var lo) (.var mid),.tyLe (.var mid) (.var hi)]

theorem finite_pos (i : Fin n) : i = lo ∨ i = mid ∨ i = hi ∨ i = lf ∨ i = hf ∨ i = lt ∨ i = ht := by
  decide +revert +kernel

abbrev termAt : Fin n → Option (TyTerm (Fin n)) := fun i =>
  if i = lo then some lowTerm else if i = hi then some highTerm
  else if i = lf ∨ i = lt then some .exactEmpty
  else if i = hf ∨ i = ht then some .emptyRecord else none

theorem heads_at (i : Fin n) : (heads i).equation = termAt i := by
  rcases finite_pos i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem parser_authors (i : Fin n) (t : TyTerm (Fin n)) (h : termAt i = some t) :
    equationAtoms i t ⊆ parserAtoms := by
  have completed (i : Fin n) : ∀ x ∈ (termAt i).toList, equationAtoms i x ⊆ parserAtoms := by
    rcases finite_pos i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  exact completed i t (by simp [h])

abbrev base : GeneralSourceState.State where
  slots := n
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := parserAtoms
  kinds := 3
  shapes := shapes
  shapes_injective := by
    intro i j h
    have three (a : Fin 3) : a = 0 ∨ a = 1 ∨ a = 2 := by omega
    rcases three i with rfl|rfl|rfl <;> rcases three j with rfl|rfl|rfl <;> first | rfl | cases h
  heads := heads
  intervals := [(lo,mid),(mid,hi)]
  heads_sound := by
    intro m valid i t observed
    apply (equationAtoms_exact i t m).mp
    exact fun a used => valid _ (parser_authors i t ((heads_at i).symm.trans observed) used)
  intervals_sound := by
    intro m fit p visited
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visited
    rcases visited with rfl|rfl
    · exact fit (.tyLe (.var lo) (.var mid)) (by decide +kernel)
    · exact fit (.tyLe (.var mid) (.var hi)) (by decide +kernel)

abbrev view : Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := fun i => Fin.elim0 i
  canonical := fun i => Fin.elim0 i
  heads := fun _ => .deferred .unresolved
  checked := by intro _ _ e; cases e

abbrev raw : State := GeneralNominalState.embed base view constructors

abbrev site : Site roles :=
  ⟨⟨347,⟨0,fun _ => (0,2),[],by intro _ h; cases h⟩⟩,fun _ => 1⟩

abbrev lowerType : Ty := record 7 exactEmpty exactEmpty
abbrev upperType : Ty := record 7 emptyRecord emptyRecord

abbrev m : Assignment := fun i =>
  (if i = 0 then lowerType else if i = 1 ∨ i = 2 then upperType else
    if i = 3 ∨ i = 5 then exactEmpty else emptyRecord,Common.rowEmpty)

theorem compare_payloads : CommonNominalFullCarrier.Subtype lowerType upperType :=
  CommonNominalFullCarrier.common_record_mono 7 CommonNominalFullCarrier.exactEmpty_below_width
    CommonNominalFullCarrier.exactEmpty_below_width

theorem raw_model : GeneralNominalState.Models raw m := by
  refine ⟨⟨?_,?_,?_⟩,?_ ,PresenceNormalForm.all_nil _ _⟩
  · intro a member
    change a ∈ parserAtoms at member
    simp only [parserAtoms,equationAtoms,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      first | exact CommonNominalFullCarrier.subtype_refl _ | exact compare_payloads
  · intro i t found
    have rel := (heads_at i).symm.trans found
    rcases finite_pos i with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · cases Option.some.inj rel; exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
    · cases rel
    · cases Option.some.inj rel; exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
    · cases Option.some.inj rel; exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
    · cases Option.some.inj rel; exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
    · cases Option.some.inj rel; exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
    · cases Option.some.inj rel; exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
  · intro p h
    simp only [raw,GeneralNominalState.embed,base,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl
    · exact compare_payloads
    · exact CommonNominalFullCarrier.subtype_refl _
  · intro _ _ h; cases h

theorem stored_site (z : Assignment) (valid : GeneralNominalState.Models raw z) : site.Holds z := by
  intro i
  exact ⟨valid.1.2.2 (lo,mid) List.mem_cons_self,
    valid.1.2.2 (mid,hi) (List.mem_cons_of_mem _ List.mem_cons_self)⟩

end Yulang.GeneralDeclarativeStoredRecordBase347
