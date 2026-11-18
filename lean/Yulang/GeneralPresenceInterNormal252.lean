import Yulang.GeneralPresenceDuplicateUnion251
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralPresenceInterNormal252
open Core.PresenceGeneration
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralPresenceUsedSupport245 (typedReads)

def atoms : TyTerm Nat → List (TyTerm Nat)
 | .inter first last => atoms first ++ atoms last
 | term => [term]

def fold : List (TyTerm Nat) → TyTerm Nat
 | [] => .top
 | [term] => term
 | first :: rest => .inter first (fold rest)

def canonical (pool terms : List (TyTerm Nat)) : List (TyTerm Nat) :=
 pool.filter (fun term => term ∈ terms)

def normalize (pool : List (TyTerm Nat)) (term : TyTerm Nat) : TyTerm Nat := fold (canonical pool (atoms term))

theorem atoms_nonempty (term : TyTerm Nat) : atoms term ≠ [] := by
 induction term <;> simp_all [atoms]

theorem atoms_flat (term atom : TyTerm Nat) (member : atom ∈ atoms term) : atoms atom = [atom] := by
 induction term <;> simp_all [atoms]
 case inter first last ihFirst ihLast =>
   rcases member with one | two
   · exact ihFirst one
   · exact ihLast two

theorem canonical_mem (pool terms : List (TyTerm Nat)) (term : TyTerm Nat) :
 term ∈ canonical pool terms ↔ term ∈ pool ∧ term ∈ terms := by simp [canonical]

theorem canonical_exact (pool terms : List (TyTerm Nat)) (supported : terms ⊆ pool) (term : TyTerm Nat) :
 term ∈ canonical pool terms ↔ term ∈ terms :=
 ⟨fun member => (canonical_mem ..).mp member |>.2,fun member => (canonical_mem ..).mpr ⟨supported member,member⟩⟩

theorem canonical_nonempty (pool terms : List (TyTerm Nat)) (supported : terms ⊆ pool) (nonempty : terms ≠ []) :
 canonical pool terms ≠ [] := by
 intro empty
 apply nonempty
 apply List.eq_nil_iff_forall_not_mem.mpr
 intro term member
 have present := (canonical_exact pool terms supported term).mpr member
 rw [empty] at present
 cases present

theorem fold_exact (terms : List (TyTerm Nat)) (nonempty : terms ≠ []) (assignment : Assignment) (value : Ty) :
 Subtype value ((fold terms).eval model assignment) ↔ ∀ term ∈ terms, Subtype value (term.eval model assignment) := by
 induction terms with
 | nil => exact False.elim (nonempty rfl)
 | cons first rest ih =>
   cases rest with
   | nil => simp [fold]
   | cons next tail =>
     change Subtype value (.inter (first.eval model assignment) ((fold (next::tail)).eval model assignment)) ↔ _
     rw [common_inter_is_meet,ih (by simp)]
     simp

theorem atoms_exact (term : TyTerm Nat) (assignment : Assignment) (value : Ty) :
 Subtype value (term.eval model assignment) ↔ ∀ atom ∈ atoms term, Subtype value (atom.eval model assignment) := by
 induction term <;> simp_all [atoms]
 case inter first last ihFirst ihLast =>
   change Subtype value (.inter (first.eval model assignment) (last.eval model assignment)) ↔ _
   rw [common_inter_is_meet,ihFirst,ihLast]
   constructor
   · rintro ⟨one,two⟩ atom (member | member)
     · exact one atom member
     · exact two atom member
   · intro held
     exact ⟨fun atom member => held atom (Or.inl member),fun atom member => held atom (Or.inr member)⟩

theorem equivalent (pool : List (TyTerm Nat)) (term : TyTerm Nat) (supported : atoms term ⊆ pool) (assignment : Assignment) :
 Equivalent ((normalize pool term).eval model assignment) (term.eval model assignment) := by
 have nonempty := canonical_nonempty pool (atoms term) supported (atoms_nonempty term)
 have exactValue (value : Ty) : Subtype value ((normalize pool term).eval model assignment) ↔ Subtype value (term.eval model assignment) := by
   rw [normalize,fold_exact _ nonempty,atoms_exact]
   exact ⟨fun held atom member => held atom ((canonical_exact _ _ supported _).mpr member),
     fun held atom member => held atom ((canonical_exact _ _ supported _).mp member)⟩
 exact ⟨(exactValue _).mp (subtype_refl _),(exactValue _).mpr (subtype_refl _)⟩

theorem atoms_fold (terms : List (TyTerm Nat)) (nonempty : terms ≠ [])
 (flat : ∀ term ∈ terms, atoms term = [term]) : atoms (fold terms) = terms := by
 induction terms with
 | nil => exact False.elim (nonempty rfl)
 | cons first rest ih =>
   cases rest with
   | nil => exact flat first (by simp)
   | cons next tail =>
     simp only [fold,atoms,flat first (by simp)]
     rw [ih (by simp) (fun term member => flat term (by simp [member]))]
     rfl

theorem canonical_idempotent (pool terms : List (TyTerm Nat)) : canonical pool (canonical pool terms) = canonical pool terms := by
 unfold canonical
 apply List.filter_congr
 intro term member
 simp [member]

theorem idempotent (pool : List (TyTerm Nat)) (term : TyTerm Nat) (supported : atoms term ⊆ pool) :
 normalize pool (normalize pool term) = normalize pool term := by
 have nonempty := canonical_nonempty pool (atoms term) supported (atoms_nonempty term)
 have flat : ∀ atom ∈ canonical pool (atoms term), atoms atom = [atom] :=
   fun atom member => atoms_flat term atom ((canonical_mem ..).mp member).2
 unfold normalize
 rw [atoms_fold _ nonempty flat,canonical_idempotent]

theorem fold_reads (terms : List (TyTerm Nat)) (name : Nat) (member : name ∈ typedReads (fold terms)) :
 ∃ term ∈ terms, name ∈ typedReads term := by
 induction terms with
 | nil => cases member
 | cons first rest ih =>
   cases rest with
   | nil => exact ⟨first,by simp,member⟩
   | cons next tail =>
     rcases List.mem_append.mp member with firstRead | laterRead
     · exact ⟨first,by simp,firstRead⟩
     · obtain ⟨term,present,read⟩ := ih laterRead
       exact ⟨term,by simp [present],read⟩

theorem no_private_reads (pool : List (TyTerm Nat)) (term : TyTerm Nat) (privateName : Nat)
 (separated : ∀ atom ∈ pool, privateName ∉ typedReads atom) :
 privateName ∉ typedReads (normalize pool term) := by
 intro member
 obtain ⟨atom,present,read⟩ := fold_reads _ _ member
 exact separated atom ((canonical_mem ..).mp present).1 read

theorem canonical_nodup (pool terms : List (TyTerm Nat)) (unique : pool.Nodup) :
 (canonical pool terms).Nodup := List.Pairwise.sublist List.filter_sublist unique

theorem fold_all_reads (terms : List (TyTerm Nat)) (name : Nat)
 (member : name ∈ GeneralPresenceSubstitutionSupport244.typeSources (fold terms)) :
 ∃ term ∈ terms, name ∈ GeneralPresenceSubstitutionSupport244.typeSources term := by
 induction terms with
 | nil => cases member
 | cons first rest ih =>
   cases rest with
   | nil => exact ⟨first,by simp,member⟩
   | cons next tail =>
     rcases List.mem_append.mp member with firstRead | laterRead
     · exact ⟨first,by simp,firstRead⟩
     · obtain ⟨term,present,read⟩ := ih laterRead
       exact ⟨term,by simp [present],read⟩

theorem no_private_all_reads (pool : List (TyTerm Nat)) (term : TyTerm Nat) (privateName : Nat)
 (separated : ∀ atom ∈ pool, privateName ∉ GeneralPresenceSubstitutionSupport244.typeSources atom) :
 privateName ∉ GeneralPresenceSubstitutionSupport244.typeSources (normalize pool term) := by
 intro member
 obtain ⟨atom,present,read⟩ := fold_all_reads _ _ member
 exact separated atom ((canonical_mem ..).mp present).1 read

theorem atom_reads (term atom : TyTerm Nat) (present : atom ∈ atoms term) :
 typedReads atom ⊆ typedReads term := by
 induction term <;> simp_all [atoms,typedReads]
 case inter first last ihFirst ihLast =>
   intro name member
   rcases present with one | two
   · exact List.mem_append_left _ (ihFirst one member)
   · exact List.mem_append_right _ (ihLast two member)

theorem normalized_reads (pool : List (TyTerm Nat)) (term : TyTerm Nat) :
 typedReads (normalize pool term) ⊆ typedReads term := by
 intro name member
 obtain ⟨atom,present,read⟩ := fold_reads _ _ member
 exact atom_reads term atom ((canonical_mem ..).mp present).2 read
end Yulang.GeneralPresenceInterNormal252
