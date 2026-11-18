import Yulang.GeneralNominalSourceBasis255
import Yulang.GeneralNominalViewFixed255
namespace Yulang.GeneralNominalCanonicalBasis255
open Core.PresenceGeneration
open GeneralDeclarations GeneralSourceDictionaries
open GeneralPresenceCheckedNormal252 (Side)
open GeneralNominalRebaseRawView243

theorem dedup_nodup (pool : List (TyTerm Nat)) : pool.eraseDups.Nodup := by
 cases pool with
 | nil => exact List.nodup_nil
 | cons first rest =>
   rw [List.eraseDups_cons]
   apply List.nodup_cons.mpr
   exact ⟨by simp,dedup_nodup (rest.filter (fun term => !term == first))⟩
termination_by pool.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- The working basis is deduplicated once, before normalizing fields.
The raw source/public concatenation is retained as a separate support witness. -/
def basis (registry : Registry) (context : GeneralNominalCandidates.Context) (keys : List (Nat × Nat)) : List (TyTerm Nat) :=
 (GeneralNominalSourceBasis255.basis registry context keys).eraseDups

theorem basis_unique (registry : Registry) (context : GeneralNominalCandidates.Context) (keys : List (Nat × Nat)) :
 (basis registry context keys).Nodup := dedup_nodup _

theorem basis_mem (registry : Registry) (context : GeneralNominalCandidates.Context) (keys : List (Nat × Nat)) (term : TyTerm Nat) :
 term ∈ basis registry context keys ↔ term ∈ GeneralNominalSourceBasis255.basis registry context keys := List.mem_eraseDups

theorem source_supported (registry : Registry) (context : GeneralNominalCandidates.Context) (keys : List (Nat × Nat)) (side : Side) :
 GeneralNominalViewNormal255.Supported side (basis registry context keys) (compile context.state CompTerm.var) :=
 GeneralNominalViewNormal255.supported_mono side _ _ _
   (fun _ member => List.mem_eraseDups.mpr member) (GeneralNominalSourceBasis255.source_supported registry context keys side)

theorem source_success (registry : Registry) (context : GeneralNominalCandidates.Context) (keys : List (Nat × Nat)) (side : Side) :
 GeneralNominalViewNormal255.prepare side (basis registry context keys) (compile context.state CompTerm.var) =
 some (GeneralNominalViewNormal255.rewrite side (basis registry context keys) (compile context.state CompTerm.var)) :=
 (GeneralNominalViewNormal255.prepare_exact ..).mpr ⟨source_supported registry context keys side,rfl⟩

theorem source_models (registry : Registry) (context : GeneralNominalCandidates.Context) (keys : List (Nat × Nat)) (side : Side)
 (assignment : GeneralNominalCommonBridge.Assignment) :
 (GeneralNominalViewNormal255.rewrite side (basis registry context keys) (compile context.state CompTerm.var)).Models assignment ↔
 GeneralNominalState.Models context.state assignment :=
 (GeneralNominalViewNormal255.prepare_models side _ _ _ (source_success registry context keys side) assignment).trans
 ((compile_exact context.state CompTerm.var assignment).trans (by rfl))

theorem separated
 (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
 (keys : List (Nat × Nat)) (invocation key purpose binder position : Nat) (privatePurpose : purpose ≤ 1)
 (term : TyTerm Nat) (member : term ∈ basis registry context keys) :
 GeneralNominalPublicBasis253.privateName context.state.seed invocation key purpose binder position ∉
 GeneralPresenceSubstitutionSupport244.typeSources term :=
 GeneralNominalSourceBasis255.separated source keys invocation key purpose binder position privatePurpose term
   (List.mem_eraseDups.mp member)

theorem normalized_atoms_unique (side : Side) (pool : List (TyTerm Nat)) (term : TyTerm Nat)
 (unique : pool.Nodup) (supported : GeneralPresenceCheckedNormal252.atoms side term ⊆ pool) :
 (GeneralPresenceCheckedNormal252.atoms side (GeneralPresenceCheckedNormal252.normalize side pool term)).Nodup := by
 cases side
 · change GeneralPresenceUnionNormal252.atoms term ⊆ pool at supported
   change (GeneralPresenceUnionNormal252.atoms (GeneralPresenceUnionNormal252.fold (GeneralPresenceUnionNormal252.canonical pool (GeneralPresenceUnionNormal252.atoms term)))).Nodup
   rw [GeneralPresenceUnionNormal252.atoms_fold _
     (GeneralPresenceUnionNormal252.canonical_nonempty _ _ supported (GeneralPresenceUnionNormal252.atoms_nonempty term))
     (fun atom member => GeneralPresenceUnionNormal252.atoms_flat term atom ((GeneralPresenceUnionNormal252.canonical_mem ..).mp member).2)]
   exact GeneralPresenceUnionNormal252.canonical_nodup _ _ unique
 · change GeneralPresenceInterNormal252.atoms term ⊆ pool at supported
   change (GeneralPresenceInterNormal252.atoms (GeneralPresenceInterNormal252.fold (GeneralPresenceInterNormal252.canonical pool (GeneralPresenceInterNormal252.atoms term)))).Nodup
   rw [GeneralPresenceInterNormal252.atoms_fold _
     (GeneralPresenceInterNormal252.canonical_nonempty _ _ supported (GeneralPresenceInterNormal252.atoms_nonempty term))
     (fun atom member => GeneralPresenceInterNormal252.atoms_flat term atom ((GeneralPresenceInterNormal252.canonical_mem ..).mp member).2)]
   exact GeneralPresenceInterNormal252.canonical_nodup _ _ unique

theorem source_fields_unique (registry : Registry) (context : GeneralNominalCandidates.Context)
 (keys : List (Nat × Nat)) (side : Side) (term : TyTerm Nat)
 (member : term ∈ GeneralNominalViewTypeTerms255.terms
   (GeneralNominalViewNormal255.rewrite side (basis registry context keys) (compile context.state CompTerm.var))) :
 (GeneralPresenceCheckedNormal252.atoms side term).Nodup := by
 obtain ⟨original,present,rfl⟩ := GeneralNominalViewTypeImage255.term_origin _ _ term member
 exact normalized_atoms_unique side _ original (basis_unique registry context keys)
   (source_supported registry context keys side original present)
end Yulang.GeneralNominalCanonicalBasis255
