import Yulang.GeneralDictionaryCompoundStep238
import Yulang.GeneralNominalOutputNames253
import Yulang.GeneralPresenceSnapshotNormal252
import Yulang.GeneralPresenceOrderedSyntax247
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundPool253
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238
open GeneralDictionaryCompoundPacket238 (plan packet)
open GeneralDictionaryCompoundFrame238 (before installed effect)
open GeneralNominalOutputNames253
open Core.PresenceGeneration (TyTerm)

abbrev signature : child.Signature roles := ⟨rfl,by intro _ h; cases h⟩
abbrev site := GeneralNominalVersionedFrame231.childSite plan child signature
abbrev endpoint := (site.occurrence.demand.arguments 0).1

/-- This registry has no output-only binders, despite emitting compound child
input targets. Therefore the named-binder interpretation of I50's output pool
contains no generated name, for any finite owner list. -/
theorem no_named_outputs (keys : List (Nat × Nat)) : outputs registry snapshot.seed keys = [] := by
 induction keys with
 | nil => rfl
 | cons key rest ih =>
   simp only [outputs,List.flatMap_cons] at *
   rw [ih]
   simp [registry,GeneralNominalCenteredHeadAllocEncoding.registry,
     GeneralNominalCenteredHeadAllocEncoding.declaration,declaration,GeneralDeclarations.Declaration.outputNames,
     child]

abbrev pool (keys : List (Nat × Nat)) : List (TyTerm Nat) :=
 (GeneralNominalState.sources snapshot ++ outputs registry snapshot.seed keys).map TyTerm.var

theorem endpoint_allocated : endpoint = GeneralDictionaryCompoundModel238.names 0 := rfl

theorem endpoint_new : endpoint ∉ GeneralNominalState.sources snapshot := by
 intro member
 have low := source_bound endpoint member
 have high : 4 < endpoint := GeneralNominalIdentities.source_above_seed snapshot.seed _
 omega

theorem endpoint_not_pool (keys : List (Nat × Nat)) : TyTerm.var endpoint ∉ pool keys := by
 intro member
 obtain ⟨name,present,equal⟩ := List.mem_map.mp member
 have same : name = endpoint := TyTerm.var.inj equal
 subst name
 rw [no_named_outputs,List.append_nil] at present
 exact endpoint_new present

theorem emitted : site ∈ GeneralNominalVersionedChildren232.emitted plan := by
 unfold GeneralNominalVersionedChildren232.emitted
 simp only [GeneralCanonicalChildOrder.canonicalRequirements]
 exact List.mem_map.mpr ⟨⟨child,by simp⟩,by simp,rfl⟩

theorem site_reached : site ∈ installed.core.sites := List.mem_append_right _ emitted

theorem point_step : GeneralNominalPointKernel240.Step registry root before installed :=
 ⟨root,.root,.install effect GeneralDictionaryCompoundStep238.installable GeneralDictionaryCompoundStep238.not_committed⟩

theorem point_reachable : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles)
 sourceRegistry root installed :=
 ⟨before,⟨GeneralDictionaryCompoundSource238.start,GeneralDictionaryCompoundSource238.initial,rfl⟩,.tail .refl point_step⟩

/-- Merely eliminating private slots cannot repair this omission: every block
that leaves this public endpoint alone preserves the out-of-pool atom. This
is not a claim that the unimplemented replacement compiler has such a block. -/
theorem private_rewrite_unsupported (keys : List (Nat × Nat))
 (old : List (GeneralPresenceDefinitionRewrite244.Entry Nat))
 (outside : ∀ entry ∈ old, entry.1 ≠ endpoint) :
 ¬ GeneralPresenceUnionNormal252.atoms
   ((TyTerm.var endpoint).subst (GeneralPresenceOrderedSubstitution247.mapping old)) ⊆ pool keys := by
 have fixed := GeneralPresenceOrderedSyntax247.mapping_outside old endpoint outside
 change ¬ GeneralPresenceUnionNormal252.atoms (GeneralPresenceOrderedSubstitution247.mapping old endpoint).ty ⊆ pool keys
 rw [fixed]
 intro closed
 exact endpoint_not_pool keys (closed (List.mem_singleton_self _))

theorem source_reachable_pool_gap :
 B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) sourceRegistry root installed ∧
 site ∈ installed.core.sites ∧ ∀ keys, TyTerm.var endpoint ∉ pool keys :=
 ⟨point_reachable,site_reached,endpoint_not_pool⟩
end Yulang.GeneralDictionaryCompoundPool253
