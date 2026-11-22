import Yulang.GeneralDeclarativeCommitModes344

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCommitPosition344
open GeneralNominalCenters (Plan Site)
open GeneralDeclarations (Clause Registry)
open GeneralNominalCommonBridge (Assignment)
open GeneralWhereVersionCompiler317 (emit allocation child children)
open GeneralWhereVersionInstall317 (Journal InstallStep Models install emitted)
open GeneralDeclarativeCommitSuffix344 (Receipt from_step child_at)
open GeneralNominalVersionedFrame231 (capture)
open GeneralDeclarationDemands (outputTarget)
open GeneralCanonicalChildOrder (canonicalRequirements canonicalRequirements_perm)

abbrev clauses (p : Plan rs) := (canonicalRequirements p.packet.declaration.requirements).attach
abbrev signature (p : Plan rs) (c : {q // q ∈ canonicalRequirements p.packet.declaration.requirements}) :=
  p.packet.checked.signature.2.2.2 c.val ((canonicalRequirements_perm _).mem_iff.mpr c.property)

theorem source_at (p : Plan rs) {i : Nat} {s : Site rs}
    (seen : (emitted p)[i]? = some s) :
    ∃ c, (clauses p)[i]? = some c ∧ s = child p c.val (signature p c) := by
  change ((clauses p).map (fun c => child p c.val (signature p c)))[i]? = some s at seen
  rw [List.getElem?_map] at seen
  cases atIndex : (clauses p)[i]? with
  | none => rw [atIndex] at seen; cases seen
  | some c =>
    rw [atIndex] at seen
    exact ⟨c,rfl,(Option.some.inj seen).symm⟩

theorem current_stamp (r : Registry) (before : Journal rs) (ctx : GeneralNominalCandidates.Context)
    (p : Plan rs) (step : InstallStep r before (install before ctx p))
    (m : Assignment) (valid : Models (install before ctx p) m) :
    Receipt r before (install before ctx p) p m := by
  obtain ⟨_,q,_,receipt⟩ := from_step step m valid
  have recorded := receipt.stamp
  change (before.versionedWhere ++ [p])[before.versionedWhere.length]? = some q at recorded
  rw [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self] at recorded
  have same : p = q := Option.some.inj recorded
  subst q
  exact receipt

theorem literal_outputs (p : Plan rs) (c : Clause) (sig : c.Signature rs) :
    (child p c sig).occurrence.demand.outputs =
      c.outputs.map (fun e => ⟨e.name,outputTarget p.packet.declaration (capture p.packet) (allocation p c).outputs e⟩) :=
  rfl

/-- Source clause, exact position, and literal targets are obtained
from the genuine committed suffix, not from equality of denotations. -/
theorem positioned {r : Registry} {before after : Journal rs}
    {p : Plan rs} {m : Assignment} (receipt : Receipt r before after p m)
    {i : Nat} {s : Site rs} (seen : (emitted p)[i]? = some s) :
    ∃ c, (clauses p)[i]? = some c ∧ s = child p c.val (signature p c) ∧
      after.mixed.core.sites[before.mixed.core.sites.length+i]? = some s ∧
      (children p)[i]? = some s.occurrence ∧
      s.occurrence.demand.outputs =
        c.val.outputs.map (fun e => ⟨e.name,outputTarget p.packet.declaration (capture p.packet)
          (allocation p c.val).outputs e⟩) := by
  obtain ⟨c,source,rfl⟩ := source_at p seen
  exact ⟨c,source,rfl,(child_at receipt seen).1,(child_at receipt seen).2,literal_outputs ..⟩

end Yulang.GeneralDeclarativeCommitPosition344
