import Yulang.GeneralDeclarativeRevalidate344

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeReplayOrdering344
open GeneralNominalCenters (Plan)
open GeneralDeclarations (Clause)
open GeneralDeclarativeClauseBatch327 (Port)
open GeneralDeclarativeReplayOrder344 (logicalChildren inputAt)
open GeneralDeclarativeRawReplayArgs344 (emittedDemand names)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralCanonicalChildOrder (canonicalRequirements canonicalDeclaration canonicalRequirements_perm)
open GeneralWhereVersionCompiler317 (allocation)

/-- The ordinary demand projection keeps source order here. The raw
compiler retains canonical clause order; these must not be asserted
literally equal unless the source list is already canonical. -/
def sourceOrder (p : Plan rs) (ports : List Port) :=
  children p.packet.declaration (names p) ⟨inputAt p ports,fun cl => (allocation p cl).outputs⟩

theorem canonical_order (p : Plan rs) (ports : List Port) :
    logicalChildren p ports =
      (canonicalRequirements p.packet.declaration.requirements).map
        (fun cl => emittedDemand p cl (inputAt p ports cl)) := by
  unfold logicalChildren GeneralDeclarativeCommitPosition344.clauses
  exact List.attach_map_val (l := canonicalRequirements p.packet.declaration.requirements)
    (f := fun cl => emittedDemand p cl (inputAt p ports cl))

theorem permuted (p : Plan rs) (ports : List Port) :
    (sourceOrder p ports).Perm (logicalChildren p ports) := by
  rw [canonical_order]
  exact (canonicalRequirements_perm p.packet.declaration.requirements).map
    (fun cl => emittedDemand p cl (inputAt p ports cl))

theorem literal_when_sorted (p : Plan rs) (ports : List Port)
    (sorted : canonicalRequirements p.packet.declaration.requirements = p.packet.declaration.requirements) :
    logicalChildren p ports = sourceOrder p ports := by
  rw [canonical_order,sorted]
  rfl

/-- An explicit view indexed by the canonicalized declaration is
literally the result of ordinary emission in that order. The lookup
ports are still the original actually prepared binder positions. -/
theorem compiler_canonical (p : Plan rs) (ports : List Port) :
    logicalChildren p ports =
      children (canonicalDeclaration p.packet.declaration) (names p)
        ⟨inputAt p ports,fun cl => (allocation p cl).outputs⟩ := by
  rw [canonical_order]
  rfl

end Yulang.GeneralDeclarativeReplayOrdering344
