import Yulang.GeneralGeneratedDictionaryNodes299
import Yulang.GeneralNominalVersionedMixedCurrentCandidate235

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralGeneratedMixedCurrentNodes299
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedMixedCurrentCandidate235 (Current source_installable)
open GeneralNominalCenteredHeadAllocEncoding renaming registry → encode
open GeneralGeneratedDictionaryRun299
open GeneralGeneratedDictionaryScope299
open GeneralGeneratedDictionaryNodes299
open B4TargetV8 (Reachable)
variable {roles : Roles.RoleDecls} {registry : Registry} {s : State roles} {root : Occurrence roles}

def Providers (registry : Registry) (s : State roles) (read : Read)
    (decode : Nat → Occurrence roles) : Prop :=
  ∀ x row, read x = some row → (∃ m, Models s m) →
    ∃ effect : Effect roles, Current (encode registry) s (decode x) effect

theorem scoped_nodes (read : Read) (decode : Nat → Occurrence roles)
    (path : Reachable (boundary roles) registry root s)
    (faith : Faithful (b:=boundary roles) (r:=registry) (s:=s) read decode)
    (scope : InScope (boundary roles) registry s root read decode)
    (available : Providers registry s read decode) : Nodes (boundary roles) registry s read decode := by
  intro x row hit m held dictionaries childEvidence
  obtain ⟨effect,current⟩ := available x row hit ⟨m,held⟩
  have picked := faith x row hit
  exact GeneralNominalVersionedMixedStableEvidence235.selected_node
    (scope x row hit).2 (source_installable current path picked) current.occurrence_eq
    (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp picked) held childEvidence

end Yulang.GeneralGeneratedMixedCurrentNodes299
