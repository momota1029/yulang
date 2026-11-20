import Yulang.GeneralGeneratedDictionaryScope299

namespace Yulang.GeneralGeneratedDictionaryNodes299
open CommonRoleOutermostResolver (All₂ Dictionary)
open B4Target (Vocabulary)
open B4TargetV8
open GeneralGeneratedDictionaryRun299
open GeneralGeneratedDictionaryScope299
variable {v : Vocabulary} {b : SourceBoundary v} {r : v.Registry} {s : v.State}

/-- The local premise quantifies model and child dictionaries. No child result
is required as table input and no other source demand is assumed certified. -/
def Nodes (b : SourceBoundary v) (r : v.Registry) (s : v.State)
    (read : Read) (decode : Nat → v.Demand) : Prop :=
  ∀ x row, read x = some row → ∀ m, b.Models s m → ∀ ds,
    All₂ (b.Evidence r s m) (row.children.map decode) ds →
    b.Evidence r s m (decode x) (.node row.key ds)

theorem from_evidenceAt (read : Read) (decode : Nat → v.Demand)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode)
    (scope : InScope b r s root read decode) (closed : Closed read)
    (atRoot : B4SkeletonV8.EvidenceAt b r s root) : Nodes b r s read decode := by
  intro x row hit m ok ds linked
  obtain ⟨reached,stable⟩ := scope x row hit
  exact atRoot m ok (decode x) row.key _ ds reached stable
    (by
      intro child mem
      obtain ⟨i,found,rfl⟩ := List.mem_map.mp mem
      obtain ⟨sub,readSub⟩ := closed x row hit i found
      exact (scope i sub readSub).2)
    (faith x row hit) linked

theorem same_model (read : Read) (decode : Nat → v.Demand) (nodes : Nodes b r s read decode)
    (m : v.Model) (valid : b.Models s m) (n x : Nat) (d : Dictionary)
    (ok : run read n x = some d) : b.Evidence r s m (decode x) d := by
  induction n generalizing x d with
  | zero => cases ok
  | succ n ih =>
    obtain ⟨row,ds,hit,all,rfl⟩ := (run_exact _ _ _ _).mp ok
    exact nodes x row hit m valid ds (map_all decode ih all)

theorem constructs (read : Read) (decode : Nat → v.Demand) (rank : Nat → Nat)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode) (nodes : Nodes b r s read decode)
    (decreases : Ranked read rank) (closed : Closed read) (x : Nat) {row : Entry}
    (hit : read x = some row) :
    ∃ d, run read (rank x+1) x = some d ∧ Classify b r s (decode x) (.selected d) ∧
      ∀ m, b.Models s m → b.Evidence r s m (decode x) d := by
  obtain ⟨d,ok⟩ := rank_suffices read rank decreases closed x hit
  exact ⟨d,ok,classifies _ _ faith _ _ _ ok,fun m valid => same_model _ _ nodes m valid _ _ _ ok⟩

end Yulang.GeneralGeneratedDictionaryNodes299
