import Yulang.GeneralGeneratedDictionaryRankBook299

namespace Yulang.GeneralGeneratedSemanticAcc299
open B4Target (Vocabulary)
open B4TargetV8
open CommonRoleOutermostResolver (Child Dictionary Frontier)
open GeneralGeneratedDictionaryRun299
open GeneralGeneratedDictionaryScope299
open GeneralGeneratedDictionaryAcc299
open GeneralGeneratedDictionaryRankCheck299 (Known)
open GeneralGeneratedDictionaryFiniteCap299 (finite_cap)

variable {v : Vocabulary} {b : SourceBoundary v} {r : v.Registry} {s : v.State}

theorem source_child_exact (read : Read) (decode : Nat → v.Demand)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode)
    (i : Nat) (row : Entry) (hit : read i = some row) (d : v.Demand) :
    Child (Local b r s) d (decode i) ↔ d ∈ row.children.map decode := by
  constructor
  · rintro ⟨key,children,selected,found⟩
    have same := Frontier.selected.inj (local_functional selected (faith i row hit))
    exact same.2 ▸ found
  · exact fun member => ⟨row.key,_,faith i row hit,member⟩

theorem semantic_accessible (read : Read) (decode : Nat → v.Demand)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode)
    (n i : Nat) (d : Dictionary) (out : run read n i = some d) :
    Acc (Child (Local b r s)) (decode i) := by
  induction n generalizing i d with
  | zero => cases out
  | succ n ih =>
    obtain ⟨row,ds,hit,all,rfl⟩ := (run_exact _ _ _ _).mp out
    apply Acc.intro
    intro child edge
    have mem := (source_child_exact read decode faith i row hit child).mp edge
    obtain ⟨j,get,rfl⟩ := List.mem_map.mp mem
    obtain ⟨p,success⟩ := all_left all j get
    exact ih j p success

theorem semantic_iff (read : Read) (decode : Nat → v.Demand)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode) (closed : Closed read)
    (i : Nat) {row : Entry} (hit : read i = some row) :
    (∃ n d, run read n i = some d) ↔ Acc (Child (Local b r s)) (decode i) := by
  constructor
  · rintro ⟨n,d,found⟩
    exact semantic_accessible read decode faith n i d found
  · intro acc
    exact accessible_success read closed i (source_accessible faith i acc) row hit

theorem bounded_semantic_iff (read : Read) (decode : Nat → v.Demand)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode)
    (closed : Closed read) (domain : List Nat) (known : Known read domain)
    (i : Nat) {row : Entry} (hit : read i = some row) :
    (∃ d, run read domain.length i = some d) ↔ Acc (Child (Local b r s)) (decode i) := by
  constructor
  · rintro ⟨d,success⟩
    exact semantic_accessible read decode faith _ i d success
  · intro acc
    exact finite_cap read domain closed known i (source_accessible faith i acc) row hit

end Yulang.GeneralGeneratedSemanticAcc299
