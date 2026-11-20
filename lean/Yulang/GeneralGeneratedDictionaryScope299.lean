import Yulang.GeneralGeneratedDictionaryRun299
import Yulang.B4SkeletonV8

namespace Yulang.GeneralGeneratedDictionaryScope299
open CommonRoleOutermostResolver (All₂ Dictionary)
open B4Target (Vocabulary)
open B4TargetV8
open GeneralGeneratedDictionaryRun299

variable {v : Vocabulary} {b : SourceBoundary v} {r : v.Registry} {s : v.State}

def Faithful (read : Read) (decode : Nat → v.Demand) : Prop :=
  ∀ x row, read x = some row →
    Local b r s (decode x) (.selected row.key (row.children.map decode))

def InScope (b : SourceBoundary v) (r : v.Registry) (s : v.State)
    (root : v.Demand) (read : Read) (decode : Nat → v.Demand) : Prop :=
  ∀ x row, read x = some row → (decode x = root ∨ b.Generated r s root (decode x)) ∧
    b.Stable r s (decode x)

theorem map_all {α β γ} {P : α → β → Prop} {Q : γ → β → Prop}
    (f : α → γ) (h : ∀ a d, P a d → Q (f a) d) {xs : List α} {ds : List β}
    (all : All₂ P xs ds) : All₂ Q (xs.map f) ds := by
  induction all with
  | nil => exact .nil
  | cons p _ ih => exact .cons (h _ _ p) ih

theorem all_left {α β} {P : α → β → Prop} {xs : List α} {ds : List β}
    (h : All₂ P xs ds) (x : α) (mem : x ∈ xs) : ∃ d, P x d := by
  induction h with
  | nil => cases mem
  | cons left _ ih =>
    rcases List.mem_cons.mp mem with rfl | tail
    · exact ⟨_,left⟩
    · exact ih tail

theorem run_has_row {read : Read} {n x : Nat} {d : Dictionary}
    (ok : run read n x = some d) : ∃ row, read x = some row := by
  cases n with
  | zero => cases ok
  | succ n =>
    obtain ⟨row,_,hit,_,_⟩ := (run_exact _ _ _ _).mp ok
    exact ⟨row,hit⟩

theorem classifies (read : Read) (decode : Nat → v.Demand)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode) (n x : Nat) (d : Dictionary)
    (ok : run read n x = some d) : Classify b r s (decode x) (.selected d) := by
  induction n generalizing x d with
  | zero => cases ok
  | succ n ih =>
    obtain ⟨row,ds,hit,all,rfl⟩ := (run_exact _ _ _ _).mp ok
    exact .selected (faith x row hit) (map_all decode ih all)

theorem same_model (read : Read) (decode : Nat → v.Demand)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode)
    (scope : InScope b r s root read decode) (node : B4SkeletonV8.EvidenceAt b r s root)
    (m : v.Model) (valid : b.Models s m) (n x : Nat) (d : Dictionary)
    (ok : run read n x = some d) : b.Evidence r s m (decode x) d := by
  induction n generalizing x d with
  | zero => cases ok
  | succ n ih =>
    obtain ⟨row,ds,hit,all,rfl⟩ := (run_exact _ _ _ _).mp ok
    obtain ⟨reach,stable⟩ := scope x row hit
    apply node m valid (decode x) row.key _ ds reach stable ?_ (faith x row hit)
    · exact map_all decode ih all
    · intro child member
      obtain ⟨i,iMem,rfl⟩ := List.mem_map.mp member
      obtain ⟨sub,got⟩ := all_left all i iMem
      obtain ⟨childRow,hit⟩ := run_has_row got
      exact (scope i childRow hit).2

theorem constructs (read : Read) (decode : Nat → v.Demand) (rank : Nat → Nat)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode)
    (scope : InScope b r s root read decode) (node : B4SkeletonV8.EvidenceAt b r s root)
    (decreases : Ranked read rank) (closed : Closed read) (x : Nat) {row : Entry}
    (hit : read x = some row) :
    ∃ d, run read (rank x+1) x = some d ∧ Classify b r s (decode x) (.selected d) ∧
      ∀ m, b.Models s m → b.Evidence r s m (decode x) d := by
  obtain ⟨d,ok⟩ := rank_suffices read rank decreases closed x hit
  exact ⟨d,ok,classifies _ _ faith _ _ _ ok,fun m valid => same_model _ _ faith scope node m valid _ _ _ ok⟩

end Yulang.GeneralGeneratedDictionaryScope299
