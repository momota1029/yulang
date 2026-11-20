import Yulang.GeneralGeneratedMixedRooted299

namespace Yulang.GeneralGeneratedDictionarySlice299
open GeneralGeneratedDictionaryRun299
open GeneralGeneratedDictionaryAcc299 (Edge)
open GeneralGeneratedDictionaryScope299 (all_left run_has_row)
open GeneralGeneratedMixedRooted299 (Rooted)
open CommonRoleOutermostResolver (All₂ Dictionary)

def keys (read : Read) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,x =>
    x :: match read x with
    | none => []
    | some row => row.children.flatMap (keys read n)

def restrict (read : Read) (keep : List Nat) : Read := fun i =>
  if i ∈ keep then read i else none

theorem below_keys (read : Read) (n x c y : Nat) (row : Entry)
    (hit : read x = some row) (mem : c ∈ row.children)
    (nested : y ∈ keys read n c) :
    y ∈ keys read (n+1) x := by
  apply List.mem_cons.mpr
  right
  simp only [hit]
  exact List.mem_flatMap.mpr ⟨c,mem,nested⟩

theorem keys_path (read : Read) (n x i : Nat) (member : i ∈ keys read n x) :
    i = x ∨ Relation.TransGen (Edge read) i x := by
  induction n generalizing x i with
  | zero => cases member
  | succ n ih =>
    rcases List.mem_cons.mp member with rfl | below
    · exact .inl rfl
    · cases hit : read x with
      | none => simp [hit] at below
      | some row =>
        simp only [hit] at below
        obtain ⟨c,here,mem⟩ := List.mem_flatMap.mp below
        right
        have edge : Edge read c x := ⟨row,hit,here⟩
        rcases ih c i mem with rfl | p
        · exact .single edge
        · exact .tail p edge

theorem restricted_hit (read : Read) (keep : List Nat) (i : Nat) (row : Entry)
    (found : restrict read keep i = some row) : i ∈ keep ∧ read i = some row := by
  unfold restrict at found
  split at found
  · exact ⟨by assumption,found⟩
  · cases found

theorem retained_path (read : Read) (n x : Nat) (keep : List Nat)
    (coverage : ∀ i ∈ keys read n x, i ∈ keep) (i : Nat) (member : i ∈ keys read n x) :
    i = x ∨ Relation.TransGen (Edge (restrict read keep)) i x := by
  induction n generalizing x i with
  | zero => cases member
  | succ n ih =>
    rcases List.mem_cons.mp member with rfl | below
    · exact .inl rfl
    · cases hit : read x with
      | none => simp [hit] at below
      | some row =>
        simp only [hit] at below
        obtain ⟨c,here,mem⟩ := List.mem_flatMap.mp below
        right
        have live : x ∈ keep := coverage x (List.mem_cons_self ..)
        have edge : Edge (restrict read keep) c x :=
          ⟨row,by simp [restrict,live,hit],here⟩
        rcases ih c (fun y h => coverage y (below_keys read n x c y row hit here h)) i mem with rfl | p
        · exact .single edge
        · exact .tail p edge

theorem rooted (read : Read) (n x : Nat) : Rooted (restrict read (keys read n x)) x :=
  fun i _row proved => retained_path read n x _ (fun _ h => h) i (restricted_hit _ _ _ _ proved).1

theorem all_with_key {P Q : Nat → Dictionary → Prop}
    {xs : List Nat} {ds : List Dictionary} (given : All₂ P xs ds)
    (cast : ∀ i ∈ xs, ∀ d, P i d → Q i d) : All₂ Q xs ds := by
  induction given with
  | nil => exact .nil
  | cons head rest ih =>
    exact .cons (cast _ (List.mem_cons_self ..) _ head) (ih (fun i h => cast i (List.mem_cons_of_mem _ h)))

theorem preserves (read : Read) (n x : Nat) (d : Dictionary)
    (ok : run read n x = some d) (keep : List Nat)
    (coverage : ∀ i ∈ keys read n x, i ∈ keep) :
    run (restrict read keep) n x = some d := by
  induction n generalizing x d with
  | zero => cases ok
  | succ n ih =>
    obtain ⟨row,ds,hit,all,rfl⟩ := (run_exact _ _ _ _).mp ok
    have onKey : x ∈ keep := coverage x (List.mem_cons_self ..)
    apply (run_exact _ _ _ _).mpr
    refine ⟨row,ds,?_,?_,rfl⟩
    · simp [restrict,onKey,hit]
    · exact all_with_key all (fun child member dict childOk =>
        ih child dict childOk (fun i inner => coverage i (below_keys read n x child i row hit member inner)))

theorem at_root (read : Read) (n x : Nat) (d : Dictionary) (hit : run read n x = some d) :
    run (restrict read (keys read n x)) n x = some d :=
  preserves read n x d hit _ (fun _ mem => mem)

theorem have_row (read : Read) (n x : Nat) (d : Dictionary)
    (hit : run read n x = some d) (i : Nat) (visited : i ∈ keys read n x) :
    (∃ row, read i = some row) := by
  induction n generalizing x d with
  | zero => cases hit
  | succ n ih =>
    obtain ⟨row,ds,hr,all,_⟩ := (run_exact _ _ _ _).mp hit
    rcases List.mem_cons.mp visited with rfl | inner
    · exact ⟨row,hr⟩
    · simp only [hr] at inner
      obtain ⟨child,mem,nested⟩ := List.mem_flatMap.mp inner
      obtain ⟨childDict,childOK⟩ := all_left all child mem
      exact ih child childDict childOK nested

theorem knows_children (read : Read) (n x : Nat) (d : Dictionary)
    (hit : run read n x = some d) (i : Nat) (visited : i ∈ keys read n x)
    (atI : Entry) (atOk : read i = some atI) (c : Nat) (child : c ∈ atI.children) :
    c ∈ keys read n x := by
  induction n generalizing x d i atI with
  | zero => cases hit
  | succ n ih =>
    obtain ⟨row,ds,hr,all,_⟩ := (run_exact _ _ _ _).mp hit
    rcases List.mem_cons.mp visited with rfl | inner
    · cases Option.some.inj (hr.symm.trans atOk)
      obtain ⟨cd,ret⟩ := all_left all c child
      have inChild : c ∈ keys read n c := by
        cases n with
        | zero => cases ret
        | succ n => exact List.mem_cons_self ..
      exact below_keys read n i c c atI atOk child inChild
    · simp only [hr] at inner
      obtain ⟨through,mem,nested⟩ := List.mem_flatMap.mp inner
      obtain ⟨childDict,childOK⟩ := all_left all through mem
      exact below_keys read n x through c row hr mem (ih through childDict childOK i nested atI atOk child)

theorem closed_slice (read : Read) (n x : Nat) (d : Dictionary) (hit : run read n x = some d) :
    Closed (restrict read (keys read n x)) := by
  intro i row seen c child
  obtain ⟨visited,raw⟩ := restricted_hit _ _ _ _ seen
  have key := knows_children read n x d hit i visited row raw c child
  obtain ⟨cc,found⟩ := have_row read n x d hit c key
  exact ⟨cc,by simp [restrict,key,found]⟩

end Yulang.GeneralGeneratedDictionarySlice299
