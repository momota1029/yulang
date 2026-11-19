import Yulang.GeneralRebaseTreeSeedExtract272

namespace Yulang.GeneralRebaseTreeSeedExact272
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalRecursiveInspection (Test)
open GeneralNominalOriginTerms (arity)
open GeneralRebaseStructuralOrigin270 (Slots)
open GeneralRebaseTreeSeedFrame272 (Frame describe)
open GeneralRebaseTreeSeedExtract272 (fill filled extract)
open GeneralRebaseFiniteTree272 (Tree height child_height)

theorem fill_complete (test : Test) (slots : Fin (arity test) → Option Tree)
 (kids : Fin (arity test) → Tree) (all : ∀ i, slots i = some (kids i)) :
 fill test slots = some (.node test kids) := by
 have good (i : Fin (arity test)) : (slots i).isSome = true := by rw [all i]; rfl
 unfold fill
 rw [dite_eq_left good]
 apply congrArg some
 apply congrArg (Tree.node test)
 funext i
 exact Option.some.inj ((Option.some_get (good i)).trans (all i))

theorem extract_mono (state : State roles) (smaller larger : Nat) (bound : smaller ≤ larger)
 (slot : Slots state) (t : Tree) (work : extract state smaller slot = some t) :
 extract state larger slot = some t := by
 induction smaller generalizing larger slot t with
 | zero => contradiction
 | succ smaller ih =>
   cases larger with
   | zero => omega
   | succ larger =>
     unfold extract at work ⊢
     cases declared : describe state slot with
     | none => simp [declared] at work
     | some f =>
       simp only [declared] at work ⊢
       obtain ⟨kids,rfl,each⟩ := filled f.test _ t work
       apply fill_complete
       intro i
       obtain ⟨child,direct,prior⟩ := Option.bind_eq_some_iff.mp (each i)
       exact Option.bind_eq_some_iff.mpr ⟨child,direct,ih larger (by omega) child (kids i) prior⟩

inductive Derived (state : State roles) : Slots state → Tree → Prop where
 | node (frame : Frame state) (read : describe state slot = some frame)
   (targets : Fin (arity frame.test) → Slots state) (kids : Fin (arity frame.test) → Tree)
   (edges : ∀ i, frame.children i = some (targets i))
   (subtrees : ∀ i, Derived state (targets i) (kids i)) :
     Derived state slot (.node frame.test kids)

theorem derived_by_compute (state : State roles) (n : Nat) (s : Slots state)
 (t : Tree) (run : extract state n s = some t) :
 Derived state s t ∧ height t ≤ n := by
 induction n generalizing s t with
 | zero => contradiction
 | succ n ih =>
   unfold extract at run
   split at run
   · contradiction
   · rename_i f recognized
     obtain ⟨kids,rfl,each⟩ := filled f.test _ t run
     have joined (i : Fin (arity f.test)) :
       ∃ s, f.children i = some s ∧ Derived state s (kids i) ∧ height (kids i) ≤ n := by
       obtain ⟨s,seen,kid⟩ := Option.bind_eq_some_iff.mp (each i)
       exact ⟨s,seen,ih s (kids i) kid⟩
     let slots (i : Fin (arity f.test)) : Slots state := Classical.choose (joined i)
     have actual (i : Fin (arity f.test)) : f.children i = some (slots i) ∧
       Derived state (slots i) (kids i) ∧ height (kids i) ≤ n := Classical.choose_spec (joined i)
     refine ⟨.node f recognized slots kids (fun i => (actual i).1) (fun i => (actual i).2.1),?_⟩
     have bound (list : List Nat) (all : ∀ v ∈ list, v ≤ n) : list.foldr max 0 ≤ n := by
       induction list with
       | nil => exact Nat.zero_le _
       | cons v rest ih =>
         exact Nat.max_le.mpr ⟨all _ List.mem_cons_self,ih (fun k mem => all k (List.mem_cons_of_mem _ mem))⟩
     change 1 + (List.ofFn fun k => height (kids k)).foldr max 0 ≤ n + 1
     have test := bound (List.ofFn fun i => height (kids i)) (by
       intro k found; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp found; exact (actual i).2.2)
     omega

theorem computed_at_height (state : State roles) (s : Slots state) (t : Tree)
 (valid : Derived state s t) : extract state (height t) s = some t := by
 induction valid with
 | node frame read targets kids edges subtrees ih =>
   let h := (List.ofFn fun i => height (kids i)).foldr max 0
   have exactHeight : height (.node frame.test kids) = h + 1 := by simp [height,h,Nat.add_comm]
   rw [exactHeight]
   unfold extract
   rw [read]
   apply fill_complete
   intro j
   have under : height (kids j) ≤ h := by
     have strict := child_height frame.test kids j
     rw [exactHeight] at strict
     omega
   exact Option.bind_eq_some_iff.mpr ⟨targets j,edges j,
     extract_mono state _ h under (targets j) (kids j) (ih j)⟩

theorem exact_support (state : State roles) (n : Nat) (s : Slots state) (t : Tree) :
 extract state n s = some t ↔ Derived state s t ∧ height t ≤ n :=
 ⟨derived_by_compute state n s t,fun ⟨valid,h⟩ => extract_mono state _ n h s t (computed_at_height state s t valid)⟩

end Yulang.GeneralRebaseTreeSeedExact272
