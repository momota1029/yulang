import Yulang.GeneralRebaseWitnessAnchor297
import Yulang.GeneralRebaseSameInputs269

namespace Yulang.GeneralRebaseMergeQuestions297
open GeneralNominalCenters (Site SameInputs)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalDemandMerging (All₂ Related)
open GeneralRebaseSameInputs269 (givenNames related_source)
open GeneralRebaseMergeCenters267 (centers)
open GeneralRebaseFiniteWitnessTable297 (Covers hit)
open CommonNominalFullCarrier (Equivalent)

abbrev Pair (roles : Roles.RoleDecls) := Site roles × Site roles

def aligned (p : Pair roles) : List (Nat × Nat) := (centers p.1).zip (centers p.2)

def atModel (p : Pair roles) (m : Assignment) : Prop :=
  ∀ c ∈ aligned p, Equivalent (m c.1).1 (m c.2).1

def counter (s : State roles) (p : Pair roles) (m : Assignment) : Prop :=
  Models s m ∧ ¬ atModel p m

def shape (p : Pair roles) : Bool :=
  p.1.occurrence.demand.role == p.2.occurrence.demand.role &&
    (centers p.1).length == (centers p.2).length

theorem shape_exact (p : Pair roles) : shape p = true ↔
    p.1.occurrence.demand.role = p.2.occurrence.demand.role ∧
    (centers p.1).length = (centers p.2).length := by
  simp [shape]

theorem roles_force_length (p : Pair roles)
    (r : p.1.occurrence.demand.role = p.2.occurrence.demand.role) :
    (centers p.1).length = (centers p.2).length := by
  simp only [centers,List.length_ofFn,r]

theorem all₂_zip (relation : Nat → Nat → Prop) (as bs : List Nat) :
    All₂ (fun a b => ∃ i j, a = some (GeneralNominalRecursiveInspection.Origin.source i) ∧
       b = some (GeneralNominalRecursiveInspection.Origin.source j) ∧ relation i j)
      (givenNames as) (givenNames bs) ↔
    as.length = bs.length ∧ ∀ c ∈ as.zip bs, relation c.1 c.2 := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => exact ⟨fun _ => ⟨rfl,fun _ h => False.elim (List.not_mem_nil h)⟩,fun _ => .nil⟩
    | cons b bs =>
      constructor
      · intro impossible; cases impossible
      · intro wrong; simp at wrong
  | cons a as ih =>
    cases bs with
    | nil =>
      constructor
      · intro impossible; cases impossible
      · intro wrong; simp at wrong
    | cons b bs =>
      constructor
      · intro hs
        cases hs with
        | cons head tail =>
          obtain ⟨i,j,ei,ej,h⟩ := head
          have left : a = i := by simpa [givenNames] using ei
          have right : b = j := by simpa [givenNames] using ej
          subst i
          subst j
          have rest := (ih bs).mp tail
          refine ⟨congrArg Nat.succ rest.1,?_⟩
          intro c known
          rcases List.mem_cons.mp known with rfl | suffix
          · exact h
          · exact rest.2 c suffix
      · rintro ⟨same,each⟩
        exact .cons ⟨a,b,rfl,rfl,each (a,b) (List.mem_cons_self ..)⟩
          ((ih bs).mpr ⟨Nat.succ.inj same,fun c used => each c (List.mem_cons_of_mem _ used)⟩)

theorem semantic_exact (s : State roles) (p : Pair roles) :
    SameInputs (Models s) p.1 p.2 ↔ shape p = true ∧ ∀ m, Models s m → atModel p m := by
  unfold SameInputs GeneralNominalDemandMerging.SameInputs
  rw [GeneralRebaseMergeCenters267.observed,GeneralRebaseMergeCenters267.observed,shape_exact]
  change (_ ∧ All₂ _ (givenNames _) (givenNames _)) ↔ _
  have origin (i j : Nat) : GeneralNominalDemandMerging.SameOrigin (Models s) (.source i) (.source j) ↔
      ∀ m, Models s m → Equivalent (m i).1 (m j).1 := by
    change GeneralNominalVersionedCycles232.Equal s (.source i) (.source j) ↔ _
    rw [GeneralRebaseSameInputs269.raw_source_eq]
    exact ⟨fun h m model => ⟨h.1 m model,h.2 m model⟩,
      fun h => ⟨fun m model => (h m model).1,fun m model => (h m model).2⟩⟩
  let related : Nat → Nat → Prop := fun i j => ∀ m, Models s m → Equivalent (m i).1 (m j).1
  let rel := fun a b => ∃ i j, a = some (GeneralNominalRecursiveInspection.Origin.source i) ∧
        b = some (GeneralNominalRecursiveInspection.Origin.source j) ∧ related i j
  have atPair (i j : Nat) : Related (Models s) (some (.source i)) (some (.source j)) ↔
      rel (some (.source i)) (some (.source j)) := by
    rw [related_source]
    refine (origin i j).trans ⟨fun h => ⟨i,j,rfl,rfl,h⟩,?_⟩
    rintro ⟨a,b,ha,hb,h⟩
    cases ha
    cases hb
    exact h
  have convert (as bs : List Nat) :
      All₂ (Related (Models s)) (givenNames as) (givenNames bs) ↔
        All₂ rel (givenNames as) (givenNames bs) := by
    induction as generalizing bs with
    | nil =>
      cases bs with
      | nil => exact ⟨fun _ => .nil,fun _ => .nil⟩
      | cons b bs => constructor <;> intro bad <;> cases bad
    | cons a as ih =>
      cases bs with
      | nil => constructor <;> intro bad <;> cases bad
      | cons b bs =>
        constructor
        · intro h
          cases h with
          | cons head tail => exact .cons ((atPair a b).mp head) ((ih bs).mp tail)
        · intro h
          cases h with
          | cons head tail => exact .cons ((atPair a b).mpr head) ((ih bs).mpr tail)
  rw [convert,(all₂_zip related)]
  constructor
  · rintro ⟨role,len,tests⟩
    exact ⟨⟨role,len⟩,fun m valid c listed => tests c listed m valid⟩
  · rintro ⟨⟨role,len⟩,tests⟩
    exact ⟨role,len,fun c listed m valid => tests m valid c listed⟩

theorem counter_exact (s : State roles) (p : Pair roles) :
    SameInputs (Models s) p.1 p.2 ↔ shape p = true ∧ ¬ ∃ m, counter s p m := by
  classical
  rw [semantic_exact]
  refine and_congr_right' ⟨fun each ⟨m,old,fail⟩ => fail (each m old),?_⟩
  intro missing m old
  exact Classical.byContradiction (fun fail => missing ⟨m,old,fail⟩)

def equal (samples : List Assignment) (test : Pair roles → Assignment → Bool) (p : Pair roles) : Bool :=
  shape p && !(hit samples test p)

theorem equal_exact (s : State roles) (pairs : List (Pair roles)) (samples : List Assignment)
    (cover : Covers (counter s) pairs samples) (test : Pair roles → Assignment → Bool)
    (p : Pair roles) (listed : p ∈ pairs)
    (cert : ∀ m ∈ samples, test p m = true ↔ counter s p m) :
    equal samples test p = true ↔ SameInputs (Models s) p.1 p.2 := by
  rw [counter_exact]
  unfold equal
  rw [Bool.and_eq_true,Bool.not_eq_true',
    GeneralRebaseFiniteWitnessTable297.hit_false _ _ _ cover _ _ listed cert]

end Yulang.GeneralRebaseMergeQuestions297
