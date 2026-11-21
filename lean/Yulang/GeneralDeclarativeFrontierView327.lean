import Yulang.GeneralDeclarativeCandidateScan327

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFrontierView327
open GeneralDeclarations (Declaration Registry Checked)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeLowerKnown321 (Ready Delayed ready_iff_not_delayed)
open GeneralDeclarativePriority321 (Candidates Survives Blocked Recurs Local)
open GeneralDeclarativeCandidateScan327 (viable exact_membership scan_blocked single)
open CommonRoleOutermostResolver (Frontier)

def decision (r : Registry) (d : Demand) (hasLower recursive : Bool)
    (passes waiting : Declaration → Bool) (produce : Declaration → Option (List Demand)) :
    Option (Frontier Demand) :=
  if hasLower then
    if recursive then some .rejected
    else if (viable r d waiting).isEmpty then
      match viable r d passes with
      | [] => some .rejected
      | [decl] => (produce decl).map (.selected decl.id)
      | _ :: _ :: _ => some .ambiguous
    else some .pending
  else if recursive then none else some .pending

/-- The selection table preserves a separate missing observation and
missing emitter. This is exact relative to independently established
source observers, not a verdict for an absent bridge. -/
structure ExactInputs (s : State) (r : Registry) (i : GeneralNominalInspection.Interpretation)
    {done : Nat → Prop} (p : Supported s done) (tests : Candidates) (d : Demand)
    (generates : Demand → Declaration → List Demand → Prop)
    (hasLower recursive : Bool) (passes waiting : Declaration → Bool)
    (produce : Declaration → Option (List Demand)) : Prop where
  lower : hasLower = true ↔ Ready p d
  k2 : recursive = true ↔ Recurs s r i tests d
  positive : ∀ decl ∈ r.declarations, decl.role = d.role → (passes decl = true ↔ tests.viable d decl)
  deferred : ∀ decl ∈ r.declarations, decl.role = d.role → (waiting decl = true ↔ tests.unresolved d decl)
  generation : Ready p d → ¬Recurs s r i tests d → ¬Blocked r tests d → ∀ decl,
    GeneralDeclarativeFrontier327.Unique r tests d decl →
    ∀ kids, produce decl = some kids ↔ generates d decl kids

theorem false_iff {b : Bool} (known : b = true ↔ prop) : b = false ↔ ¬prop := by
  cases b <;> simp_all

theorem two_differ {r : Registry} {d : Demand} (checked : Checked r)
    (seen : viable r d passes = a :: b :: more) : a.id ≠ b.id := by
  have unique : ((viable r d passes).map Declaration.id).Nodup :=
    List.Nodup.sublist (List.filter_sublist.map _) checked.1
  rw [seen] at unique
  intro same
  exact (List.nodup_cons.mp unique).1 (same.symm ▸ List.mem_cons_self)

theorem sound {s : State} {p : Supported s done} (checked : Checked r)
    (valid : ExactInputs s r i p tests d generates hasLower recursive passes waiting produce)
    (observed : decision r d hasLower recursive passes waiting produce = some f) :
    Local s r i p tests generates d f := by
  cases lower : hasLower
  · have delayed : Delayed p d := Classical.byContradiction fun no =>
      ((false_iff valid.lower).mp lower) ((ready_iff_not_delayed p d).mpr no)
    cases recurs : recursive
    · have safe := (false_iff valid.k2).mp recurs
      have exactF : f = .pending := by simpa [decision,lower,recurs,eq_comm] using observed
      subst f
      exact .unsupported delayed safe
    · simp [decision,lower,recurs] at observed
  · have ready := valid.lower.mp lower
    cases recurs : recursive
    · have safe := (false_iff valid.k2).mp recurs
      cases wait : (viable r d waiting).isEmpty
      · have blocked := (scan_blocked valid.deferred).mp wait
        have exactF : f = .pending := by simpa [decision,lower,recurs,wait,eq_comm] using observed
        subst f
        exact .unresolved ready safe blocked
      · have clear : ¬Blocked r tests d := fun blocked => by
          have falseWait := (scan_blocked valid.deferred).mpr blocked
          simp [wait] at falseWait
        cases scan : viable r d passes with
        | nil =>
          have exactF : f = .rejected := by simpa [decision,lower,recurs,wait,scan,eq_comm] using observed
          subst f
          refine .noCandidate ready safe clear (fun a viableOne => ?_)
          have wanted := (exact_membership valid.positive).mpr viableOne
          rw [scan] at wanted
          exact List.not_mem_nil wanted
        | cons a tail =>
          cases tail with
          | nil =>
            have picked := (single checked valid.positive).mp scan
            cases emitted : produce a with
            | none => simp [decision,lower,recurs,wait,scan,emitted] at observed
            | some kids =>
              have exactF : f = .selected a.id kids := by
                simpa [decision,lower,recurs,wait,scan,emitted,eq_comm] using observed
              subst f
              exact .selected ready safe clear picked.1 picked.2
                ((valid.generation ready safe clear a picked kids).mp emitted)
          | cons b more =>
            have exactF : f = .ambiguous := by simpa [decision,lower,recurs,wait,scan,eq_comm] using observed
            subst f
            have first := (exact_membership valid.positive).mp (scan ▸ List.mem_cons_self : a ∈ viable r d passes)
            have last := (exact_membership valid.positive).mp
              (scan ▸ List.mem_cons_of_mem _ List.mem_cons_self : b ∈ viable r d passes)
            exact .ambiguous ready safe clear first last (two_differ checked scan)
    · have exactF : f = .rejected := by simpa [decision,lower,recurs,eq_comm] using observed
      subst f
      exact .recursive ready (valid.k2.mp recurs)

theorem wait_empty {r : Registry} {d : Demand}
    (correct : ∀ decl ∈ r.declarations, decl.role = d.role → (waiting decl = true ↔ tests.unresolved d decl))
    (clear : ¬Blocked r tests d) : (viable r d waiting).isEmpty = true := by
  cases h : (viable r d waiting).isEmpty
  · exact False.elim (clear ((scan_blocked correct).mp h))
  · rfl

theorem none_viable {r : Registry} {d : Demand}
    (correct : ∀ decl ∈ r.declarations, decl.role = d.role → (passes decl = true ↔ tests.viable d decl))
    (none : ∀ decl, ¬Survives r tests d decl) : viable r d passes = [] := by
  cases snapshot : viable r d passes with
  | nil => rfl
  | cons first more =>
    exact False.elim (none first ((exact_membership correct).mp (snapshot ▸ List.mem_cons_self)))

theorem complete {s : State} {p : Supported s done} (checked : Checked r)
    (valid : ExactInputs s r i p tests d generates hasLower recursive passes waiting produce)
    (holds : Local s r i p tests generates d f) :
    decision r d hasLower recursive passes waiting produce = some f := by
  cases holds with
  | unsupported later safe =>
    have lower := (false_iff valid.lower).mpr (fun r => (ready_iff_not_delayed p d).mp r later)
    simp [decision,lower,(false_iff valid.k2).mpr safe]
  | recursive ready recurs => simp [decision,valid.lower.mpr ready,valid.k2.mpr recurs]
  | unresolved ready safe blocked =>
    simp [decision,valid.lower.mpr ready,(false_iff valid.k2).mpr safe,
      (scan_blocked valid.deferred).mpr blocked]
  | noCandidate ready safe clear none =>
    simp [decision,valid.lower.mpr ready,(false_iff valid.k2).mpr safe,
      wait_empty valid.deferred clear,none_viable valid.positive none]
  | ambiguous ready safe clear a b distinct =>
    have first := (exact_membership valid.positive).mpr a
    have last := (exact_membership valid.positive).mpr b
    cases seq : viable r d passes with
    | nil => rw [seq] at first; exact False.elim (List.not_mem_nil first)
    | cons x xs =>
      cases xs with
      | nil =>
        have firstOnly := List.mem_singleton.mp (seq ▸ first)
        have lastOnly := List.mem_singleton.mp (seq ▸ last)
        exact False.elim (distinct (congrArg Declaration.id (firstOnly.trans lastOnly.symm)))
      | cons y ys =>
        simp [decision,valid.lower.mpr ready,(false_iff valid.k2).mpr safe,
          wait_empty valid.deferred clear,seq]
  | selected ready safe clear here only generatesKids =>
    have sole := (single checked valid.positive).mpr ⟨here,only⟩
    have generated := (valid.generation ready safe clear _ ⟨here,only⟩ _).mpr generatesKids
    simp [decision,valid.lower.mpr ready,(false_iff valid.k2).mpr safe,
      wait_empty valid.deferred clear,sole,generated]

theorem exact {s : State} {p : Supported s done} (checked : Checked r)
    (valid : ExactInputs s r i p tests d generates hasLower recursive passes waiting produce) :
    decision r d hasLower recursive passes waiting produce = some f ↔
      Local s r i p tests generates d f :=
  ⟨sound checked valid,complete checked valid⟩

/-- The option's absence is not another resolver verdict. It reports
an unrepresented frontier, either the deliberately open overlap or
an absent compile witness in the unique positive branch. -/
theorem absent {s : State} {p : Supported s done} (checked : Checked r)
    (valid : ExactInputs s r i p tests d generates hasLower recursive passes waiting produce) :
    decision r d hasLower recursive passes waiting produce = none ↔
      ¬(GeneralDeclarativeFrontier327.NoOverlap s r i p tests d ∧
        GeneralDeclarativeFrontier327.CanGenerate s r i p tests generates d) := by
  rw [← GeneralDeclarativeFrontier327.coverage checked]
  constructor
  · rintro nowhere ⟨f,h⟩
    have observes := complete checked valid h
    rw [nowhere] at observes
    cases observes
  · intro no
    cases seen : decision r d hasLower recursive passes waiting produce with
    | none => rfl
    | some f => exact False.elim (no ⟨f,sound checked valid seen⟩)

end Yulang.GeneralDeclarativeFrontierView327
