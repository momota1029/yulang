import Yulang.GeneralRebaseSparseGate283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseClassFrontier283
open GeneralSourceState (Output)
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseEffectView243 (Equation)
open GeneralNominalRebaseRawView243 (Atom read)
open GeneralNominalRebaseClassView243 (View equations equations_exact)
open GeneralRebaseClassDelta283 (Growth EqPairs)
open Core.PresenceGeneration (CompTerm)
open PresenceNormalForm (All)
open CommonNominalFullCarrier (model Equivalent)

local instance : DecidableEq Output := fun a b =>
  if h : a.name = b.name ∧ a.target = b.target then
    isTrue (by cases a; cases b; cases h; congr)
  else isFalse (fun eq => h ⟨congrArg Output.name eq,congrArg Output.target eq⟩)

def fresh (prev next : List Output) : List Output :=
  next.filter (fun output => output ∉ prev)

theorem fresh_exact (prev next : List Output) (out : Output) :
    out ∈ fresh prev next ↔ out ∈ next ∧ out ∉ prev := by
  simp [fresh]

def pairs (prev next : List Output) : List (Output × Output) :=
  next.flatMap fun first => (next.filter fun last => first ∉ prev ∨ last ∉ prev).map (first,·)

theorem pairs_exact (prev next : List Output) (first last : Output) :
    (first,last) ∈ pairs prev next ↔ first ∈ next ∧ last ∈ next ∧ (first ∉ prev ∨ last ∉ prev) := by
  simp [pairs]

def pairAtoms (mapping : Nat → CompTerm Nat) (pair : Output × Output) : List Atom :=
  if pair.1.name = pair.2.name then
    [.tyLe (mapping pair.1.target).1 (mapping pair.2.target).1,
      .tyLe (mapping pair.2.target).1 (mapping pair.1.target).1]
  else []

theorem pair_exact (mapping : Nat → CompTerm Nat) (a : Assignment) (first last : Output) :
    All model a (pairAtoms mapping (first,last)) ↔
      (first.name = last.name → Equivalent ((read mapping a) first.target).1 ((read mapping a) last.target).1) := by
  by_cases h : first.name = last.name
  · simp only [pairAtoms,h,ite_true,All,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,
      forall_eq,true_implies]
    rfl
  · simp [pairAtoms,All,h]

def compile (plan : Plan roles) (mapping : Nat → CompTerm Nat) (prev next : List Output) : View :=
  ⟨equations plan mapping (fresh prev next),(pairs prev next).flatMap (pairAtoms mapping)⟩

theorem exact (plan : Plan roles) (mapping : Nat → CompTerm Nat) (prev next : List Output) (base : Assignment) :
    (compile plan mapping prev next).Holds base ↔
       Growth plan (read mapping base) (· ∈ prev) (· ∈ next) := by
  unfold compile View.Holds Growth
  rw [equations_exact]
  apply and_congr
  · simp only [GeneralRebaseClassDelta283.Bodies,fresh_exact,GeneralNominalVersionedEffects231.body_holds_iff]
  · unfold EqPairs All
    simp only [List.forall_mem_flatMap]
    constructor
    · intro h first last paired
      exact (pair_exact mapping base first last).mp
        (h (first,last) ((pairs_exact prev next first last).mpr paired))
    · intro h pair listed
      obtain ⟨first,last⟩ := pair
      exact (pair_exact mapping base first last).mpr
        (h first last ((pairs_exact prev next first last).mp listed))

theorem no_growth (plan : Plan roles) (a : Assignment) (old next : Output → Prop)
    (covered : ∀ out, next out → old out) : Growth plan a old next := by
  constructor
  · exact fun o present => False.elim (present.2 (covered o present.1))
  · intro first last present
    rcases present.2.2 with miss|miss
    · exact False.elim (miss (covered first present.1))
    · exact False.elim (miss (covered last present.2.1))

end Yulang.GeneralRebaseClassFrontier283
