import Yulang.GeneralDeclarativeCaptureClosure320
import Yulang.GeneralDeclarativeLinear320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14500
set_option maxHeartbeats 4100000
namespace Yulang.GeneralDeclarativeRepeatedHead320
open GeneralDeclarations (Declaration Registry)
open GeneralDeclarationPatterns (Pattern Constructors)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Bounds HeadArg)
open GeneralDeclarativeLinear320 (table captures table_order keys argument_mem map_right)
open GeneralDeclarativeNormalized320 (ordered_map)
open GeneralDeclarativeMerge320 (EqualTerm Merge lower upper)
open GeneralDeclarativeCaptureClosure320 (Origin)
open GeneralDeclarativeBounds319 (Bound)
open CommonRoleOutermostResolver (All₂)

theorem representative {entries : List (Nat × Capture)} {name : Nat}
    (known : ∃ arg, (name,arg) ∈ entries) :
    (name,captures entries name) ∈ entries := by
  induction entries with
  | nil =>
    obtain ⟨_,used⟩ := known
    cases used
  | cons entry rest ih =>
    rcases entry with ⟨k,bounds⟩
    by_cases same : k = name
    · subst k
      simp [captures]
    · obtain ⟨arg,used⟩ := known
      rcases List.mem_cons.mp used with equal|tail
      · exact False.elim (same (congrArg Prod.fst equal.symm))
      · simp only [captures,same,ite_false]
        exact List.mem_cons_of_mem _ (ih ⟨arg,tail⟩)

def capture (entries : List (Nat × Capture)) (lo hi : Nat → Nat) (name : Nat) : Capture :=
  ⟨lo name,(captures entries name).center,hi name⟩

/-- This compares actual logical sources from the normal state, not interval
overlap, role identity, or a chosen matching model. -/
def CentersAgree (s : State) (entries : List (Nat × Capture)) : Prop :=
  ∀ name a b, (name,a) ∈ entries → (name,b) ∈ entries → Bound s.normal a.center b.center

def occurrences (entries : List (Nat × Capture)) (name : Nat) : List Capture :=
  entries.filterMap fun pr => if pr.1 = name then some pr.2 else none

theorem occurrence_iff {entries : List (Nat × Capture)} {name : Nat} {arg : Capture} :
    arg ∈ occurrences entries name ↔ (name,arg) ∈ entries := by
  unfold occurrences
  constructor
  · intro found
    obtain ⟨⟨key,a⟩,member,read⟩ := List.mem_filterMap.mp found
    by_cases same : key = name
    · subst key
      have sameValue : a = arg := by simpa using read
      cases sameValue
      exact member
    · simp [same] at read
  · intro known
    exact List.mem_filterMap.mpr ⟨(name,arg),known,by simp⟩

theorem exists_binding {names : List Nat} {args : List Capture} {name : Nat}
    (length : names.length = args.length) (seen : name ∈ names) :
    ∃ arg, (name,arg) ∈ table names args := by
  rw [← keys length] at seen
  obtain ⟨⟨key,arg⟩,used,eq⟩ := List.mem_map.mp seen
  change key = name at eq
  subst key
  exact ⟨arg,used⟩

/-- Actual variable reads are synthesized even when the name repeats.
Only the shared actual proof is used for the head. The merged bounds
below are needed when those same variables appear in emitted demands. -/
theorem repeated_head {s c interp names args lo hi}
    (length : names.length = args.length)
    (bounded : ∀ a ∈ args, Bounds s a) (shared : CentersAgree s (table names args)) :
    All₂ (HeadArg s c interp (capture (table names args) lo hi)) args (names.map Pattern.var) := by
  apply map_right
  apply ordered_map (table_order length)
  intro arg listed name _ found
  have chosen := representative ⟨arg,found⟩
  refine ⟨bounded arg listed,.variable name,rfl,.capture ?_ ?_⟩
  · exact shared name arg (captures (table names args) name) found chosen
  · exact shared name (captures (table names args) name) arg chosen found

/-- The actual center of each merged capture is selected deterministically
as the first occurrence. If normal constraints contain its correct join and
meet equalities, no additional premise asserting that merged interval fits
is needed. -/
theorem repeated_origins {s names args lo hi}
    (length : names.length = args.length)
    (bounded : ∀ a ∈ args, Bounds s a) (shared : CentersAgree s (table names args))
    (merged : ∀ name ∈ names, ∀ first rest, occurrences (table names args) name = first :: rest →
      EqualTerm s (lo name) (lower first rest) ∧ EqualTerm s (hi name) (upper first rest)) :
    ∀ name ∈ names, Origin s (capture (table names args) lo hi name) := by
  intro name mentioned
  obtain ⟨arg,point⟩ := exists_binding length mentioned
  have chosen := representative ⟨arg,point⟩
  cases shape : occurrences (table names args) name with
  | nil =>
    have impossible := occurrence_iff.mpr point
    rw [shape] at impossible
    cases impossible
  | cons first rest =>
    refine .inr ⟨first,rest,?_,?_,(merged name mentioned first rest shape).1,
      (merged name mentioned first rest shape).2⟩
    · intro entry used
      exact bounded entry (argument_mem (occurrence_iff.mp (shape.symm ▸ used)))
    · intro entry used
      have appears := occurrence_iff.mp (shape.symm ▸ used)
      exact ⟨shared name entry (captures (table names args) name) appears chosen,
        shared name (captures (table names args) name) entry chosen appears⟩

end Yulang.GeneralDeclarativeRepeatedHead320
