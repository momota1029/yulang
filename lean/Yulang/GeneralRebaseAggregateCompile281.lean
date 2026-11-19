import Yulang.GeneralRebaseAggregateCollapse281

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseAggregateCompile281
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceState (Interval)
open GeneralNominalSaturationState (Packet)
open GeneralNominalAllocation (occurrences lower upper equations)
open GeneralNominalVersionedFrame231 (capture)
open GeneralRebasePortCopy280 (Write PairWrites)
open GeneralRebasePortProjection280 (Respects res_append)
open GeneralRebasePortMeaning280 (matches_refl)
open PresenceNormalForm (Atom All)

def repeated (sample : Interval) (others : List Interval) : Bool :=
  others.all (fun bounds => bounds == sample)

theorem repeated_exact (sample : Interval) (others : List Interval) :
    repeated sample others = true ↔ ∀ b ∈ others, b = sample := by
  unfold repeated
  simp only [List.all_eq_true,beq_iff_eq]

def compileBinder (p : Packet roles) (name : Nat) : Option (List Write) :=
  match occurrences p.bindings name with
  | [] => none
  | [_] => some []
  | sample :: next :: tail =>
    if repeated sample (next :: tail) then some (PairWrites ((capture p).inputs name) sample) else none

def rawBinder (p : Packet roles) (name : Nat) : List (Atom Nat) :=
  match occurrences p.bindings name with
  | [_] => []
  | bounds => equations ((capture p).inputs name).1 (lower bounds) ++
      equations ((capture p).inputs name).2 (upper bounds)

theorem binder_exact (p : Packet roles) (name : Nat) (m : Assignment)
    (compiled : compileBinder p name = some ws) :
    All CommonNominalFullCarrier.model m (rawBinder p name) ↔ Respects ws m := by
  cases h : occurrences p.bindings name with
  | nil => simp [compileBinder,h] at compiled
  | cons first tail =>
    cases tail with
    | nil =>
      have empty : ws = [] := (Option.some.inj (by simpa only [compileBinder,h] using compiled)).symm
      subst ws
      rw [rawBinder,h]
      constructor
      · intro _ _ mem; cases mem
      · intro _; exact PresenceNormalForm.all_nil _ _
    | cons next rest =>
      by_cases same : repeated first (next :: rest) = true
      · have formula : PairWrites ((capture p).inputs name) first = ws :=
          Option.some.inj (by simpa only [compileBinder,h,same,ite_true] using compiled)
        subst ws
        rw [rawBinder,h]
        apply GeneralRebaseAggregateCollapse281.collapse_atoms m _ _ List.mem_cons_self
        intro interval listed
        rcases List.mem_cons.mp listed with rfl|remaining
        · exact matches_refl m _
        · rw [(repeated_exact first (next::rest)).mp same _ remaining]
          exact matches_refl m _
      · simp [compileBinder,h,same] at compiled

def collect (p : Packet roles) : List Nat → Option (List Write)
  | [] => some []
  | name :: tail => do
    let head ← compileBinder p name
    let rest ← collect p tail
    pure (head ++ rest)

def compile (p : Packet roles) : Option (List Write) := collect p p.declaration.inputNames

theorem collect_exact (p : Packet roles) (names : List Nat) (m : Assignment)
    (compiled : collect p names = some ws) :
    All CommonNominalFullCarrier.model m (names.flatMap (rawBinder p)) ↔ Respects ws m := by
  induction names generalizing ws with
  | nil =>
    have empty : ws = [] := (Option.some.inj compiled).symm
    subst ws
    constructor
    · intro _ _ mem; cases mem
    · intro _; exact PresenceNormalForm.all_nil _ _
  | cons name rest ih =>
    unfold collect at compiled
    cases head : compileBinder p name with
    | none => simp [head] at compiled
    | some first =>
      cases tail : collect p rest with
      | none => simp [head,tail] at compiled
      | some last =>
        rw [head,tail] at compiled
        have eq : first ++ last = ws := Option.some.inj compiled
        subst ws
        rw [List.flatMap_cons,PresenceNormalForm.all_append,res_append]
        exact and_congr (binder_exact p name m head) (ih tail)

theorem packet_exact (p : Packet roles) (m : Assignment) (compiled : compile p = some ws) :
    All CommonNominalFullCarrier.model m
      (GeneralNominalVersionedAllocation231.merges p.context.state p.registry p.site.occurrence.identity
        p.declaration p.bindings) ↔ Respects ws m :=
  collect_exact p p.declaration.inputNames m compiled

end Yulang.GeneralRebaseAggregateCompile281
