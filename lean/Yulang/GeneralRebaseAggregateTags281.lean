import Yulang.GeneralRebaseAggregateLift281

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
namespace Yulang.GeneralRebaseAggregateTags281
open GeneralNominalSaturationState (Packet)
open GeneralNominalIdentities (Origin source source_identity)
open GeneralNominalAllocation (occurrences origin)
open GeneralNominalVersionedFrame231 (capture)
open GeneralRebaseAggregateCompile281 (repeated compileBinder compile collect)
open GeneralRebaseAggregateSupport281 (endKey endpoint)
open GeneralRebasePortCopy280 (Write PairWrites)

structure Tag where
  binder : Nat
  upper : Bool
  read : Nat
  deriving DecidableEq, Repr

def tag (p : Packet roles) (name : Nat) : Option (List Tag) :=
  match occurrences p.bindings name with
  | [] => none
  | [_] => some []
  | first :: next :: tail =>
    if repeated first (next :: tail) then some [⟨name,false,first.1⟩,⟨name,true,first.2⟩] else none

def collectTags (p : Packet roles) : List Nat → Option (List Tag)
  | [] => some []
  | name :: rest => do
    let first ← tag p name
    let after ← collectTags p rest
    pure (first ++ after)

def tags (p : Packet roles) : Option (List Tag) := collectTags p p.declaration.inputNames

def versioned (p : Packet roles) (t : Tag) : Write :=
  (source p.context.state.seed (endKey p t.binder t.upper),t.read)

def fixedOrigin (parent declaration : Nat) (t : Tag) : Origin :=
  origin parent declaration (if t.upper then 1 else 0) t.binder 0

def fixed (p : Packet roles) (t : Tag) : Write :=
  (source p.context.state.seed (fixedOrigin p.site.occurrence.identity p.declaration.id t),t.read)

def fixedWrites (p : Packet roles) : Option (List Write) :=
  (tags p).map (List.map (fixed p))

theorem binder_exact (p : Packet roles) (name : Nat) :
    (tag p name).map (List.map (versioned p)) = compileBinder p name := by
  unfold tag compileBinder
  cases observed : occurrences p.bindings name with
  | nil => rfl
  | cons first tail =>
    cases tail with
    | nil => rfl
    | cons next tail =>
      change (if repeated first (next::tail) then some [Tag.mk name false first.1,Tag.mk name true first.2] else none).map
        (List.map (versioned p)) = (if repeated first (next::tail) then some (PairWrites ((capture p).inputs name) first) else none)
      by_cases same : repeated first (next::tail) = true
      · rw [ite_eq_left same,ite_eq_left same]
        change some [(source p.context.state.seed (endKey p name false),first.1),
          (source p.context.state.seed (endKey p name true),first.2)] =
          some (PairWrites ((capture p).inputs name) first)
        have h :
            (capture p).inputs name =
              (source p.context.state.seed (endKey p name false),
               source p.context.state.seed (endKey p name true)) := by
          change (GeneralNominalVersionedAllocation231.capture _ _ _ _ _).inputs name = _
          simp only [GeneralNominalVersionedAllocation231.capture,observed]
          rfl
        rw [h]
        rfl
      · simp only [ite_eq_right same,Option.map_none]

theorem collect_exact (p : Packet roles) (names : List Nat) :
    (collectTags p names).map (List.map (versioned p)) = collect p names := by
  induction names with
  | nil => rfl
  | cons first rest ih =>
    unfold collectTags collect
    rw [← binder_exact p first,← ih]
    cases tag p first <;> cases collectTags p rest <;> try rfl
    rename_i left right
    exact congrArg some List.map_append

theorem versioned_exact (p : Packet roles) :
    (tags p).map (List.map (versioned p)) = compile p :=
  collect_exact p p.declaration.inputNames

theorem fixed_independent {p q : Packet roles} (seed : p.context.state.seed = q.context.state.seed)
    (owner : p.site.occurrence.identity = q.site.occurrence.identity) (same : p.declaration.id = q.declaration.id)
    (t : Tag) : fixed p t = fixed q t := by
  unfold fixed
  rw [seed,owner,same]

theorem fixed_reads (p : Packet roles) (t : Tag) : (fixed p t).2 = (versioned p t).2 := rfl

end Yulang.GeneralRebaseAggregateTags281
