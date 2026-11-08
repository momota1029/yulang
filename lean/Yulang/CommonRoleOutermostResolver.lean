import Lean

/-!
# The outer recursion of interval role resolution

This module closes the *outer* protocol, conditionally on two named bridges:
`FrontierExact` and accessibility of the generated where requests. It does
not supply either bridge for the complete Yulang source/interval carrier.
In particular a graph inspection observation is not an implementation of a
`Protocol` satisfying the intended source `Local` judgment.

`Request` includes the demand and its constraint state. The protocol closes
over the root caller's fixed visible declarations. A selected frontier must
already include propagated associated equations and **every** where request,
after substitution of merged interval bindings. The same protocol is used
for all children. No point assignment is searched by the outer recursion.

The independent judgments below do not mention `resolve`. Accessibility is
an explicit proof argument, not a bound on execution depth or a role rank.
The trace retains all children, even when one of them fails. Only an entirely
successful trace projects to a finite dictionary.

This is a fixed-frontier recursion: children return trees, not updated
constraint states. Threading changes from one child through its siblings,
recollecting parent frontiers, and proving snapshot stability remain part of
the missing source bridge. The cross-child summary policy is a protocol
policy; the specification's K2 priority concerns candidates of one demand.
-/
namespace Yulang.CommonRoleOutermostResolver

universe u

inductive Frontier (Request : Type u) where
  | pending
  | selected (key : Nat) (children : List Request)
  | ambiguous
  | rejected

/-- The executable producer and its independent declarative boundary are
separate fields. The bridge between them is an explicit theorem hypothesis.
`Local` must be supplied by interval propagation rules, not defined as an
equality with `frontier`, when instantiating the source calculus. -/
structure Protocol (Request : Type u) where
  frontier : Request → Frontier Request
  Local : Request → Frontier Request → Prop

def FrontierExact (protocol : Protocol Request) : Prop :=
  ∀ request frontier, protocol.frontier request = frontier ↔ protocol.Local request frontier

/-- Independent where dependency. This relation does not call the producer. -/
def Child (localRule : Request → Frontier Request → Prop) (child parent : Request) : Prop :=
  ∃ key children, localRule parent (.selected key children) ∧ child ∈ children

inductive Tree where
  | pending
  | selected (key : Nat) (children : List Tree)
  | ambiguous
  | rejected
  deriving Repr

inductive Dictionary where
  | node (key : Nat) (children : List Dictionary)
  deriving Repr

inductive Result where
  | pending
  | selected (dictionary : Dictionary)
  | ambiguous
  | rejected
  deriving Repr

/-- An ordered relation on complete finite child lists. -/
inductive All₂ (relation : α → β → Prop) : List α → List β → Prop where
  | nil : All₂ relation [] []
  | cons : relation first last → All₂ relation before after →
      All₂ relation (first :: before) (last :: after)

/-- Independent finite resolution derivations, including exact ordered
where children and declaration identities. -/
inductive Resolves (localRule : Request → Frontier Request → Prop) : Request → Tree → Prop where
  | pending : localRule request .pending → Resolves localRule request .pending
  | ambiguous : localRule request .ambiguous → Resolves localRule request .ambiguous
  | rejected : localRule request .rejected → Resolves localRule request .rejected
  | selected : localRule request (.selected key requests) →
      All₂ (Resolves localRule) requests trees →
      Resolves localRule request (.selected key trees)

/-- The single recursive entry. The accessibility proof covers exactly the
independent generated where relation; the frontier bridge justifies every
recursive call. Neither missing hypothesis is hidden as an axiom. -/
def resolve (protocol : Protocol Request) (exact : FrontierExact protocol)
    (request : Request) (accessible : Acc (Child protocol.Local) request) : Tree :=
  accessible.rec (motive := fun _ _ => Tree) fun parent _ recurse =>
    match observed : protocol.frontier parent with
    | .pending => .pending
    | .ambiguous => .ambiguous
    | .rejected => .rejected
    | .selected key children =>
        .selected key (children.attach.map fun child =>
          recurse child.val ⟨key, children, (exact parent _).mp observed, child.property⟩)

theorem resolve_unfold (protocol : Protocol Request) (exact : FrontierExact protocol)
    (request : Request) (accessible : Acc (Child protocol.Local) request) :
    resolve protocol exact request accessible =
      match observed : protocol.frontier request with
      | .pending => .pending
      | .ambiguous => .ambiguous
      | .rejected => .rejected
      | .selected key children =>
          .selected key (children.attach.map fun child =>
            resolve protocol exact child.val
              (accessible.inv ⟨key, children, (exact request _).mp observed, child.property⟩)) := by
  cases accessible
  rfl

/-- Exactness before summarizing child failures. There is no support,
success, fuel, rank, or output-derivation premise. The two remaining source
bridges are exactly `exact` and `accessible`, explicit in the statement. -/
theorem resolve_tree_exact_of_frontier_exact (protocol : Protocol Request)
    (exact : FrontierExact protocol) (request : Request)
    (accessible : Acc (Child protocol.Local) request) (tree : Tree) :
    resolve protocol exact request accessible = tree ↔ Resolves protocol.Local request tree := by
  induction accessible generalizing tree with
  | intro request predecessors ih =>
      rw [resolve_unfold]
      split
      next observed =>
          constructor
          · rintro rfl
            exact .pending ((exact request _).mp observed)
          · intro derivation
            cases derivation with
            | pending => rfl
            | ambiguous h => have := (exact request _).mpr h; simp [observed] at this
            | rejected h => have := (exact request _).mpr h; simp [observed] at this
            | selected h _ => have := (exact request _).mpr h; simp [observed] at this
      next observed =>
          constructor
          · rintro rfl
            exact .ambiguous ((exact request _).mp observed)
          · intro derivation
            cases derivation with
            | ambiguous => rfl
            | pending h => have := (exact request _).mpr h; simp [observed] at this
            | rejected h => have := (exact request _).mpr h; simp [observed] at this
            | selected h _ => have := (exact request _).mpr h; simp [observed] at this
      next observed =>
          constructor
          · rintro rfl
            exact .rejected ((exact request _).mp observed)
          · intro derivation
            cases derivation with
            | rejected => rfl
            | pending h => have := (exact request _).mpr h; simp [observed] at this
            | ambiguous h => have := (exact request _).mpr h; simp [observed] at this
            | selected h _ => have := (exact request _).mpr h; simp [observed] at this
      next key children observed =>
          let runChild := fun child : { c // c ∈ children } =>
            resolve protocol exact child.val
              (predecessors child.val ⟨key, children, (exact request _).mp observed, child.property⟩)
          have childExact (child : { c // c ∈ children }) (tree : Tree) :
              runChild child = tree ↔ Resolves protocol.Local child.val tree :=
            ih child.val ⟨key, children, (exact request _).mp observed, child.property⟩ tree
          have allChildren : All₂ (Resolves protocol.Local) children
              (children.attach.map runChild) := by
            have aux (xs : List { c // c ∈ children }) :
                All₂ (Resolves protocol.Local) (xs.map Subtype.val) (xs.map runChild) := by
              induction xs with
              | nil => exact .nil
              | cons child rest restIH =>
                  exact .cons ((childExact child _).mp rfl) restIH
            simpa using aux children.attach
          change Tree.selected key (children.attach.map runChild) = tree ↔ _
          constructor
          · rintro rfl
            exact .selected ((exact request _).mp observed) allChildren
          · intro derivation
            cases derivation with
            | pending h => have := (exact request _).mpr h; simp [observed] at this
            | ambiguous h => have := (exact request _).mpr h; simp [observed] at this
            | rejected h => have := (exact request _).mpr h; simp [observed] at this
            | selected h childrenDerivations =>
                have same := (exact request _).mpr h
                rw [observed] at same
                cases same
                congr 1
                have aux (xs : List { c // c ∈ children }) (ys : List Tree)
                    (related : All₂ (Resolves protocol.Local) (xs.map Subtype.val) ys) :
                    xs.map runChild = ys := by
                  induction xs generalizing ys with
                  | nil => cases related; rfl
                  | cons child rest restIH =>
                      cases related with
                      | cons first last =>
                          exact congr (congrArg List.cons ((childExact child _).mpr first)) (restIH _ last)
                apply aux children.attach
                simpa using childrenDerivations

def Result.isRejected : Result → Bool
  | .rejected => true
  | _ => false

def Result.isAmbiguous : Result → Bool
  | .ambiguous => true
  | _ => false

def Result.isPending : Result → Bool
  | .pending => true
  | _ => false

def Result.dictionary : Result → Option Dictionary
  | .selected dictionary => some dictionary
  | _ => none

/-- A projection of all visited where outcomes. The tree keeps every
failure, so this summary order does not choose a diagnostic or skip a child. -/
def combine (key : Nat) (results : List Result) : Result :=
  if results.any Result.isRejected then .rejected
  else if results.any Result.isAmbiguous then .ambiguous
  else if results.any Result.isPending then .pending
  else .selected (.node key (results.filterMap Result.dictionary))

/-- Independent rules for completion of the full where list. In particular
the success rule requires exactly one dictionary per child, in order. -/
inductive Combine (key : Nat) (results : List Result) : Result → Prop where
  | rejected : .rejected ∈ results → Combine key results .rejected
  | ambiguous : .rejected ∉ results → .ambiguous ∈ results → Combine key results .ambiguous
  | pending : .rejected ∉ results → .ambiguous ∉ results → .pending ∈ results →
      Combine key results .pending
  | selected : results = dictionaries.map Result.selected →
      Combine key results (.selected (.node key dictionaries))

theorem any_rejected_exact (results : List Result) :
    results.any Result.isRejected = true ↔ .rejected ∈ results := by
  induction results with
  | nil => simp
  | cons first rest ih => cases first <;> simp [Result.isRejected, ih]

theorem any_ambiguous_exact (results : List Result) :
    results.any Result.isAmbiguous = true ↔ .ambiguous ∈ results := by
  induction results with
  | nil => simp
  | cons first rest ih => cases first <;> simp [Result.isAmbiguous, ih]

theorem any_pending_exact (results : List Result) :
    results.any Result.isPending = true ↔ .pending ∈ results := by
  induction results with
  | nil => simp
  | cons first rest ih => cases first <;> simp [Result.isPending, ih]

theorem all_successful (results : List Result)
    (noRejected : .rejected ∉ results) (noAmbiguous : .ambiguous ∉ results)
    (noPending : .pending ∉ results) :
    results = (results.filterMap Result.dictionary).map Result.selected := by
  induction results with
  | nil => rfl
  | cons first rest ih =>
      have restNoRejected : .rejected ∉ rest := fun h => noRejected (List.mem_cons_of_mem _ h)
      have restNoAmbiguous : .ambiguous ∉ rest := fun h => noAmbiguous (List.mem_cons_of_mem _ h)
      have restNoPending : .pending ∉ rest := fun h => noPending (List.mem_cons_of_mem _ h)
      cases first with
      | rejected => exact False.elim (noRejected List.mem_cons_self)
      | ambiguous => exact False.elim (noAmbiguous List.mem_cons_self)
      | pending => exact False.elim (noPending List.mem_cons_self)
      | selected dictionary =>
          simpa [Result.dictionary] using
            congrArg (List.cons (.selected dictionary)) (ih restNoRejected restNoAmbiguous restNoPending)

theorem combine_exact (key : Nat) (results : List Result) (result : Result) :
    combine key results = result ↔ Combine key results result := by
  constructor
  · intro computed
    unfold combine at computed
    split at computed
    · subst result
      exact .rejected ((any_rejected_exact results).mp ‹_›)
    · rename_i noRejected
      have noRejected' : .rejected ∉ results := fun h => noRejected ((any_rejected_exact _).mpr h)
      split at computed
      · subst result
        exact .ambiguous noRejected' ((any_ambiguous_exact results).mp ‹_›)
      · rename_i noAmbiguous
        have noAmbiguous' : .ambiguous ∉ results := fun h => noAmbiguous ((any_ambiguous_exact _).mpr h)
        split at computed
        · subst result
          exact .pending noRejected' noAmbiguous' ((any_pending_exact results).mp ‹_›)
        · rename_i noPending
          subst result
          apply Combine.selected
          apply all_successful results noRejected' noAmbiguous'
          exact fun h => noPending ((any_pending_exact _).mpr h)
  · intro derivation
    cases derivation with
    | rejected h => simp [combine, (any_rejected_exact _).mpr h]
    | ambiguous noRejected h =>
        have noRejected' : results.any Result.isRejected = false := by
          cases observed : results.any Result.isRejected
          · rfl
          · exact False.elim (noRejected ((any_rejected_exact _).mp observed))
        simp [combine, noRejected', (any_ambiguous_exact _).mpr h]
    | pending noRejected noAmbiguous h =>
        have noRejected' : results.any Result.isRejected = false := by
          cases observed : results.any Result.isRejected
          · rfl
          · exact False.elim (noRejected ((any_rejected_exact _).mp observed))
        have noAmbiguous' : results.any Result.isAmbiguous = false := by
          cases observed : results.any Result.isAmbiguous
          · rfl
          · exact False.elim (noAmbiguous ((any_ambiguous_exact _).mp observed))
        simp [combine, noRejected', noAmbiguous', (any_pending_exact _).mpr h]
    | selected all =>
        subst results
        simp [combine, List.any_map, Function.comp_def, Result.isRejected,
          Result.isAmbiguous, Result.isPending, Result.dictionary, List.filterMap_map]

mutual
  def classification : Tree → Result
    | .pending => .pending
    | .ambiguous => .ambiguous
    | .rejected => .rejected
    | .selected key children => combine key (classifications children)

  def classifications : List Tree → List Result
    | [] => []
    | first :: rest => classification first :: classifications rest
end

/-- Independent finite-tree summary, separate from the executable fold. -/
inductive Summarizes : Tree → Result → Prop where
  | pending : Summarizes .pending .pending
  | ambiguous : Summarizes .ambiguous .ambiguous
  | rejected : Summarizes .rejected .rejected
  | selected : All₂ Summarizes trees results → Combine key results result →
      Summarizes (.selected key trees) result

mutual
  theorem classification_exact (tree : Tree) (result : Result) :
      classification tree = result ↔ Summarizes tree result := by
    cases tree with
    | pending =>
        constructor
        · rintro rfl; exact .pending
        · intro h; cases h; rfl
    | ambiguous =>
        constructor
        · rintro rfl; exact .ambiguous
        · intro h; cases h; rfl
    | rejected =>
        constructor
        · rintro rfl; exact .rejected
        · intro h; cases h; rfl
    | selected key children =>
        change combine key (classifications children) = result ↔ _
        constructor
        · intro h
          exact .selected ((classifications_exact children _).mp rfl) ((combine_exact _ _ _).mp h)
        · intro h
          cases h with
          | selected childSummaries combined =>
              rw [(classifications_exact children _).mpr childSummaries]
              exact (combine_exact _ _ _).mpr combined
  termination_by sizeOf tree

  theorem classifications_exact (trees : List Tree) (results : List Result) :
      classifications trees = results ↔ All₂ Summarizes trees results := by
    cases trees with
    | nil =>
        constructor
        · rintro rfl; exact .nil
        · intro h; cases h; rfl
    | cons first rest =>
        constructor
        · rintro rfl
          exact .cons ((classification_exact first _).mp rfl) ((classifications_exact rest _).mp rfl)
        · intro h
          cases h with
          | cons head tail =>
              simp only [classifications, (classification_exact first _).mpr head,
                (classifications_exact rest _).mpr tail]
  termination_by sizeOf trees
end

/-- Independent declarative four-way classification. `Resolves` checks the
local decisions and every child; `Summarizes` permits a selected result only
when the complete finite dictionary exists. Neither calls `resolve`. -/
def Classify (localRule : Request → Frontier Request → Prop) (request : Request)
    (result : Result) : Prop :=
  ∃ tree, Resolves localRule request tree ∧ Summarizes tree result

/-- Exact outer classification for every protocol, independently specified
local judgment, exact frontier implementation, accessible request, and
proposed result. This conditional theorem is not `source_frontier_exact`
or `checked_interval_children_accessible`, and is not the whole B4 E1. -/
theorem resolve_exact_of_frontier_exact (protocol : Protocol Request)
    (exact : FrontierExact protocol) (request : Request)
    (accessible : Acc (Child protocol.Local) request) (result : Result) :
    classification (resolve protocol exact request accessible) = result ↔
      Classify protocol.Local request result := by
  constructor
  · intro computed
    exact ⟨_, (resolve_tree_exact_of_frontier_exact protocol exact request accessible _).mp rfl,
      (classification_exact _ _).mp computed⟩
  · rintro ⟨tree, resolved, summarized⟩
    rw [(resolve_tree_exact_of_frontier_exact protocol exact request accessible tree).mpr resolved]
    exact (classification_exact _ _).mpr summarized

end Yulang.CommonRoleOutermostResolver
