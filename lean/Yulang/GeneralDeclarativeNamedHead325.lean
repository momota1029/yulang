import Yulang.GeneralDeclarativeHeadOrigin325
import Yulang.GeneralDeclarativeTermCapture322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNamedHead325
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeExactWalk323 (Exact)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeTermCapture322 (named Shared KnownNames named_binds first occurs_if repr_found)
open GeneralDeclarativeHeadOrigin325 (Read observed_binders by_equations)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeNFHead324 (fact)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (Constructors Pattern normalize normalizeArgs variablesArgs)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (All₂)

structure Inspected (s : State) (c : Constructors) (i : Interpretation)
    (a : Capture) (p : Pattern) (uses : List Occurrence) : Prop where
  range : Bounds s a
  read : ∃ actual code, Derives s (.variable a.center) actual ∧
    translate c i (normalize p) = some code ∧ Exact .actual actual code uses

inductive Ordered (s : State) (c : Constructors) (i : Interpretation) :
    List Capture → List Pattern → List Occurrence → Prop where
  | nil : Ordered s c i [] [] []
  | cons : Inspected s c i a p one → Ordered s c i as ps rest →
      Ordered s c i (a::as) (p::ps) (one++rest)

theorem incidence (reads : Ordered s c i args ps seen) :
    seen.map Occurrence.binder = variablesArgs (normalizeArgs ps) ∧
    ∀ o ∈ seen, o.mode = .actual := by
  induction reads with
  | nil => simp [variablesArgs,normalizeArgs]
  | cons head tail ih =>
    obtain ⟨_,_,_,written,exact⟩ := head.read
    obtain ⟨one,modes⟩ := observed_binders written exact
    refine ⟨by simp [List.map_append,one,ih.1,variablesArgs,normalizeArgs],?_⟩
    intro o h
    rcases List.mem_append.mp h with put|later
    · exact modes o put
    · exact ih.2 o later

theorem all_seen_have_anchors (reads : Ordered s c i args ps seen)
    (wanted : binder ∈ variablesArgs (normalizeArgs ps)) : ∃ rep, first seen binder = some rep := by
  rw [← (incidence reads).1] at wanted
  obtain ⟨occ,has,rfl⟩ := List.mem_map.mp wanted
  exact occurs_if has ((incidence reads).2 occ has)

/-- The single name table for the entire head is produced from the
ordinary pool, using a real first visible occurrence. A repeated
binder does not independently receive a name at each argument. -/
theorem named_ordered {s : State} (reads : Ordered s c i args ps seen)
    (included : seen ⊆ all) (sharing : Shared s all) (coverage : KnownNames s all pool)
    (initial : Nat → Capture) :
    All₂ (fun a p => Bounds s a ∧ Result s (fact c i (named s all pool initial) a p)) args ps := by
  induction reads with
  | nil => exact .nil
  | @cons a p one as ps rest head tail ih =>
    obtain ⟨actual,code,center,written,walked⟩ := head.read
    have firstSubset : one ⊆ all := fun _ ha => included (List.mem_append_left _ ha)
    have restSubset : rest ⊆ all := fun _ ha => included (List.mem_append_right _ ha)
    exact .cons (by_equations (⟨head.range,actual,code,one,center,written,walked,
      fun o h => named_binds firstSubset sharing coverage walked.walked o h⟩ :
      Read s c i (named s all pool initial) a p)) (ih restSubset)

end Yulang.GeneralDeclarativeNamedHead325
