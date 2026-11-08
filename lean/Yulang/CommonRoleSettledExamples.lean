import Yulang.CommonRoleSettledResolver
import Yulang.CommonRoleSettledGraphBridge

/-! X6 and X8–X12 through the SINGLE outer entry. Source: spec/06-roles.md
6.2–6.5 and the 2026-11-08 conformance list. These are lowered, settled
role requests, not source-expression inference or Core.infer integration. -/
namespace Yulang.CommonRoleSettledExamples
open CommonRoleSettledSyntax CommonRoleSettledConstraints CommonRoleSettledFrontier
open CommonRoleSettledResolver
open CommonRoleOutermostResolver (Tree Result Dictionary Classify)
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem propagate_empty (p : Pattern) (t : Ty) :
    propagate (State.empty : State n) p t = rigid p t := by
  have model : (State.empty : State n).Models :=
    ⟨fun _ => Core.PresenceGeneration.Comp.pure Common.model .bottom, (by intro a h; cases h)⟩
  have h : propagate (State.empty : State n) p t = true ↔ rigid p t = true := by
    rw [propagate_exact, rigid_exact]
    exact and_iff_right model
  cases a : propagate (State.empty : State n) p t <;> cases b : rigid p t <;> simp_all

def int : Ty := .atom .int
def tickInt : Ty := .wrap (.variant 0) int
def loop : Ty := .recordLoop 1
def listLoop : Ty := .wrap (.nominal 0) loop
def boxedLoop : Ty := .wrap (.record 0) loop
def tree : Ty := .atom (.named 9)

def mergedTick : Declaration := ⟨0, 0, .wrap (.variant 0) (.bind 0 [1]), []⟩
def concreteTick : Declaration := ⟨0, 1, .wrap (.variant 0) (.atom .int), []⟩
def lenList : Declaration := ⟨1, 2, .wrap (.nominal 0) (.bind 0 []), []⟩
def showList : Declaration := ⟨2, 3, .wrap (.nominal 0) (.bind 0 []), [(2, .var 0)]⟩
def checkNested : Declaration :=
  ⟨3, 4, .wrap (.record 0) (.wrap (.record 1) (.bind 0 [])), [(3, .wrap (.record 0) (.var 0))]⟩
def checkOpaque : Declaration := ⟨3, 5, .wrap (.record 0) (.bind 0 []), []⟩
def checkInspect : Declaration := ⟨3, 6, .wrap (.record 0) (.wrap (.record 1) (.bind 1 [])), []⟩
def showTree : Declaration := ⟨2, 7, .atom (.named 9), []⟩

def x6Single : Registry := ⟨[mergedTick], by intro d h; simp only [List.mem_singleton] at h; subst d; decide +kernel,
  by decide +kernel⟩
def x6Registry : Registry := ⟨[mergedTick, concreteTick], by
  intro d h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> decide +kernel, by decide +kernel⟩
def x8Registry : Registry := ⟨[lenList], by intro d h; simp only [List.mem_singleton] at h; subst d; decide +kernel,
  by decide +kernel⟩
def x9Registry : Registry := ⟨[showList], by intro d h; simp only [List.mem_singleton] at h; subst d; decide +kernel,
  by decide +kernel⟩
def x10Registry : Registry := ⟨[checkNested], by intro d h; simp only [List.mem_singleton] at h; subst d; decide +kernel,
  by decide +kernel⟩
def x11Registry : Registry := ⟨[checkOpaque, checkInspect], by
  intro d h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> decide +kernel, by decide +kernel⟩
def x12Registry : Registry := ⟨[showTree], by intro d h; simp only [List.mem_singleton] at h; subst d; decide +kernel,
  by decide +kernel⟩

def request (role : Nat) (t : Ty) : Request 0 := .known role t .empty

theorem tick_finite : tickInt.regular = false := by decide +kernel
theorem list_finite : listLoop.regular = false := by decide +kernel
theorem box_finite : boxedLoop.regular = false := by decide +kernel
theorem loop_cyclic : loop.regular = true := (loop_regular 1).2

/-- The normalization of the repeated tag puts BOTH original plain names in
one merged payload binder; the emitted captures retain both entire pairs. -/
theorem x6_merged_capture :
    inspect mergedTick.head tickInt = .hit int ∧
      bindings mergedTick.head int = [(0, (int, int)), (1, (int, int))] := by
  constructor
  · simp [inspect, mergedTick, tickInt, show (Ty.wrap (.variant 0) int).regular = false from tick_finite]
  · rfl

private theorem x6_frontier : frontier x6Registry.declarations (request 0 tickInt) = .ambiguous := by
  simp [frontier, request, Request.known, x6Registry, scan, trial, encode, propagate_empty,
    mergedTick, concreteTick, rigid, inspect, tickInt, int, summarize, hits,
    show (Ty.wrap (.variant 0) (.atom .int)).regular = false from tick_finite]

private theorem x6_single_frontier : frontier x6Single.declarations (request 0 tickInt) = .selected 0 [] := by
  simp [frontier, request, Request.known, x6Single, scan, trial, encode, propagate_empty,
    mergedTick, rigid, inspect, tickInt, int, summarize, hits, children,
    show (Ty.wrap (.variant 0) (.atom .int)).regular = false from tick_finite]

private theorem x8_frontier : frontier x8Registry.declarations (request 1 listLoop) = .selected 2 [] := by
  simp [frontier, request, Request.known, x8Registry, scan, trial, encode, propagate_empty,
    lenList, rigid, inspect, listLoop, summarize, hits, children,
    show (Ty.wrap (.nominal 0) loop).regular = false from list_finite]

private theorem x9_frontier : frontier x9Registry.declarations (request 2 listLoop) =
    .selected 3 [request 2 loop] := by
  simp [frontier, request, Request.known, x9Registry, scan, trial, encode, propagate_empty,
    showList, rigid, inspect, listLoop, summarize, hits, children, Template.instantiate,
    show (Ty.wrap (.nominal 0) loop).regular = false from list_finite]

private theorem cycle_frontier (visible : List Declaration) (role : Nat) :
    frontier visible (request role loop) = .rejected := by
  simp [frontier, request, Request.known, loop, loop_regular]

private theorem x10_frontier : frontier x10Registry.declarations (request 3 boxedLoop) = .rejected := by
  simp [frontier, request, Request.known, x10Registry, scan, trial, encode, propagate_empty,
    checkNested, rigid, inspect, boxedLoop, loop, loop_regular, summarize,
    show (Ty.wrap (.record 0) (.recordLoop 1)).regular = false from box_finite]

private theorem x11_frontier : frontier x11Registry.declarations (request 3 boxedLoop) = .rejected := by
  simp [frontier, request, Request.known, x11Registry, scan, trial, encode, propagate_empty,
    checkOpaque, checkInspect, rigid, inspect, boxedLoop, loop, loop_regular, summarize,
    show (Ty.wrap (.record 0) (.recordLoop 1)).regular = false from box_finite]

private theorem x12_frontier : frontier x12Registry.declarations (request 2 tree) = .selected 7 [] := by
  simp [frontier, request, Request.known, x12Registry, scan, trial, encode, propagate_empty,
    showTree, rigid, inspect, tree, summarize, hits, children]

/-- X6, first part: merged-plain head is a real selected candidate. -/
theorem x6_single_selected : classify x6Single (request 0 tickInt) = .selected (.node 0 []) := by
  unfold classify
  rw [resolve_eq, x6_single_frontier]
  rfl

/-- X6: both actual declarations survive; their identities are ambiguous. -/
theorem x6_ambiguous : classify x6Registry (request 0 tickInt) = .ambiguous := by
  unfold classify
  rw [resolve_eq, x6_frontier]
  rfl

/-- X8: list payload μ is captured opaquely and a finite Len dictionary is built. -/
theorem x8_len_selected : classify x8Registry (request 1 listLoop) = .selected (.node 2 []) := by
  unfold classify
  rw [resolve_eq, x8_frontier]
  rfl

/-- X9 retains the actual where child; it rejects at the anonymous regular root. -/
theorem x9_where_tree : resolve x9Registry (request 2 listLoop) = .selected 3 [.rejected] := by
  rw [resolve_eq, x9_frontier]
  simp only [List.map_cons, List.map_nil]
  rw [resolve_eq, cycle_frontier]

theorem x9_show_rejected : classify x9Registry (request 2 listLoop) = .rejected := by
  unfold classify
  rw [x9_where_tree]
  rfl

/-- X10: propagation leaves a candidate which must inspect μ; K2 rejects it. -/
theorem x10_inspection_rejected : classify x10Registry (request 3 boxedLoop) = .rejected := by
  unfold classify
  rw [resolve_eq, x10_frontier]
  rfl

/-- X11: a safe candidate does not override the inspecting candidate's K2 veto. -/
theorem x11_rejection_before_ambiguity : classify x11Registry (request 3 boxedLoop) = .rejected := by
  unfold classify
  rw [resolve_eq, x11_frontier]
  rfl

/-- X12: matching uses only the nominal identity, never the recursive body. -/
theorem x12_named_selected : classify x12Registry (request 2 tree) = .selected (.node 7 []) := by
  unfold classify
  rw [resolve_eq, x12_frontier]
  rfl

/-- Every conformance result also inhabits the independent outer judgment,
via the SAME unconditional exactness entry. -/
theorem all_six_independent :
    Classify (Local x6Registry.declarations) (request 0 tickInt) .ambiguous ∧
    Classify (Local x8Registry.declarations) (request 1 listLoop) (.selected (.node 2 [])) ∧
    Classify (Local x9Registry.declarations) (request 2 listLoop) .rejected ∧
    Classify (Local x10Registry.declarations) (request 3 boxedLoop) .rejected ∧
    Classify (Local x11Registry.declarations) (request 3 boxedLoop) .rejected ∧
    Classify (Local x12Registry.declarations) (request 2 tree) (.selected (.node 7 [])) :=
  ⟨(resolve_exact ..).mp x6_ambiguous, (resolve_exact ..).mp x8_len_selected,
   (resolve_exact ..).mp x9_show_rejected, (resolve_exact ..).mp x10_inspection_rejected,
   (resolve_exact ..).mp x11_rejection_before_ambiguity, (resolve_exact ..).mp x12_named_selected⟩

/-- The literal repeated-tag source head is lowered to the head actually
used by X6. No pre-merge payload splitting or assignment search is involved. -/
theorem x6_source_lowered :
    CommonRoleSettledGraphBridge.lowerRepeatedTag [(0, 0), (0, 1)] = some mergedTick.head := rfl

theorem upper_only_pending :
    classify x12Registry (Request.waiting 2 tree (State.empty : State 0)) = .pending := by
  unfold classify
  rw [resolve_eq]
  rfl

def duplicateList : Declaration := { showList with requirements := [(2, .var 0), (2, .var 0)] }
def showInt : Declaration := ⟨2, 8, .atom .int, []⟩
def duplicateRegistry : Registry := ⟨[duplicateList, showInt], by
  intro d h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> decide +kernel, by decide +kernel⟩
def listInt : Ty := .wrap (.nominal 0) int

private theorem list_int_finite : listInt.regular = false := by decide +kernel
private theorem duplicate_frontier : frontier duplicateRegistry.declarations (request 2 listInt) =
    .selected 3 [request 2 int, request 2 int] := by
  simp [frontier, request, Request.known, duplicateRegistry, scan, trial, encode, propagate_empty,
    duplicateList, showList, showInt, rigid, inspect, listInt, int, summarize, hits, children, Template.instantiate,
    show (Ty.wrap (.nominal 0) (.atom .int)).regular = false from list_int_finite]
private theorem int_frontier : frontier duplicateRegistry.declarations (request 2 int) = .selected 8 [] := by
  simp [frontier, request, Request.known, duplicateRegistry, scan, trial, encode, propagate_empty,
    duplicateList, showList, showInt, rigid, inspect, int, summarize, hits, children]

theorem all_where_children_retained : classify duplicateRegistry (request 2 listInt) =
    .selected (.node 3 [.node 8 [], .node 8 []]) := by
  have leaf : resolve duplicateRegistry (request 2 int) = .selected 8 [] := by
    rw [resolve_eq, int_frontier]; rfl
  unfold classify
  rw [resolve_eq, duplicate_frontier]
  simp only [List.map_cons, List.map_nil, leaf]
  rfl

def incompatible : Declaration := ⟨3, 10, .wrap (.record 0) (.atom .int), []⟩
def incompatibleRegistry : Registry := ⟨[checkOpaque, incompatible], by
  intro d h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> decide +kernel, by decide +kernel⟩

theorem incompatible_eliminated_before_k2 :
    classify incompatibleRegistry (request 3 boxedLoop) = .selected (.node 5 []) := by
  have front : frontier incompatibleRegistry.declarations (request 3 boxedLoop) = .selected 5 [] := by
    simp [frontier, request, Request.known, incompatibleRegistry, scan, trial, encode, propagate_empty,
      incompatible, checkOpaque, rigid, inspect, boxedLoop, loop, summarize, hits, children,
      show (Ty.wrap (.record 0) (.recordLoop 1)).regular = false from box_finite]
  unfold classify
  rw [resolve_eq, front]
  rfl

def unrolledLoop : Ty := .wrap (.record 1) loop
def boxedUnrolling : Ty := .wrap (.record 0) unrolledLoop
def deepInspect : Declaration := ⟨3, 11, .wrap (.record 0) (.wrap (.record 1) (.atom .int)), []⟩
def unrollingRegistry : Registry := ⟨[checkOpaque, deepInspect], by
  intro d h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> decide +kernel, by decide +kernel⟩
private theorem unrolled_regular : unrolledLoop.regular = true := by decide +kernel
private theorem boxed_unrolled_finite : boxedUnrolling.regular = false := by decide +kernel

/-- Regression for the repaired prepass: neither a folded recursive graph
nor its finite unrolling permits inspecting the recursive payload to eliminate
this candidate. Both go through the same outer resolver and reject. -/
theorem folded_unrolled_k2 :
    classify unrollingRegistry (request 3 boxedLoop) = .rejected ∧
    classify unrollingRegistry (request 3 boxedUnrolling) = .rejected := by
  have folded : frontier unrollingRegistry.declarations (request 3 boxedLoop) = .rejected := by
    simp [frontier, request, Request.known, unrollingRegistry, scan, trial, encode, propagate_empty,
      deepInspect, checkOpaque, rigid, inspect, boxedLoop, loop, loop_regular, summarize,
      show (Ty.wrap (.record 0) (.recordLoop 1)).regular = false from box_finite]
  have unrolled : frontier unrollingRegistry.declarations (request 3 boxedUnrolling) = .rejected := by
    simp [frontier, request, Request.known, unrollingRegistry, scan, trial, encode, propagate_empty,
      deepInspect, checkOpaque, rigid, inspect, boxedUnrolling, unrolledLoop, loop, summarize,
      show (Ty.wrap (.record 1) (.recordLoop 1)).regular = true from unrolled_regular,
      show (Ty.wrap (.record 0) (.wrap (.record 1) (.recordLoop 1))).regular = false from boxed_unrolled_finite]
  constructor
  · unfold classify; rw [resolve_eq, folded]; rfl
  · unfold classify; rw [resolve_eq, unrolled]; rfl

def conflict : State 1 := ⟨clash, clash_grammar.1, clash_grammar.2.1, clash_grammar.2.2⟩

theorem ordinary_conflict_rejected :
    classify x8Registry (Request.known 1 listLoop conflict) = .rejected := by
  have noModel : ¬ conflict.Models := by rintro ⟨assignment, model⟩; exact clash_impossible assignment model
  have eliminated (p : Pattern) (t : Ty) : propagate conflict p t = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact noModel ((propagate_exact conflict p t).mp h).1
  have front : frontier x8Registry.declarations (Request.known 1 listLoop conflict) = .rejected := by
    simp [frontier, Request.known, x8Registry, scan, trial, eliminated, lenList, listLoop,
      summarize, hits, show (Ty.wrap (.nominal 0) loop).regular = false from list_finite]
  unfold classify
  rw [resolve_eq, front]
  rfl

/-- All generated repeated-name checks really remain in the ordinary pass. -/
theorem repeated_self_and_cross_generated :
    CommonRoleCandidateConstraints.generate (slots (n := 0) [0, 0]) =
      [.tyLe (.var 0) (.var 0), .tyLe (.var 0) (.var 0),
       .tyLe (.var 0) (.var 0), .tyLe (.var 0) (.var 0)] := rfl

end Yulang.CommonRoleSettledExamples
