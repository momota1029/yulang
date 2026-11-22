import Yulang.GeneralDeclarativeWitnessRangeRelease355
import Yulang.GeneralDeclarativeWitnessCovariantHead352
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessRangeCut355
open GeneralDeclarationPatterns (Pattern coveredArgs normalizeArgs normalize variablesArgs)
open GeneralDeclarativeWitnessCovariantDescent353 (descent legal exactShape)
open GeneralDeclarativeWitnessChecks349 (names scope_sound counts lexical output_only)
open GeneralDeclarativeWitnessProblem349 (splitOr splitAnd)
open GeneralDeclarativeWitnessCovariantHead352 (rawPattern)
open GeneralDeclarativeWitnessTypedRangeWriter354 (Run)
open GeneralDeclarativeWitnessCovariantCompiler353 (Prepared captures)
open GeneralDeclarativeWitnessCompiler350 (Context initial portNames placed)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOpaqueShared328 (build)
open GeneralDeclarativeOpaqueGroup328 (group group_exact)
open GeneralDeclarations (Declaration Clause)

theorem residual_joins_only_allow_bare_here {hs cs : List Pattern}
    (notCovered : coveredArgs (normalizeArgs hs) = false)
    (h : descent hs cs = true) : ∃ n, cs = [.var n] := by
  rcases splitOr h with main|extra
  · have countsOK := (splitAnd (splitAnd main).1).1
    unfold counts at countsOK
    simp [notCovered] at countsOK
  · have test := (splitAnd extra).2
    split at test
    · rename_i t b l u c r n
      exact ⟨n,rfl⟩
    · cases test

theorem c354_head_is_residual : coveredArgs (normalizeArgs [rawPattern]) = false := by decide +kernel

theorem accepted_clause_is_bare {s : GeneralSourceMetadataBundle291.SourceBundle} {d : Declaration}
    (ok : legal s d = true) (head : d.head = [rawPattern]) {c : Clause} (in_ : c ∈ d.requirements) :
    ∃ n, c.arguments = [.var n] := by
  have every := (splitAnd (splitAnd (splitAnd ok).2).2).2
  have passes := List.all_eq_true.mp every c in_
  rw [head] at passes
  exact residual_joins_only_allow_bare_here c354_head_is_residual passes

theorem bare_scope {s : GeneralSourceMetadataBundle291.SourceBundle} {d : Declaration}
    (ok : legal s d = true) {c : Clause} (member : c ∈ d.requirements) {n : Nat}
    (args : c.arguments = [.var n]) : n ∈ d.inputNames ∧ n ∉ d.outputNames := by
  have checks := (splitAnd (splitAnd ok).2)
  have allowed := scope_sound (splitAnd checks.2).1
  have out := output_only (splitAnd checks.1).2
  have isInput : n ∈ d.inputNames :=
    allowed.1 c member n (by simp [args,normalizeArgs,variablesArgs,normalize,Pattern.variables])
  exact ⟨isInput,fun clash => out.1 n clash (GeneralPatternVariableProvenance.normalize_args_variables d.head isInput)⟩

theorem actual_capture_no_renaming (keys : List Nat) {seen : List (Nat × Capture)} {n v : Nat}
    (witness : ∃ u, (n,u) ∈ seen) (every : ∀ u, (n,u) ∈ seen → u.center = v)
    (keep : List Nat) (fallback : Nat → Capture) (st : State) (found : n ∈ keys) :
    ((build keep seen fallback st keys).captures n).center = v := by
  induction keys generalizing st with
  | nil => cases found
  | cons key tail ih =>
    cases got : group key seen with
    | nil =>
      by_cases same : n = key
      · subst key
        obtain ⟨u,m⟩ := witness
        have mem := (group_exact n seen).2 m
        rw [got] at mem
        cases mem
      · have rest := (List.mem_cons.mp found).resolve_left same
        simpa [build,got] using ih st rest
    | cons u more =>
      by_cases same : n = key
      · subst key
        have mem : (n,u) ∈ seen := (group_exact n seen).mp (got ▸ List.mem_cons_self)
        simpa [build,got,GeneralDeclarativeAggregate324.span] using every u mem
      · have rest := (List.mem_cons.mp found).resolve_left same
        simpa [build,got,same] using ih (GeneralDeclarativeAggregate324.ready st keep u more) rest

theorem selected_center {p w} (r : Run p w) {n : Nat} (in_ : n ∈ r.readFrom.center.decl.inputNames)
    (notOutput : n ∉ r.readFrom.center.decl.outputNames) :
    ((portNames r.readFrom.ctx r.ports).input n).center = r.readFrom.center.anchor.current.valueName := by
  have found : n ∈ r.readFrom.center.names := r.readFrom.center.binds.symm ▸ in_
  have key : n ∈ (captures r.readFrom.center.anchor r.readFrom.center.names).map Prod.fst :=
    List.mem_map.mpr ⟨(n,GeneralDeclarativeWitnessCovariantCompiler353.selectedSlot r.readFrom.center.anchor),
      List.mem_map_of_mem found,rfl⟩
  have witness : ∃ u, (n,u) ∈ captures r.readFrom.center.anchor r.readFrom.center.names :=
    ⟨_,List.mem_map_of_mem found⟩
  have whole : ∀ u, (n,u) ∈ captures r.readFrom.center.anchor r.readFrom.center.names →
      u.center = r.readFrom.center.anchor.current.valueName := by
    intro u present
    obtain ⟨j,_,eq⟩ := List.mem_map.mp present
    exact (congrArg (Capture.center ∘ Prod.snd) eq).symm
  have raw := actual_capture_no_renaming _ witness whole p.keep p.fallback
    (GeneralDeclarativeStableAssemble329.tieState p.stage
      (captures r.readFrom.center.anchor r.readFrom.center.names) p.fallback) key
  unfold portNames GeneralDeclarativeFrameReadback325.sourceNames GeneralDeclarativeProducedNames325.table
  change (if n ∈ r.readFrom.center.decl.outputNames then _ else
    ((initial r.readFrom.ctx).captures n)).center = _
  split
  · rename_i contradictory
    exact False.elim (notOutput contradictory)
  · change ((build p.keep (captures r.readFrom.center.anchor r.readFrom.center.names) p.fallback
      (GeneralDeclarativeStableAssemble329.tieState p.stage
        (captures r.readFrom.center.anchor r.readFrom.center.names) p.fallback)
      ((captures r.readFrom.center.anchor r.readFrom.center.names).map Prod.fst)).captures n).center = _
    exact raw

theorem actual_grandchild_center {p w} (r : Run p w)
    (head : r.readFrom.center.decl.head = [rawPattern])
    {d : Demand} (child : d ∈ r.children) :
    ∃ a, d.arguments = [a] ∧ a.center = r.readFrom.center.anchor.current.valueName := by
  obtain ⟨c,in_,exact⟩ := List.mem_map.mp child
  obtain ⟨n,shape⟩ := accepted_clause_is_bare r.readFrom.center.good head in_
  have names := bare_scope r.readFrom.center.good in_ shape
  refine ⟨(portNames r.readFrom.ctx r.ports).input n,?_,selected_center r names.1 names.2⟩
  rw [← exact]
  simp [GeneralDeclarativeSourceEmission322.demand, GeneralDeclarativeSourceEmission322.inputs,
    GeneralDeclarativeSourceEmission322.useArg,shape,normalize]

theorem no_grandchild_at_a_different_fixed_target {p w} (r : Run p w)
    (head : r.readFrom.center.decl.head = [rawPattern]) {d : Demand}
    (child : d ∈ r.children) {a : Capture} (arg : a ∈ d.arguments) :
    a.center = r.readFrom.center.anchor.current.valueName := by
  obtain ⟨actual,one,center⟩ := actual_grandchild_center r head child
  rw [one] at arg
  exact (congrArg Capture.center (List.mem_singleton.mp arg)).trans center

end Yulang.GeneralDeclarativeWitnessRangeCut355
