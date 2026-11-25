import Yulang.GeneralDeclarativeI65I74WhereListPriority411

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereCycle411
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern)
open CommonRoleOutermostResolver (Summarizes)
open Checker408 (Problem Result)
open GeneralDeclarativeWitnessDeclaredState357 (point)

/-- This requires a nonempty literal where, unlike the preceding C410
list leaf. Nor can older ordinary, nullary-argument nominal, or
covariant-native local source cases express this actual event. -/
theorem where_rule_is_a_new_local_family411 {s q} {e : Event s q}
    (source : WhereListRead e) {needs} : ¬List410.R2.elected s q e needs := by
  rintro (old|leaf)
  · rcases old with legacy|named
    · rcases R0_selection_uses_independent_original_rule407 e legacy with general|native
      · have inScope : e.frame.decl ∈ visible s.core q := by simp [source.test.only]
        have atHead : Pattern.app source.test.key [.var source.test.binder] ∈ e.frame.decl.head := by
          simp [source.test.named]
        obtain ⟨_,absurd,_⟩ := general.2 _ inScope _ atHead
        cases absurd
      · obtain ⟨native⟩ := native
        have h := (List.cons.inj (native.test.writtenHead.symm.trans source.test.named)).1
        change Pattern.app native.test.key [.var native.test.binder] =
          Pattern.app source.test.key [.var source.test.binder] at h
        have key := (Pattern.app.inj h).1
        have mode := native.test.table
        rw [key,source.test.table] at mode
        cases mode
    · obtain ⟨_,⟨bare⟩⟩ := named
      have h := (List.cons.inj (bare.test.named.symm.trans source.test.named)).1
      have lengths := congrArg List.length (Pattern.app.inj h).2
      cases lengths
  · obtain ⟨_,⟨leaf⟩⟩ := leaf
    have h := source.test.exactWhere.symm.trans leaf.test.noWhere
    cases h

/-- Once the actual child is on a raw cycle, no local source rule can
replace that child's diagnostic, even if it is added in a future stage. -/
theorem raw_cycle_forces_the_exact_child_trace411 {R s q t e} (cycle : RootCycle s q)
    (trace : SourceTrace R s q t e) : t = .rejected ∧ e = none := by
  cases trace with
  | rootK2 => exact ⟨rfl,rfl⟩
  | other _ safe _ _ => exact (safe cycle).elim
  | selected _ safe _ _ _ => exact (safe cycle).elim

/-- Fix one actual parent event, its ordered raw child and one source
tree before quantifying over models. Inspecting a model cannot change
the chosen declaration, lexical name, role, child occurrence, or writes. -/
theorem checked_where_child_keeps_same_trace_for_all_models411
    (p : Problem) (r : Result) (w : CycleWire) (yes : check p r (.whereChild w) = true) :
    ∃ (d : Declaration) (source : VerifiedWhereList p d)
      (e : Event p.state p.root) (t : SourceTrace R3 p.state p.root r.tree (some e)),
      e.frame.decl = d ∧ e.kids = [source.known.child] ∧
      source.known.child.occurrence = p.root.occurrence ++ [0] ∧
      e.frame.input source.known.binder = point source.known.payload ∧
      ¬RootCycle p.state p.root ∧ RootCycle p.state source.known.child ∧
      Summarizes r.tree r.verdict ∧ r.writes = writes t ∧
      ∀ m, Fits p.state m → TraceMeaning p.state m t := by
  obtain ⟨d,_,source,_,cycle,report⟩ := accepted_where_wire_reflects_actual_child411 p r w yes
  subst r
  obtain ⟨e,rule,decl,kids,capture,ew⟩ := selected_where_is_exact_actual_child411 source
  let one : WhereForest R3 p.state [source.known.child] [.rejected] :=
    .cons (.rootK2 cycle) .nil
  let forest : WhereForest R3 p.state e.kids [.rejected] := kids.symm ▸ one
  let tree : SourceTrace R3 p.state p.root (.selected e.frame.decl.id [.rejected]) (some e) :=
    .selected e source.rawSafe rule .nil forest
  have sum : Summarizes (.selected e.frame.decl.id [.rejected]) .rejected :=
    .selected (.cons .rejected .nil) (.rejected List.mem_cons_self)
  have forestZero : ∀ qs (h : qs = [source.known.child]), forestWrites (h.symm ▸ one) = [] := by
    intro qs h
    cases h
    rfl
  have zero : writes tree = [] := by
    change Check408.encodedEventWrites e ++ forestWrites forest = []
    rw [ew,forestZero e.kids kids]
    rfl
  have exactTree : (.selected e.frame.decl.id [.rejected] : CommonRoleOutermostResolver.Tree) =
      (expected411 d).tree := by simp [decl,expected411]
  refine ⟨d,source,e,exactTree ▸ tree,decl,kids,rfl,capture,source.rawSafe,cycle,
    exactTree ▸ sum,?_,?_⟩
  · change [] = writes (exactTree ▸ tree)
    generalize (expected411 d).tree = target at exactTree ⊢
    cases exactTree
    exact zero.symm
  · intro m fit
    exact mixed_R3_trace_model_meaning411 _ m fit

end Yulang.GeneralDeclarativeI65.I72.WhereCycle411
