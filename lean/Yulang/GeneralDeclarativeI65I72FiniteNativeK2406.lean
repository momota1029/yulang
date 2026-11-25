import Yulang.GeneralDeclarativeI65I72FiniteNativeTwoRoots406

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Tree Dictionary Result Summarizes)
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeInspect321 (Visit PatternK2)

/-- A completed producer (possibly itself a finite native chain)
really makes this particular child inspectable. Its unfiltered
ordinary cycle is preserved regardless of the typed body's evidence
or a separate lack of support at some other position. -/
structure EnteredFiniteK2406 (s : State) (q : Request) where
  producer : Request
  dictionary : Dictionary
  original : Fin producer.demand.outputs.length → NamedMixedReceipt401 s.core
  before : FiniteNative406 s producer dictionary original
  i : Fin producer.demand.outputs.length
  seen : Declaration
  address : NativeEntryAddress405 s q seen ⟨producer,dictionary,i,original i⟩
  rootSafe : ¬RootCycle s q
  childCycle : CurrentCycleAt s address.site.site

theorem actual_finite_producer_opens_entered_K2_406 {s q} (rejected : EnteredFiniteK2406 s q) :
    (⟨rejected.address.entry.input.lower,
      .nominal rejected.address.entry.key [.variable rejected.address.entry.lowerChild]⟩ : Equation)
      ∈ s.core.current.ordinary.equations ∧
    PatternK2 s.core.current.ordinary rejected.address.entry.lowerChild rejected.address.entry.query := by
  let lit := rejected.address.entry.literal
  exact ⟨chosen_finite_native_output_retains_exact_nominal406 rejected.before rejected.i
    lit.usesOriginalLower lit.declared lit.nominalCode,
    ⟨rejected.address.entry.lowerChild,.here rejected.address.entry.inspecting,rejected.childCycle⟩⟩

private theorem same_rigid_child_not_var406 {s q row need otherNeed r}
    (gate : CompletedUnaryGate406 s q row need)
    (entry : CompletedUnaryEntry404 s q r otherNeed) : False := by
  have authored := entry.visibleRow
  rw [gate.only] at authored
  have rowEq := List.mem_singleton.mp authored
  have exactHead := entry.exactHead
  rw [congrArg Declaration.head rowEq,gate.exactHead] at exactHead
  have owns := (List.cons.inj exactHead).1
  have normal := entry.dispatch
  rw [← owns] at normal
  change Pattern.app gate.key [.var gate.binder] = Pattern.app entry.key [entry.child] at normal
  have literal := (List.cons.inj (Pattern.app.inj normal).2).1
  have translated := entry.exactChild
  rw [← literal] at translated
  change some (Expr.variable gate.binder) = some entry.query at translated
  have inspecting := entry.inspecting
  rw [← Option.some.inj translated] at inspecting
  cases inspecting

private theorem scoped_selected_cannot_ignore_entered_K2406 {s q t d}
    (guard : EnteredFiniteK2406 s q) (source : ScopedSource406 s q t)
    (done : Summarizes t (.selected d)) : False := by
  cases source with
  | completed node => exact same_rigid_child_not_var406 node.chosen.gate guard.address.entry
  | prior original =>
    cases original with
    | rootK2 => cases done
    | other v _ _ _ => cases v <;> cases done
    | selected event raw primitive support kids =>
      obtain ⟨actual,_⟩ := (authored_and_variable_rules_ground_the_same_trace405 raw primitive support).byActualRule
      cases actual with
      | variableCase scan =>
        have headSeen : guard.address.entry.written ∈ guard.seen.head := by
          rw [guard.address.entry.exactHead]
          exact List.mem_cons_self
        obtain ⟨name,written,_⟩ := (variable_scan_is_total405 scan.scan).2.2 guard.seen
          guard.address.entry.visibleRow _ headSeen
        have dispatch := guard.address.entry.dispatch
        rw [written] at dispatch
        cases dispatch
      | nominal priorNative =>
        apply authored_unary_inherits_no_competing_local_diagnostic405
          (verdict := .rejected) (needs := [⟨guard.producer,guard.dictionary,guard.i,guard.original guard.i⟩])
          priorNative.test
        exact .inl (.inr ⟨rfl,⟨⟨_,0,rfl,guard.seen,guard.address.entry,guard.childCycle⟩⟩⟩)

theorem finite_selected_cannot_ignore_entered_K2406 {s q d original}
    (guard : EnteredFiniteK2406 s q) (source : FiniteNative406 s q d original) : False := by
  cases source with
  | base original done _ => exact scoped_selected_cannot_ignore_entered_K2406 guard original done
  | advance original step done => exact same_rigid_child_not_var406 step.head.gate guard.address.entry

/-- The extension retains all prior verdicts. A completed finite
producer can additionally feed the explicit native entry described
above. No clause tests for the absence of a representability proof
or reads a model in order to reject, wait or select. -/
inductive FiniteVerdict406 (s : State) (q : Request) : Result → Prop where
  | prior : ScopedSource406 s q t → Summarizes t result → FiniteVerdict406 s q result
  | selected : FiniteNative406 s q d original → FiniteVerdict406 s q (.selected d)
  | enteredK2 : EnteredFiniteK2406 s q → FiniteVerdict406 s q .rejected

theorem new_finite_entered_K2_has_priority406 {s q} (real : EnteredFiniteK2406 s q) :
    FiniteVerdict406 s q .rejected ∧ ∀ d, ¬ FiniteVerdict406 s q (.selected d) := by
  refine ⟨.enteredK2 real,?_⟩
  intro d chosen
  cases chosen with
  | prior trace complete => exact scoped_selected_cannot_ignore_entered_K2406 real trace complete
  | selected selected => exact finite_selected_cannot_ignore_entered_K2406 real selected

theorem raw_root_K2_has_priority_in_finite_extension406 {s q} (root : RootCycle s q) :
    FiniteVerdict406 s q .rejected ∧ ∀ d, ¬ FiniteVerdict406 s q (.selected d) := by
  obtain ⟨⟨t,⟨trace⟩,verdict⟩,_⟩ := new_trace_preserves_raw_root_k2_406 root
  refine ⟨.prior trace verdict,?_⟩
  intro d chosen
  cases chosen with
  | prior trace complete =>
    rw [raw_k2_forces_new_trace_verdict406 root trace] at complete
    cases complete
  | selected actual => exact raw_K2_still_precedes_finite_native_rule406 root actual

theorem finite_verdict_uses_one_grounded_ledger_for_every_fitting_model406 {s q d}
    (chosen : FiniteVerdict406 s q (.selected d)) :
    ∃ (original : Fin q.demand.outputs.length → NamedMixedReceipt401 s.core) (proof : FiniteNative406 s q d original)
      (ledger : FiniteNativeLedger406 s proof),
      FiniteRootPriorities406 proof ∧ ∀ m, Fits s m → ledger.Means m := by
  cases chosen with
  | prior trace done =>
    obtain ⟨original,⟨actual⟩⟩ := any_actual_scoped_selection_is_a_finite_base406 trace done
    obtain ⟨priority,ledger,meaning⟩ := finite_completed_native_source_assembles_exact_ledger406 actual
    exact ⟨original,actual,ledger,priority,meaning⟩
  | selected trace =>
    obtain ⟨priority,ledger,meaning⟩ := finite_completed_native_source_assembles_exact_ledger406 trace
    exact ⟨_,trace,ledger,priority,meaning⟩

/-- The finite producer can even be a new native proof. A separate
unfinished inner equality is *not* admitted as support but remains
in the raw ordinary graph and can force the entered-child rejection. -/
theorem finite_lower_and_pending_inner_edge_remain_raw_K2_406 {s p q dict original row}
    (producer : FiniteNative406 s p dict original) (i : Fin p.demand.outputs.length)
    (entry : NativeEntryAddress405 s q row ⟨p,dict,i,original i⟩)
    (safe : ¬RootCycle s q)
    {done : Nat → Prop} (authority : GeneralDeclarativeOrigins321.Supported s.core.current.ordinary done)
    (tag owner : Nat)
    (rawEq : authority.derivesFrom
      (⟨entry.site.site,.nominal tag [.variable entry.site.site]⟩ : Equation) (.output owner))
    (pendingOnly : ∀ cause, authority.derivesFrom
      (⟨entry.site.site,.nominal tag [.variable entry.site.site]⟩ : Equation) cause →
        ∃ n, cause = .output n ∧ ¬ done n) :
    (⟨entry.site.site,.nominal tag [.variable entry.site.site]⟩ : Equation)
      ∉ (GeneralDeclarativeOrigins321.restriction authority).equations ∧
    FiniteVerdict406 s q .rejected ∧ ∀ d, ¬FiniteVerdict406 s q (.selected d) := by
  have raw := GeneralDeclarativeK2Alias321.cycle_in_alias_graph
    (GeneralDeclarativeGraphRows321.pending_nominal_self_cycle authority owner rawEq)
  let explored : EnteredFiniteK2406 s q := ⟨p,dict,original,producer,i,row,entry,safe,raw⟩
  exact ⟨GeneralDeclarativeOrigins321.pending_only authority _ pendingOnly,
    new_finite_entered_K2_has_priority406 explored⟩

end Yulang.GeneralDeclarativeI65.I72
