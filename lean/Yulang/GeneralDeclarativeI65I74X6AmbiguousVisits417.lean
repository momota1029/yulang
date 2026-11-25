import Yulang.GeneralDeclarativeI65I74X6AmbiguousEvents417

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417
open GeneralDeclarativeI65
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeK2Graph321 (View arguments)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeInspect321 (Visit PatternK2)
open GeneralDeclarativeGraphRows321 (observed structural shapeOf literal_head)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410
  exact_escape_preserves_alias_side410)
open PlainMerged416 (PlainRows mergedCode)

def groundVariantAtRoot (gate : ExactEscapeWire) (root tag payload : Nat) (row : Equation) : Bool :=
  match shapeOf row.right with
  | some (.variant label child) =>
    decide (gate.side row.left = gate.side root ∧ label = tag → child = payload)
  | _ => true

theorem variant_profile_tracks_reached_child417 {s q} (rows : PlainRows s q)
    {gate : ExactEscapeWire} (escape : checkExactEscape s.core.current.ordinary rows.root gate = true)
    (profile : s.core.current.ordinary.equations.all
      (groundVariantAtRoot gate rows.root rows.tag rows.payload) = true)
    {n} (look : structural s.core.current.ordinary rows.root (.variant rows.tag n)) :
    n = rows.payload := by
  obtain ⟨source,alias,expr,present,shape⟩ := look
  have side := (exact_escape_preserves_alias_side410 escape alias).symm
  have checked := List.all_eq_true.mp profile _ present
  exact (of_decide_eq_true (by
    simpa [groundVariantAtRoot,shape] using checked :
      decide (gate.side source = gate.side rows.root ∧ rows.tag = rows.tag → n = rows.payload) = true))
    ⟨side,rfl⟩

theorem scalar_int_has_no_descendant417 {v : View} {first site : Nat}
    (seen : Visit v first (.primitive (.scalar .int) []) site) : site = first := by
  cases seen with
  | here => rfl
  | primitive _ off _ _ => simp at off

structure Visits {s q} (rows : PlainRows s q) : Prop where
  exactPort : ∀ n, structural s.core.current.ordinary rows.root (.variant rows.tag n) →
    n = rows.payload
  rootSafe : ¬ AliasCycle s.core.current.ordinary (observed s.core.current.ordinary) rows.root
  payloadSafe : ¬ AliasCycle s.core.current.ordinary (observed s.core.current.ordinary) rows.payload

theorem root_safe417 {s q} {rows : PlainRows s q} (v : Visits rows) : ¬ RootCycle s q := by
  rintro ⟨name,found,cycle⟩
  rw [rows.requested] at found
  cases List.mem_singleton.mp found
  exact v.rootSafe cycle

theorem plain_root_only417 {s q} {rows : PlainRows s q} {a b : Nat} (v : Visits rows) :
    ¬ PatternK2 s.core.current.ordinary rows.root (mergedCode rows.tag a b) :=
  PlainMerged416.normalization_has_only_the_actual_variant_visit416 rows v.rootSafe

theorem ground_visits_exactly_root_or_payload417 {s q} {rows : PlainRows s q}
    (v : Visits rows) {site}
    (visit : Visit (structural s.core.current.ordinary) rows.root (groundCode rows.tag) site) :
    site = rows.root ∨ site = rows.payload := by
  change Visit (structural _) rows.root (.variant rows.tag (.primitive (.scalar .int) [])) site at visit
  cases visit with
  | here => exact .inl rfl
  | variant structureInside child =>
    exact .inr ((scalar_int_has_no_descendant417 child).trans (v.exactPort _ structureInside))

theorem ground_actually_inspects_both_original_roots417 {s q} (rows : PlainRows s q) :
    Visit (structural s.core.current.ordinary) rows.root (groundCode rows.tag) rows.root ∧
    Visit (structural s.core.current.ordinary) rows.root (groundCode rows.tag) rows.payload := by
  exact ⟨.here .variant,.variant (literal_head rows.rootRow rfl) (.here .primitive)⟩

theorem ground_can_only_report_ambiguity_after_both_K2_checks417 {s q} {rows : PlainRows s q}
    (v : Visits rows) : ¬ PatternK2 s.core.current.ordinary rows.root (groundCode rows.tag) := by
  rintro ⟨site,visit,cycle⟩
  rcases ground_visits_exactly_root_or_payload417 v visit with rfl|rfl
  · exact v.rootSafe cycle
  · exact v.payloadSafe cycle

theorem a_cycle_at_the_real_payload_is_ground_K2_even_without_root_K2417 {s q} (r : PlainRows s q)
    (cycle : AliasCycle s.core.current.ordinary (observed s.core.current.ordinary) r.payload) :
    PatternK2 s.core.current.ordinary r.root (groundCode r.tag) :=
  ⟨r.payload,(ground_actually_inspects_both_original_roots417 r).2,cycle⟩

end Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417
