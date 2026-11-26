import Yulang.GeneralDeclarativeI65I74MixedFixedCompanion442

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.MixedFixed442
open GeneralDeclarativeI65
open Checker408 (Problem)
open CommonNominalFullCarrier (Equivalent)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarations (Declaration)

theorem actual_replay_frame_keeps_its_own_head442 {p : Problem} {w : RefPositions441.Wire}
    {r : Replay p} (got : replay442 p w = some r) :
    r.event.frame.input = preoutputInputOfHead399 r.event.head (fun _ => emptyCapture403) := by
  unfold replay442 at got
  split at got
  next d scope =>
    cases first : RefPositions441.replay441 (inputOnly p) d (inputOnly_visible p ▸ scope) w with
    | none => simp [first,Bind.bind,Option.bind] at got
    | some a =>
      simp only [first,Bind.bind,Option.bind] at got
      split at got
      · cases got
      · split at got
        · split at got
          · split at got
            · cases got
            · cases Option.some.inj got
              rfl
          · cases got
        · cases got
  all_goals cases got

/-- Once the same assignment has genuine retained meaning, the actually
checked mixed source event yields the *existing* fixed dictionary evidence.
This is model-level evidence, not a new I72.Classifies or checker branch. -/
theorem actual_mixed_replay_with_retention_is_original_dictionary442
    {p : Problem} {w : RefPositions441.Wire} {r : Replay p}
    (got : replay442 p w = some r) (a : ReplayReadOwnOutput r)
    (m : I72.Model) (fit : I72.Fits p.state m)
    (target : Equivalent (m.assignment p.root.demand.outputs[r.i0].target).1 (a.2.out.actualValue m)) :
    I72.DictionaryEvidence p.state m p.root (.node r.decl.id []) := by
  rw [← r.exactDecl]
  refine .node r.event ?_ ((original_replayed_ref_is_the_fixed_target_slice442 r a.2.out m).mpr target)
    (r.noWhere ▸ .nil)
  have authored : GeneralDeclarations.DeclarationChecked
      (authoredRegistry p.state.core.current).constructors
      (authoredRegistry p.state.core.current).roles r.event.frame.decl :=
    r.exactDecl ▸ r.original.checked
  exact semantic_node_in_signature p.state p.root r.event
    (node_from_exact_preoutput_head405 r.event authored (fun _ => emptyCapture403)
      (actual_replay_frame_keeps_its_own_head442 got)) m fit

theorem actual_mixed_replay_with_existing_typed_companion_is_dictionary442
    {p : Problem} {w : RefPositions441.Wire} {r : Replay p}
    (got : replay442 p w = some r) (a : ReplayReadOwnOutput r) {graph}
    (kept : ExistingMixedCompanion a.2.out graph)
    (m : I72.Model) (fit : I72.Fits p.state m)
    (valid : GeneralNominalState.Models graph m.assignment) :
    I72.DictionaryEvidence p.state m p.root (.node r.decl.id []) :=
  actual_mixed_replay_with_retention_is_original_dictionary442 got a m fit
    ((original_output_fixed_iff_same_target_equals_mixed_value442 a.2.out m).mp
      (existing_companion_has_independent_typed_fixed_equality442 kept m valid))

end Yulang.GeneralDeclarativeI65.I72.MixedFixed442
