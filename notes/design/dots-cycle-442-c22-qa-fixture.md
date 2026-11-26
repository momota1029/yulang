# C442 補助検証の再現

これは公開 production/Audit を変更するためのコードではない。正本元 `fbbf227b2023e0da5d18d8f5c3826545f6b79e28`、技術 pin `ca663ec06b47c9acdbfce2ad4e449e4284956551` と照合する実装周辺の対照。

1. `lean/Audit/Cycle442I74MixedFixedEndToEnd.lean` (blob `0b73359dbb2211b189aee2c373d376502d4c7447`) の複製を空の作業ディレクトリに置く。元の Git ファイルは変更しない。
2. 先頭 import `Yulang.GeneralDeclarativeI65I74MixedFixedRead442` を `Yulang.GeneralDeclarativeI65I74MixedFixedDictionary442` に替え、その次の行に `import Yulang.GeneralDeclarativeI65I74MixedFixedBoundary442` を足す。最後の `end Yulang.GeneralDeclarativeI65.I72.MixedFixed442.Example` の直前に下のコードを足す。正確な検証コピーの `git hash-object` は `e977e0eed24a4c2fe6664911fe47517492e1ccce`。
3. 正本の旧依存とこの pin の新 production だけを `LEAN_PATH` に取る。独立 Audit の olean を一切含めない。official Lean 4.35.0 `lean --trust=0 -DwarningAsError=true <copy>` を一つだけ実行。exit 0。標準のみの #print が 20 行（公開 Audit と繰り返す 6、追加 14）。不要な全体ビルドはしない。

| 対照 | 元 typed source replay | original `Fits` | older descriptor / fixed equality |
| --- | --- | --- | --- |
| 捕捉 row signed、fixed target 21 も同じ signed | 同一 Event と typed wire | true | exact companion Models および実 node 81 の既存 dictionary evidence |
| 元 row signed のまま target 21 の内側 row だけ empty | 同一 Event と typed wire | true、native/view も同一 | false |
| source row だけ変える（全 .1 は同じ） | 各 model の typed RHS が異なる | 両方 true | 単一の旧 Expr はどちらかで原 RHS に非同値 |
| 固定要求先だけ 21 → 22 に変更 | true、address 22 を保つ | ここでは判定しない | 21 に記録されたその exact descriptor とは照合不可 |
| body ID、binder swap、issuer または associated name の相違 | false/none | 判定しない | 不正な補いはしない |
| 旧 public R21 `.reference` に exact nonempty report | scope 外で false | 任意 | 言語の拒否ではない |

```lean
open GeneralNominalState (Descriptor)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)

theorem operational_typed_read_preserves_own_exact_nonflattened_wire442 :
    replayed.readOwnRefOutput.isSome = true := by decide +kernel

def own := replayed.readOwnRefOutput.get operational_typed_read_preserves_own_exact_nonflattened_wire442

theorem exact_single_written_wire_is_not_flattened442 :
    Check408.encodedEventWrites replayed.event =
      [⟨[71,3],0,0,⟨76,21⟩,.explicit out,
        .node 4 [9] [.node 11 [1,0,6,1,1,1] [],.node 10 [0,2,8,2,2,2] []]⟩] := rfl

theorem wrong_authored_body_and_wrong_issuer_do_not_replay442 :
    (replayedOriginalRef442 9 6 8 101 (by decide) named).isNone = true ∧
    (replayedOriginalRef442 9 8 6 100 (by decide) named).isNone = true ∧
    (replay442 {problem with root := {problem.root with occurrence := [71,4]}} wire).isNone = true := by
  decide +kernel

theorem two_actual_fits_exclude_any_old_single_rhs442 :
    ¬∃ rhs : GeneralNominalCenteredHeadMatExpressions.Expr, ∀ m, Fits problem.state m →
      Equivalent
        (GeneralNominalCenteredHeadMatExpressions.value (GeneralDeclarativeHead320.environment m.assignment) .actual rhs)
        (own.2.out.actualValue m) := by
  apply independently_varying_original_effect_excludes_any_old_denotation442
    own.2.out (model effect effect) (model Common.rowEmpty effect)
    (every_input_and_target_row_fits442 _ _) (every_input_and_target_row_fits442 _ _) (fun _ => rfl)
  intro eq
  change effect = Common.rowEmpty at eq
  have seen : effect (56,[1,-2]) := rfl
  rw [eq] at seen
  exact seen

abbrev companionBase : GeneralSourceState.State where
  slots := 2
  source := fun i => if i.val = 0 then 21 else 2
  source_injective := by
    intro a b eq
    apply Fin.ext
    change (if a.val = 0 then 21 else 2) = (if b.val = 0 then 21 else 2) at eq
    split at eq <;> split at eq <;> omega
  rowSource := fun i => if i.val = 0 then 31 else 1
  ordinary := []
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun _ => .unresolved
  intervals := []
  heads_sound := by intro _ _ _ _ impossible; cases impossible
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev companionViews : GeneralNormalizedObservation.Snapshot companionBase where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun _ => .deferred .unresolved
  checked := by intro _ _ impossible; cases impossible

def companionDescriptor : Descriptor 2 :=
  ⟨9,⟨[.row,.type],9⟩,[.row (1,1),.type (1,1)],rfl⟩

def companionGraph : GeneralNominalState.State where
  base := companionBase
  view := companionViews
  constructors := (authoredRegistry problem.state.core.current).constructors
  nominals := fun i => if i.val = 0 then some companionDescriptor else none
  catalogue := by
    intro i d h
    split at h
    · have named := Option.some.inj h
      subst d
      rfl
    · cases h
  bodies_opaque := by intro _ _ _; rfl

abbrev targetPosition : Fin companionGraph.base.slots := ⟨0,by decide +kernel⟩
abbrev payloadPosition : Fin companionGraph.base.slots := ⟨1,by decide +kernel⟩

def exactCompanion : ExistingMixedCompanion own.2.out companionGraph :=
  ⟨targetPosition,payloadPosition,payloadPosition,companionDescriptor,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem actual_companion_graph_retains_exact_mixed_target442 (m : I72.Model) :
    GeneralNominalState.Models companionGraph m.assignment ↔ FixedTargets m replayed.event := by
  have origin := original_replayed_ref_is_the_fixed_target_slice442 replayed own.2.out m
  have actual := existing_mixed_descriptor_point_exact442 companionBase m.assignment 0 1 1 companionDescriptor rfl
  constructor
  · intro fit
    apply origin.mpr
    exact actual.mp (fit.2.1 targetPosition companionDescriptor rfl)
  · intro fit
    have want := origin.mp fit
    refine ⟨⟨PresenceNormalForm.all_nil _ _,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
    · intro _ _ impossible; cases impossible
    · intro _ member; cases member
    · intro i descriptor recorded
      change (if i.val = 0 then some companionDescriptor else none) = some descriptor at recorded
      split at recorded
      · rename_i eq
        have h : i = targetPosition := Fin.ext eq
        subst i
        have same := (Option.some.inj recorded).symm
        subst descriptor
        exact actual.mpr want
      · cases recorded

theorem real_original_bad_model_cannot_be_relabelled_companion442 :
    Fits problem.state (model effect Common.rowEmpty) ∧
    ¬GeneralNominalState.Models companionGraph (model effect Common.rowEmpty).assignment :=
  ⟨every_input_and_target_row_fits442 _ _,fun falseFit =>
    original_fixed_targets_can_fail_after_real_source_replay442.2.2.2
      ((actual_companion_graph_retains_exact_mixed_target442 _).mp falseFit)⟩

theorem real_original_good_model_and_companion_share_assignment442 :
    Fits problem.state (model effect effect) ∧
    GeneralNominalState.Models companionGraph (model effect effect).assignment :=
  ⟨every_input_and_target_row_fits442 _ _,(actual_companion_graph_retains_exact_mixed_target442 _).mpr
    original_fixed_targets_can_fail_after_real_source_replay442.2.2.1⟩

#print axioms operational_typed_read_preserves_own_exact_nonflattened_wire442
#print axioms exact_single_written_wire_is_not_flattened442
#print axioms wrong_authored_body_and_wrong_issuer_do_not_replay442
#print axioms two_actual_fits_exclude_any_old_single_rhs442
#print axioms actual_companion_graph_retains_exact_mixed_target442
#print axioms real_original_bad_model_cannot_be_relabelled_companion442
#print axioms real_original_good_model_and_companion_share_assignment442
def same_source_new_target : Problem :=
  {problem with root := {problem.root with demand := {problem.root.demand with outputs := [⟨76,22⟩]}}}

theorem source_read_retains_new_requested_target_without_claiming_retention442 :
    (replay442 same_source_new_target wire).isSome = true := by decide +kernel

def retargeted := (replay442 same_source_new_target wire).get
  source_read_retains_new_requested_target_without_claiming_retention442

theorem typed_retargeted_read442 : retargeted.readOwnRefOutput.isSome = true := by decide +kernel

def newTargetOutput := retargeted.readOwnRefOutput.get typed_retargeted_read442

theorem same_source_replay_has_new_exact_address442 (m : I72.Model) :
    newTargetOutput.2.out.named.receipt.actualEquation m =
      some (22,nominal 9 [.inr (m.assignment 1).2,.inl (m.assignment 2).1]) :=
  rfl

theorem cannot_retarget_existing_companion_by_replaying_equal_rhs442 :
    ¬Nonempty (ExistingMixedCompanion newTargetOutput.2.out companionGraph) := by
  rintro ⟨held⟩
  have taken := held.actual
  change (if held.root.val = 0 then some companionDescriptor else none) = some held.descriptor at taken
  by_cases h : held.root.val = 0
  · have target := held.target
    change (if held.root.val = 0 then 21 else 2) = 22 at target
    simp [h] at target
  · simp [h] at taken

#print axioms source_read_retains_new_requested_target_without_claiming_retention442
#print axioms typed_retargeted_read442
#print axioms same_source_replay_has_new_exact_address442
#print axioms cannot_retarget_existing_companion_by_replaying_equal_rhs442
theorem actual_original_good_fit_has_fixed_dictionary442 :
    DictionaryEvidence problem.state (model effect effect) problem.root (.node 81 []) := by
  have got : replay442 problem wire = some replayed := rfl
  exact actual_mixed_replay_with_existing_typed_companion_is_dictionary442 got own exactCompanion
    (model effect effect) real_original_good_model_and_companion_share_assignment442.1
    real_original_good_model_and_companion_share_assignment442.2

def exactOriginalReport : Check408.Result :=
  ⟨.selected 81 [],.selected (.node 81 []),Check408.encodedEventWrites replayed.event⟩

theorem previous_public_ref_lane_does_not_claim_nonempty_ref_write442 :
    RefPositions441.check problem exactOriginalReport (.reference wire) = false := by
  decide +kernel

theorem wrong_associated_name_does_not_read_output442 :
    (replay442 {problem with root := {problem.root with demand :=
      {problem.root.demand with outputs := [⟨77,21⟩]}}} wire).isNone = true := by
  decide +kernel

#print axioms actual_original_good_fit_has_fixed_dictionary442
#print axioms previous_public_ref_lane_does_not_claim_nonempty_ref_write442
#print axioms wrong_associated_name_does_not_read_output442
```
