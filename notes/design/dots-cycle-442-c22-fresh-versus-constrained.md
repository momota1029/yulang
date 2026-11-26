# C442 — fresh と既に制約された fixed target を区別する

この追試は canonical R22 でも保存の権限でもない。次サイクルの保持ライター設計を、上の一つの actual source fixture 上で比較した。

- **fresh 21**: 古い原 `Fits` のどのモデルでも、21 の `.1` だけを正しい mixed ref value にしたモデルを構成できる（`every_actual_preoutput_fit_extends_to_real_typed_store442`）。他の全 slot、全 `.2` と authoredViews/nativeSyntax を保ち、同じ元 State を満たす。RHS は 21 の .1 を読まない。companion の実 descriptor の Models と元 Event の既存辞書を得るが、**元のモデルをそのまま全て**満たすという主張ではない。
- **既存の語彙で制約した 21**: その固定先に先に Int の ordinary equation がある actual 適合モデルを構成、元と同じ authored mixed source replay は動く。しかしどの適合モデルも同じ Event の mixed `FixedTargets` を満たせない（`no_actual_fit_can_retain_loaded_scalar_as_mixed_rhs442`）。初めから適合モデルなしという反例ではない。21 の代入を黙って上書きすると、今ある Int の等式に違反する（`cannot_rewrite_a_preconstrained_scalar_output442`）。仕様上の書き込みは旧制約と**連言**で、既存値の置換や勝手な拒否 rule の追加ではない。

## 再現

[dots-cycle-442-c22-qa-fixture.md](dots-cycle-442-c22-qa-fixture.md) の 20 行の検証コピーを用意し、その同じ最後の namespace `end` の直前に以下を加える。exact Git-byte hash `abcfcd3882db3bcd06ac0ecac297777df885f963`。公式 Lean 4.35.0 `--trust=0 -DwarningAsError=true`、production-only import、独立した physical source で exit 0。標準のみ 31 行（先の追試と重複 20、追加 11）。公開 Lean/Audit ファイルの 39 行には加算しない。全体ビルド・Rust は行っていない。

```lean
/-- Narrow model repair for this particular pre-output snapshot. It preserves
every old ordinary/type or row dependency; other original States may already
constrain 21 and need not admit this repair. -/
def writeFreshTarget (m : I72.Model) : I72.Model :=
  { m with assignment := fun n => if n = 21 then
      (nominal 9 [.inr (m.assignment 1).2,.inl (m.assignment 2).1],(m.assignment n).2)
    else m.assignment n }

theorem exact_output_does_not_read_its_fixed_target442 (m : I72.Model) :
    named.receipt.actualEquation (writeFreshTarget m) = named.receipt.actualEquation m :=
  rfl

theorem fixed_target_repair_preserves_all_other_names_and_channels442 (m : I72.Model) :
    (∀ n, n ≠ 21 → (writeFreshTarget m).assignment n = m.assignment n) ∧
    (∀ n, ((writeFreshTarget m).assignment n).2 = (m.assignment n).2) ∧
    (writeFreshTarget m).authoredValues = m.authoredValues ∧
    (writeFreshTarget m).nativeSyntax = m.nativeSyntax := by
  refine ⟨fun n h => by simp [writeFreshTarget,h],?_,rfl,rfl⟩
  intro n
  by_cases h : n = 21 <;> simp [writeFreshTarget,h]

theorem fixed_target_repair_keeps_original_fits442 (m : I72.Model) (fit : Fits problem.state m) :
    Fits problem.state (writeFreshTarget m) := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro atom member
    change atom ∈ [rowOne,valueTwo] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact Common.rowLe_refl _
    · exact subtype_refl _
  · intro eq impossible
    cases impossible
  · intro eq present
    change eq ∈ [intRow] at present
    cases List.mem_singleton.mp present
    have prior := fit.1.1.2 intRow (by
      change intRow ∈ [intRow]
      exact List.mem_cons_self)
    change Equivalent (m.assignment 2).1 (.base .int) at prior
    exact prior
  · intro view present
    change view ∈ [originalView] at present
    cases List.mem_singleton.mp present
    have prior := fit.1.2 originalView (by
      change originalView ∈ [originalView]
      exact List.mem_cons_self)
    exact prior
  · intro ori present
    exact fit.2 ori present

theorem repairing_actual_target_establishes_exact_retention442 (m : I72.Model) :
    FixedTargets (writeFreshTarget m) replayed.event := by
  apply (original_replayed_ref_is_the_fixed_target_slice442 replayed own.2.out _).mpr
  exact eqv_refl _

theorem every_actual_preoutput_fit_extends_to_real_typed_store442 (m : I72.Model)
    (fit : Fits problem.state m) :
    Fits problem.state (writeFreshTarget m) ∧
      GeneralNominalState.Models companionGraph (writeFreshTarget m).assignment ∧
      DictionaryEvidence problem.state (writeFreshTarget m) problem.root (.node 81 []) := by
  have good := fixed_target_repair_keeps_original_fits442 m fit
  have held := (actual_companion_graph_retains_exact_mixed_target442 _).mpr
    (repairing_actual_target_establishes_exact_retention442 m)
  have got : replay442 problem wire = some replayed := rfl
  exact ⟨good,held,actual_mixed_replay_with_existing_typed_companion_is_dictionary442
    got own exactCompanion _ good held⟩

#print axioms exact_output_does_not_read_its_fixed_target442
#print axioms fixed_target_repair_preserves_all_other_names_and_channels442
#print axioms fixed_target_repair_keeps_original_fits442
#print axioms repairing_actual_target_establishes_exact_retention442
#print axioms every_actual_preoutput_fit_extends_to_real_typed_store442
theorem two_kinds_ref_cannot_satisfy_scalar_target442 (r : Common.Row) (t : Ty) :
    ¬CommonNominalFullCarrier.Subtype (nominal 9 [.inr r,.inl t]) (.base .int) := by
  intro h
  let env : CommonNominalFullDemand.Environment Common.Row :=
    ⟨fun _ => .top,fun _ => []⟩
  have test := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (h 0)
    0 env (.base .int) (show CommonNominalFullDemand.ProbeAt Common.rowLe 0 env
      (.base .int) (.base .int) from rfl)
  change False at test
  exact test

def fixedScalarAtOwnTarget : Equation := ⟨21,.primitive (.scalar .int) []⟩

def constrainedCore : GeneralDeclarativeI65.State :=
  {core with current := {core.current with ordinary := {core.current.ordinary with
    equations := [intRow,fixedScalarAtOwnTarget]}}}

def scalarOldTarget : I72.Model :=
  {model effect effect with assignment := fun n =>
    (.base .int,(model effect effect).assignment n |>.2)}

theorem old_target_constraint_has_a_model442 : GeneralDeclarativeI65.Fits constrainedCore scalarOldTarget := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro atom member
    change atom ∈ [rowOne,valueTwo] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact Common.rowLe_refl _
    · exact subtype_refl _
  · intro e impossible; cases impossible
  · intro e member
    change e ∈ [intRow,fixedScalarAtOwnTarget] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> exact eqv_refl _
  · intro view member
    change view ∈ [originalView] at member
    cases List.mem_singleton.mp member
    exact ⟨⟨4,9,[.inr effect,.inl (.base .int)]⟩,rfl,rfl,rfl,rfl⟩
  · intro ori member
    change ori ∈ [inputOrigin,outputObservation] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> rfl

theorem cannot_rewrite_a_preconstrained_scalar_output442 (m : I72.Model) :
    ¬GeneralDeclarativeI65.Fits constrainedCore (writeFreshTarget m) := by
  intro fit
  have conflict := fit.1.1.2 fixedScalarAtOwnTarget (by
    change fixedScalarAtOwnTarget ∈ [intRow,fixedScalarAtOwnTarget]
    simp)
  exact two_kinds_ref_cannot_satisfy_scalar_target442 _ _ conflict.1

#print axioms two_kinds_ref_cannot_satisfy_scalar_target442
#print axioms old_target_constraint_has_a_model442
#print axioms cannot_rewrite_a_preconstrained_scalar_output442
def constrainedPlan : B6MixedRhs401 constrainedCore false (normalize (bodyPattern (.explicit out))) :=
  refPlan 9 6 8 originalUse mode rfl

def constrainedAtlas : B6OccurrenceAtlas401 constrainedCore := ⟨fun q o i body =>
  if q.occurrence == [71,3] && o == 0 && i.val == 0 then
    if h : body = .explicit out then some (h.symm ▸ constrainedPlan) else none
  else none⟩

def constrainedProblem : Problem := ⟨⟨constrainedCore,constrainedAtlas⟩,problem.root⟩

theorem real_preconstrained_target_still_reads_original_source442 :
    (replay442 constrainedProblem wire).isSome = true := by decide +kernel

def constrainedReplay :=
  (replay442 constrainedProblem wire).get real_preconstrained_target_still_reads_original_source442

theorem constrainedMixedCanOnlyBeItsOriginalSymbolicValue442 (m : I72.Model) :
    (constrainedReplay.event.outputs i0).receipt.actualEquation m =
      some (21,nominal 9 [.inr (m.assignment 1).2,.inl (m.assignment 2).1]) := rfl

theorem no_actual_fit_can_retain_loaded_scalar_as_mixed_rhs442 (m : I72.Model)
    (fit : I72.Fits constrainedProblem.state m) :
    ¬FixedTargets m constrainedReplay.event := by
  intro bad
  obtain ⟨rhs,receipt,claimed⟩ := bad i0
  rw [constrainedMixedCanOnlyBeItsOriginalSymbolicValue442] at receipt
  have st := (Prod.mk.inj (Option.some.inj receipt)).2
  subst rhs
  have old := fit.1.1.2 fixedScalarAtOwnTarget (by
    change fixedScalarAtOwnTarget ∈ [intRow,fixedScalarAtOwnTarget]
    simp)
  change Equivalent (m.assignment 21).1 (.base .int) at old
  exact two_kinds_ref_cannot_satisfy_scalar_target442 _ _
    (CommonNominalFullCarrier.subtype_trans claimed.2 old.1)

#print axioms real_preconstrained_target_still_reads_original_source442
#print axioms constrainedMixedCanOnlyBeItsOriginalSymbolicValue442
#print axioms no_actual_fit_can_retain_loaded_scalar_as_mixed_rhs442
```
