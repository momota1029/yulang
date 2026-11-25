import Yulang.GeneralDeclarativeI65I72OrderedNativeAssembly407

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleOutermostResolver (Tree Dictionary Result Summarizes All₂)

/-- An extension by a genuinely ordered all-visible native rule.
The independent head computation yields an ElectedNativeHead407.
The body reuses the original B6 occurrence, and an exact strictly
smaller finite source is recorded at the original output ordinal. -/
inductive OrderedNativeClassifies407 (s : State) (q : Request) : Result → Prop where
  | earlier : FiniteVerdict406 s q result → OrderedNativeClassifies407 s q result
  | ordered {p : Request} {d : Dictionary}
      {original : Fin p.demand.outputs.length → NamedMixedReceipt401 s.core}
      (before : FiniteNative406 s p d original) (i : Fin p.demand.outputs.length)
      {input : NativeElectionInput407 s q ⟨p,d,i,original i⟩}
      (step : OrderedNativeStep407 input trees) (kids : All₂ Summarizes trees (dKids.map Result.selected)) :
        OrderedNativeClassifies407 s q (.selected (.node step.elected.row.id dKids))

/-- When the entire tape is covered and exactly one tag agrees,
assemble the actual new derivation without a selected judgment or
a winner as input, and return its same-index ledger. Body facts
are addressed to the actual winner's literal frame. -/
theorem actual_mixed_tags_construct_native_classifies407 {s p d original q trees dKids}
    (before : FiniteNative406 s p d original) (i : Fin p.demand.outputs.length)
    (input : NativeElectionInput407 s q ⟨p,d,i,original i⟩)
    (winner : VisibleIndex407 s q)
    (tag : (input.roots winner).unary.key = input.read.found)
    (other : ∀ j : VisibleIndex407 s q, j ≠ winner → (input.roots j).unary.key ≠ input.read.found)
    (actual : NativeActualPath407 input)
    (body : ∀ e : ElectedNativeHead407 input, e.winner = winner →
      ∀ i : Fin q.demand.outputs.length, NamedMixedOutput401 s.b6 (OrderedNativeFrame407 e actual) i)
    (fixed : ∀ (e : ElectedNativeHead407 input) (same : e.winner = winner),
      ∀ k : Fin q.demand.outputs.length, ∃ code : Expr, fixedValueCode403 (body e same k).rhs = some code ∧
        (⟨q.demand.outputs[k].target,code⟩ : Equation) ∈ s.core.current.ordinary.equations)
    (clauses : LiteralVariableWhere403 (visible s.core q)[winner])
    (whereRows : ∀ e : ElectedNativeHead407 input, e.winner = winner →
      WhereForest PriorSource406 s (frameWhereKids400 (OrderedNativeFrame407 e actual)) trees)
    (children : All₂ Summarizes trees (dKids.map Result.selected)) :
    OrderedNativeClassifies407 s q (.selected (.node (visible s.core q)[winner].id dKids)) ∧
      ∃ (step : OrderedNativeStep407 input trees) (ledger : OrderedNativeLedger407 (before := before) step dKids),
        step.elected.winner = winner ∧ (∀ visit ∈ CompletedVisits407 input.read input.roots,
          ¬CurrentCycleAt s visit.site) ∧
        ∀ m, Fits s m → OrderedNativeMeaning407 step m ∧ ledger.lower.Means m ∧
          DictionaryEvidenceForest s m (frameWhereKids400 step.frame) dKids := by
  have h := exact_single_native_hit_elects407 input winner tag other
  obtain ⟨e⟩ := h
  have eq : e.winner = winner := by
    have hit := (native_live_is_exact_not_first_match407 input e.winner).mp (by simp [e.one])
    by_cases same : e.winner = winner
    · exact same
    · exact False.elim ((other _ same) (a_literal_typed_nominal_cannot_name_different_constructors406 _
        hit (actual_typed_point_yields_literal_declared_code404 (original i).rhs input.read.sourceType).1))
  have clauseOk : LiteralVariableWhere403 e.row := by
    simpa only [ElectedNativeHead407.row,eq] using clauses
  let step : OrderedNativeStep407 input trees :=
    ⟨e,actual,body e eq,fixed e eq,clauseOk,whereRows e eq⟩
  obtain ⟨ledger,safe,_,many⟩ :=
    actual_ordered_native_selection_assembles_one_ledger407 before i step children
  have selection := OrderedNativeClassifies407.ordered before i step children
  change OrderedNativeClassifies407 s q (.selected (.node (visible s.core q)[e.winner].id dKids)) at selection
  have outcome := congrArg (fun j : VisibleIndex407 s q => Result.selected (.node (visible s.core q)[j].id dKids)) eq
  have transported := outcome ▸ selection
  exact ⟨transported,step,ledger,eq,safe,many⟩

theorem raw_root_K2_still_has_priority407 {s q} (raw : RootCycle s q) :
    OrderedNativeClassifies407 s q .rejected ∧ ∀ d, ¬OrderedNativeClassifies407 s q (.selected d) := by
  obtain ⟨rejected,oldCannot⟩ := raw_root_K2_has_priority_in_finite_extension406 raw
  refine ⟨.earlier rejected,?_⟩
  intro d chosen
  cases chosen with
  | earlier prior => exact oldCannot _ prior
  | @ordered _ _ _ _ _ _ _ input _ _ => exact input.rawSafe raw

end Yulang.GeneralDeclarativeI65.I72
