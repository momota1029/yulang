import Yulang.GeneralObservedMetadataTranslation290

/-! Compare the actual recursive inspector under two sets of translation
inputs on the same recorded observation state. Local equality preserves
the entire report, not merely its three encoded diagnostics. -/
namespace Yulang.GeneralObservedMetadataReport290
open GeneralDeclarationPatterns (Constructors)
open GeneralDeclarations (Declaration)
open GeneralNominalInspection (Interpretation Query translate Bounds)
open GeneralNominalRecursiveInspection (Report inspectMany)
open GeneralObservedMetadataKeys290 (headKeys candidateKeys member_many candidate_key)
open GeneralObservedMetadataEntry290 (LocalEqual agree agree_exact)
open GeneralNominalCandidates (Context)

def queriesFrom (c : Constructors) (i : Interpretation) (d : Declaration) : List Query :=
  d.normalHead.map (translate c i)

theorem queries_eq (c : Constructors) (i : Interpretation) (e : Constructors) (j : Interpretation)
    (d : Declaration) (h : LocalEqual (headKeys d) c i e j) :
    queriesFrom c i d = queriesFrom e j d := by
  unfold queriesFrom
  exact List.map_congr_left (fun p comes =>
    GeneralObservedMetadataTranslation290.translate_eq c i e j p
      (h.restrict (fun _ present => member_many comes present)))

def reportFrom (state : GeneralNominalState.State) (c : Constructors) (i : Interpretation)
    (d : Declaration) (bounds : List (Bounds state)) : Report state :=
  let result := inspectMany state (queriesFrom c i d) bounds (fun _ => none) 0
  { result with checked := bounds ++ result.checked }

theorem report_actual (ctx : Context) (d : Declaration) (bounds : List (Bounds ctx.state)) :
    reportFrom ctx.state ctx.state.constructors ctx.interpretation d bounds =
      GeneralNominalRecursiveCandidates.report ctx d bounds := rfl

theorem report_eq (state : GeneralNominalState.State) (c : Constructors) (i : Interpretation)
    (e : Constructors) (j : Interpretation) (d : Declaration) (bounds : List (Bounds state))
    (h : LocalEqual (headKeys d) c i e j) : reportFrom state c i d bounds = reportFrom state e j d bounds := by
  unfold reportFrom
  rw [queries_eq _ _ _ _ _ h]

theorem reports_of_candidates (state : GeneralNominalState.State) (c : Constructors) (i : Interpretation)
    (e : Constructors) (j : Interpretation) (ds : List Declaration)
    (agreeCheck : agree (candidateKeys ds) c i e j = true) :
    ∀ d ∈ ds, ∀ bounds, reportFrom state c i d bounds = reportFrom state e j d bounds := by
  intro d member bounds
  exact report_eq _ _ _ _ _ _ _ (((agree_exact ..).mp agreeCheck).restrict
    (fun _ h => candidate_key member h))

end Yulang.GeneralObservedMetadataReport290
