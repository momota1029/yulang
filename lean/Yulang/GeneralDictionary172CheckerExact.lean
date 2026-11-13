import Yulang.GeneralDictionary171RequestChecker

/-! Exactness for the conservative checker's explicit physical-slot certificate.
This is not completeness for semantic Evidence or for the language. -/
namespace Yulang.GeneralDictionary172CheckerExact
open GeneralNominalInspection (Query)
open GeneralNominalRecursiveInspection
open GeneralNominalMaterialization (Request)
open GeneralDictionary171InspectionObservation (Closed)
open GeneralDictionary171LocalInspectionObservation (PointInspection)
open GeneralDictionary171RequestChecker

theorem closedQuery_complete (query : Query) (closed : Closed query) :
    closedQuery query = true := by
  induction closed with
  | scalar => rfl
  | nominal name children closed ih =>
    change closedQueries children = true
    induction children with
    | nil => rfl
    | cons q qs rest =>
      simp only [closedQueries, Bool.and_eq_true]
      exact ⟨ih q (by simp), rest (fun q h => closed q (by simp [h]))
        (fun q h => ih q (by simp [h]))⟩

theorem closedQuery_iff (query : Query) : closedQuery query = true ↔ Closed query :=
  ⟨closedQuery_sound query, closedQuery_complete query⟩

theorem pointArguments_ofFn (slots : Fin k → Fin n) :
    pointArguments (List.ofFn fun i => GeneralNominalState.Parameter.type (slots i,slots i)) = true := by
  induction k with
  | zero => simp [pointArguments]
  | succ k ih =>
    rw [List.ofFn_succ]
    simpa [pointArguments] using ih (fun i => slots i.succ)

theorem pointArguments_iff (arguments : List (GeneralNominalState.Parameter n)) :
    pointArguments arguments = true ↔
      ∃ k, ∃ slots : Fin k → Fin n,
        arguments = List.ofFn fun i => .type (slots i,slots i) := by
  constructor
  · exact pointArguments_sound arguments
  · rintro ⟨k,slots,rfl⟩
    exact pointArguments_ofFn slots

theorem pointReport_iff (state : GeneralNominalState.State) (report : Report state) :
    pointReport state report = true ↔ PointInspection state report := by
  constructor
  · exact pointReport_sound state report
  · intro points
    apply List.all_eq_true.mpr
    intro bound member
    cases recorded : state.nominals bound.1 with
    | none => rfl
    | some descriptor =>
      exact (pointArguments_iff descriptor.arguments).mpr (points bound member descriptor recorded)

theorem finishedReport_iff (report : Report state) :
    finishedReport report = true ↔ Finished report := by
  simp [finishedReport, Finished, List.isEmpty_iff, and_assoc]

/-- Exact source identity, closed query, actual finished inspection and local
point descriptor bounds. No semantic Evidence is assumed. -/
def At (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (request : Request)
    (slot : Fin state.base.slots) : Prop :=
  let query := GeneralNominalInspection.translate state.constructors interpretation
    (GeneralDeclarationPatterns.normalize request.pattern)
  let report := inspect state query (slot,slot) (some (.source request.target))
  request.target = state.base.source slot ∧ Closed query ∧
    Finished report ∧ PointInspection state report

theorem checkAt_iff (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (request : Request)
    (slot : Fin state.base.slots) :
    checkAt state interpretation request slot = true ↔ At state interpretation request slot := by
  simp [checkAt, At, closedQuery_iff, finishedReport_iff, pointReport_iff, and_assoc]

theorem checkRequest_iff (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (request : Request) :
    checkRequest state interpretation request = true ↔
      ∃ slot, At state interpretation request slot := by
  simp [checkRequest, List.any_eq_true, checkAt_iff]

theorem checkRequests_iff (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (requests : List Request) :
    checkRequests state interpretation requests = true ↔
      ∀ request ∈ requests, ∃ slot, At state interpretation request slot := by
  simp [checkRequests, List.all_eq_true, checkRequest_iff]

end Yulang.GeneralDictionary172CheckerExact
