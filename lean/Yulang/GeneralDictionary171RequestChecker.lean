import Yulang.GeneralDictionary171LocalInspectionObservation

/-! Executable conservative checking of finite observed materialization requests.
False means this checker did not certify a request, never semantic rejection. -/
namespace Yulang.GeneralDictionary171RequestChecker
open GeneralNominalInspection (Query)
open GeneralNominalRecursiveInspection
open GeneralNominalMaterialization (Request)
open GeneralDictionary171InspectionObservation (Closed)
open GeneralDictionary171LocalInspectionObservation (PointInspection)

mutual
  def closedQuery : Query → Bool
    | .scalar _ => true
    | .nominal _ children => closedQueries children
    | _ => false
  def closedQueries : List Query → Bool
    | [] => true
    | query :: rest => closedQuery query && closedQueries rest
end

mutual
  theorem closedQuery_sound (query : Query) (good : closedQuery query = true) : Closed query := by
    cases query with
    | scalar base => exact .scalar base
    | nominal name children => exact .nominal name children (closedQueries_sound children good)
    | variables => cases good
    | node => cases good
    | deferred => cases good
  termination_by sizeOf query
  decreasing_by all_goals simp_all; omega
  theorem closedQueries_sound (queries : List Query) (good : closedQueries queries = true) :
      ∀ query ∈ queries, Closed query := by
    cases queries with
    | nil => intro query member; cases member
    | cons query rest =>
      have both : closedQuery query = true ∧ closedQueries rest = true := by simpa only [closedQueries,Bool.and_eq_true] using good
      intro found member
      rcases List.mem_cons.mp member with rfl | member
      · exact closedQuery_sound found both.1
      · exact closedQueries_sound rest both.2 found member
  termination_by sizeOf queries
  decreasing_by all_goals simp_all; omega
end

def pointArguments : List (GeneralNominalState.Parameter n) → Bool
  | [] => true
  | .type (lower,upper) :: rest => (lower == upper) && pointArguments rest
  | .row _ :: _ => false

theorem pointArguments_sound (arguments : List (GeneralNominalState.Parameter n))
    (good : pointArguments arguments = true) :
    ∃ k, ∃ slots : Fin k → Fin n,
      arguments = List.ofFn fun i => .type (slots i,slots i) := by
  induction arguments with
  | nil => exact ⟨0,Fin.elim0,rfl⟩
  | cons argument rest ih =>
    cases argument with
    | row => cases good
    | type bounds =>
      have both : (bounds.1 == bounds.2) = true ∧ pointArguments rest = true := by simpa only [pointArguments,Bool.and_eq_true] using good
      have equal : bounds.1 = bounds.2 := by simpa using both.1
      obtain ⟨k,slots,parameters⟩ := ih both.2
      refine ⟨k+1,Fin.cases bounds.1 slots,?_⟩
      rw [List.ofFn_succ]
      simp only [Fin.cases_zero,Fin.cases_succ]
      rw [← parameters]
      cases bounds
      simp_all

def pointReport (state : GeneralNominalState.State) (report : Report state) : Bool :=
  report.inspected.all fun bounds => match state.nominals bounds.1 with
    | none => true
    | some descriptor => pointArguments descriptor.arguments

theorem pointReport_sound (state : GeneralNominalState.State) (report : Report state)
    (good : pointReport state report = true) : PointInspection state report := by
  intro bound member descriptor recorded
  have one := List.all_eq_true.mp good bound member
  rw [recorded] at one
  exact pointArguments_sound _ one

def finishedReport (report : Report state) : Bool :=
  report.blocked.isEmpty && report.conflicts.isEmpty && report.arity.isEmpty

theorem finishedReport_sound (report : Report state) (good : finishedReport report = true) :
    Finished report := by
  have facts : (report.blocked = [] ∧ report.conflicts = []) ∧ report.arity = [] := by
    simpa [finishedReport,List.isEmpty_iff] using good
  exact ⟨facts.1.1,facts.1.2,facts.2⟩

/-- Search the actual snapshot, retaining the physical slot of the chosen
source ID. Duplicate source IDs are tried independently rather than conflated. -/
def checkAt (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (request : Request)
    (slot : Fin state.base.slots) : Bool :=
  let query := GeneralNominalInspection.translate state.constructors interpretation
    (GeneralDeclarationPatterns.normalize request.pattern)
  let report := inspect state query (slot,slot) (some (.source request.target))
  (request.target == state.base.source slot) && closedQuery query &&
    finishedReport report && pointReport state report

def checkRequest (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (request : Request) : Bool :=
  (List.finRange state.base.slots).any (checkAt state interpretation request)

def checkRequests (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (requests : List Request) : Bool :=
  requests.all (checkRequest state interpretation)

theorem checkAt_sound (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (request : Request)
    (slot : Fin state.base.slots) (good : checkAt state interpretation request slot = true) :
    request.target = state.base.source slot ∧
    Nonempty (GeneralDictionaryObservedFiniteRequests.Tree state slot
      (GeneralNominalInspection.translate state.constructors interpretation
        (GeneralDeclarationPatterns.normalize request.pattern))) := by
  simp only [checkAt,Bool.and_eq_true,beq_iff_eq] at good
  exact ⟨good.1.1.1,GeneralDictionary171LocalInspectionObservation.inspected_tree state _
    (closedQuery_sound _ good.1.1.2) slot _
    (finishedReport_sound _ good.1.2) (pointReport_sound _ _ good.2)⟩

theorem checkRequest_sound (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (request : Request)
    (good : checkRequest state interpretation request = true) :
    ∃ slot : Fin state.base.slots, request.target = state.base.source slot ∧
    Nonempty (GeneralDictionaryObservedFiniteRequests.Tree state slot
      (GeneralNominalInspection.translate state.constructors interpretation
        (GeneralDeclarationPatterns.normalize request.pattern))) := by
  obtain ⟨slot,_,works⟩ := List.any_eq_true.mp good
  exact ⟨slot,checkAt_sound state interpretation request slot works⟩

theorem checkRequests_sound (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (requests : List Request)
    (good : checkRequests state interpretation requests = true) :
    GeneralDictionaryObservedFiniteRequests.Observed state interpretation requests := by
  intro request member
  exact checkRequest_sound state interpretation request (List.all_eq_true.mp good request member)
end Yulang.GeneralDictionary171RequestChecker
