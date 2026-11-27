import Yulang.GeneralDeclarativeI65I74RecordTraversal455
import Yulang.GeneralDeclarativeI65I74FullState444

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordTrail455
open Yulang.GeneralDeclarativeI65
open RecordTraversal455 (OpenOps Trail TrailPath)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open Core.PresenceGeneration (TyTerm)
open RetainedFull445

mutual
  private def exactExprEq (a b : Expr) : Decidable (a = b) := by
    cases a <;> cases b
    case variable.variable a b => exact decidable_of_iff (a = b) (by simp)
    case primitive.primitive a xs b ys =>
      letI := exactExprsEq xs ys
      exact decidable_of_iff (a = b ∧ xs = ys) (by simp)
    case nominal.nominal a xs b ys =>
      letI := exactExprsEq xs ys
      exact decidable_of_iff (a = b ∧ xs = ys) (by simp)
    case record.record a x xs b y ys =>
      letI := exactExprEq x y
      letI := exactExprEq xs ys
      exact decidable_of_iff (a = b ∧ x = y ∧ xs = ys) (by simp)
    case variant.variant a x b y =>
      letI := exactExprEq x y
      exact decidable_of_iff (a = b ∧ x = y) (by simp)
    case join.join x xs y ys =>
      letI := exactExprEq x y
      letI := exactExprEq xs ys
      exact decidable_of_iff (x = y ∧ xs = ys) (by simp)
    all_goals exact isFalse (by intro h; cases h)
  private def exactExprsEq (a b : List Expr) : Decidable (a = b) := by
    cases a with
    | nil => cases b <;> exact inferInstance
    | cons x xs =>
      cases b with
      | nil => exact isFalse (by intro h; cases h)
      | cons y ys =>
        letI := exactExprEq x y
        letI := exactExprsEq xs ys
        exact decidable_of_iff (x = y ∧ xs = ys) (by simp)
end

local instance : DecidableEq Expr := exactExprEq

def closedRecordTerm : TyTerm Nat → Option Expr
  | .emptyRecord => some (.primitive .emptyRecord [])
  | .record f (.var n) tail =>
    (closedRecordTerm tail).map fun more => .record f (.variable n) more
  | _ => none

/-- Only exact independently authored native native at the actual row
owner can justify opening. A raw result alone (even if it closes a
K2 walk at an already reached site) is not an opener. -/
def SourceOpen (s : GeneralDeclarativeI65.State) (row : Equation) : Prop :=
  ∃ orig ∈ s.origins, ∃ term : TyTerm Nat,
    orig.slot = row.left ∧ orig.endpoint = .ordinary term ∧ closedRecordTerm term = some row.right

def checkSourceOpen (s : GeneralDeclarativeI65.State) (row : Equation)
    (ordinal : Nat) : Bool :=
  match s.origins[ordinal]? with
  | some orig =>
    match orig.endpoint with
    | .ordinary term => decide (orig.slot = row.left ∧ closedRecordTerm term = some row.right)
    | _ => false
  | none => false

theorem source_opener_iff_finite_original_index455 (s : GeneralDeclarativeI65.State)
    (row : Equation) :
    (∃ i, checkSourceOpen s row i = true) ↔ SourceOpen s row := by
  constructor
  · rintro ⟨ordinal,checked⟩
    cases orig : s.origins[ordinal]? with
    | none => simp [checkSourceOpen,orig] at checked
    | some source =>
      cases auth : source.endpoint with
      | ordinary term =>
        have exact : source.slot = row.left ∧ closedRecordTerm term = some row.right := by
          simpa [checkSourceOpen,orig,auth] using checked
        exact ⟨source,List.mem_of_getElem? orig,term,exact.1,auth,exact.2⟩
      | nominal key args => simp [checkSourceOpen,orig,auth] at checked
  · rintro ⟨orig,inOriginal,term,slot,native,decoder⟩
    obtain ⟨i,atI⟩ := List.mem_iff_getElem?.mp inOriginal
    exact ⟨i,by simp [checkSourceOpen,atI,slot,native,decoder]⟩

def sourceOps (s : GeneralDeclarativeI65.State) : OpenOps where
  Token := Nat
  allowed := fun _ row => SourceOpen s row
  check := fun _ row i => checkSourceOpen s row i
  exactCheck := fun _ row => source_opener_iff_finite_original_index455 s row

theorem actual_original_opener_has_same_model_native_read455
    {s : GeneralDeclarativeI65.State} {row : Equation} (auth : SourceOpen s row)
    (m : I72.Model) (fit : GeneralDeclarativeI65.Fits s m) :
    ∃ term, m.nativeSyntax row.left = some (.ordinary term) ∧
      closedRecordTerm term = some row.right := by
  obtain ⟨orig,seen,term,owner,native,decode⟩ := auth
  exact ⟨term,by simpa only [owner,native] using fit.2 orig seen,decode⟩

open GeneralDeclarativeGraphRows321 (shapeOf)
open GeneralDeclarativeInspect321 (fieldPatterns)
open GeneralDeclarativeK2Graph321 (Shape)

def ModelOpen (s : GeneralDeclarativeI65.State) (m : I72.Model)
    (root : Nat) (code : Expr) (label child : Nat) (query : Expr) : Prop :=
  ∃ row ∈ s.current.ordinary.equations, ∃ fs, ∃ term,
    GeneralDeclarativeLowerKnown321.Alias s.current.ordinary root row.left ∧
    m.nativeSyntax row.left = some (.ordinary term) ∧ closedRecordTerm term = some row.right ∧
    CommonNominalFullCarrier.Equivalent (m.assignment row.left).1
      (GeneralNominalCenteredHeadMatExpressions.value (GeneralDeclarativeHead320.environment m.assignment) .actual row.right) ∧
    shapeOf row.right = some (.record fs) ∧ (label,child) ∈ fs ∧
    (label,query) ∈ fieldPatterns code

inductive ModelTrail (s : GeneralDeclarativeI65.State) (m : I72.Model) :
    Nat → Expr → TrailPath → Nat → Prop where
  | stop : GeneralDeclarativeInspect321.Inspects code → ModelTrail s m n code [] n
  | down : ModelOpen s m root code field child query → ModelTrail s m child query rest site →
    ModelTrail s m root code ((field,child)::rest) site

theorem independently_authored_trail_has_exact_source_reads_in_same_model455
    {s : GeneralDeclarativeI65.State} {root code path site}
    (actual : Trail s.current.ordinary (sourceOps s) root code path site)
    (m : I72.Model) (fit : GeneralDeclarativeI65.Fits s m) :
    ModelTrail s m root code path site := by
  induction actual with
  | stop inspect => exact .stop inspect
  | down safe step rest ih =>
    obtain ⟨row,atRow,fs,link,shape,allowed,field,pat⟩ := step
    obtain ⟨term,seen,matchRow⟩ := actual_original_opener_has_same_model_native_read455 allowed m fit
    exact .down ⟨row,atRow,fs,term,link,seen,matchRow,fit.1.1.2 row atRow,shape,field,pat⟩ ih

end Yulang.GeneralDeclarativeI65.I72.RecordTrail455
