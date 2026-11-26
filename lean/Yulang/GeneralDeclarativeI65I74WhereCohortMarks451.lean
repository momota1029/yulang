import Yulang.GeneralDeclarativeI65I74WhereCohortDiagnostic451

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem)
open RetainedFull445
open GeneralDeclarations (Clause Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (point)

/-- Literal diagnostic carriers only. We do not choose a displayed
representative or alter the original exact-trace checker. -/
structure OriginalMark where
  ordinal : Nat
  writtenId : Nat
  request : I72.Request
  actualCenter : Nat
  classLabel : Nat
  rawK2 : Bool

def OriginalDiagnostic.marks {p : Problem} {a : ParentSelection p} (d : OriginalDiagnostic a) :
    List OriginalMark :=
  List.zipWith (fun (q,i) (c,((_,center),label),k2) =>
      ⟨i,c.id,q,center,label,k2⟩)
    a.children.zipIdx
    (List.zipWith (fun c tagged => (c,tagged)) a.decl.requirements
      (List.zipWith Prod.mk d.cohorts.labelled d.bits))

def OriginalDiagnostic.atClass {p : Problem} {a : ParentSelection p}
    (d : OriginalDiagnostic a) (label : Nat) : List OriginalMark :=
  d.marks.filter fun m => m.classLabel == label

theorem every_actual_clause_has_a_preserved_location_mark451 {p : Problem} {a : ParentSelection p}
    (d : OriginalDiagnostic a) {i : Nat} {c : Clause} (original : a.decl.requirements[i]? = some c) :
    ∃ binder payload label bit,
      c.arguments = [.var binder] ∧ (binder,payload) ∈ a.chosen.roster.bindings ∧
      let actual : I72.Request := ⟨p.root.occurrence ++ [i],⟨c.role,[point payload],[]⟩⟩
      d.marks[i]? = some ⟨i,c.id,actual,payload,label,bit⟩ ∧
        (bit = true ↔ RootCycle p.state actual) := by
  obtain ⟨b,pay,pattern,fromHead,_,actual⟩ := known_original_clause_has_actual_payload451 a original
  let q : I72.Request := ⟨p.root.occurrence ++ [i],⟨c.role,[point pay],[]⟩⟩
  have yes : a.children[i]? = some q := actual
  obtain ⟨atPoint,label,origin⟩ := d.cohorts.indexed i yes
  obtain ⟨bit,flag,exact⟩ := status_position_is_actual_child451 d.status i yes
  have full : atPoint = (⟨pay,rfl⟩ : ActualPoint q) := actual_point_center_unique451 _ _
  refine ⟨b,pay,label,bit,pattern,fromHead,?_,exact⟩
  unfold OriginalDiagnostic.marks
  rw [List.getElem?_zipWith,List.getElem?_zipIdx,List.getElem?_zipWith,List.getElem?_zipWith,
    yes,original,origin,flag,full]
  simp [ActualPoint.tag,q]

theorem only_marks_of_selected_class451 {p : Problem} {a : ParentSelection p}
    (d : OriginalDiagnostic a) (label : Nat) (m : OriginalMark) :
    m ∈ d.atClass label ↔ m ∈ d.marks ∧ m.classLabel = label := by
  simp [OriginalDiagnostic.atClass]

theorem validated_class_location_list_keeps_source_order451 {p : Problem} {a : ParentSelection p}
    (d : OriginalDiagnostic a) (label : Nat) : (d.atClass label).Sublist d.marks := by
  exact List.filter_sublist

structure SourceDiagnosticWire where
  parent : ParentWire
  diagnostic : DiagnosticWire

structure AnnotatedOriginalDiagnostics (p : Problem) where
  parent : ParentSelection p
  diagnostics : OriginalDiagnostic parent

/-- Run the source reader at the real FullProblem. This is an
intermediate evidence-producing operation, never a verdict selector. -/
def readOriginalWhereProfiles451 (p : FullProblem) (w : SourceDiagnosticWire) :
    Option (AnnotatedOriginalDiagnostics p.old) :=
  match only : visible p.state.base.core p.root with
  | [d] => do
    let original ← readParentChoice p.old d only w.parent
    let parent : ParentSelection p.old := ⟨d,original⟩
    let data ← readDiagnostic parent w.diagnostic
    pure ⟨parent,data⟩
  | _ => none

theorem independent_selected_original_profiles_have_finite_wire451 (p : FullProblem)
    (data : AnnotatedOriginalDiagnostics p.old) :
    ∃ w, readOriginalWhereProfiles451 p w = some data := by
  obtain ⟨pw,parent⟩ := independent_list_frame_replays_exactly450 data.parent.chosen
  obtain ⟨dw,diag⟩ := actual_diagnostic_preparation_has_finite_exact_data451 data.parent data.diagnostics
  refine ⟨⟨pw,dw⟩,?_⟩
  simp only [readOriginalWhereProfiles451]
  split
  · rename_i d only
    have same : d = data.parent.decl := List.singleton_inj.mp (only.symm.trans data.parent.chosen.only)
    subst d
    rw [show readParentChoice p.old data.parent.decl only pw = some data.parent.chosen from parent]
    cases data with
    | mk a e =>
      cases a with
      | mk d c =>
        simp only [Bind.bind,Option.bind,Option.pure_def] at diag ⊢
        have exactEq : readDiagnostic (⟨d,c⟩ : ParentSelection p.old) dw = some e := diag
        rw [exactEq]
  · rename_i missing
    exact (missing _ data.parent.chosen.only).elim

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451
