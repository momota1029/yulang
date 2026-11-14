import Yulang.GeneralNominalRootedView196

set_option backward.isDefEq.respectTransparency false
/-! Successful finite observation traces for descriptor-changing reinspection.
No trace constructor mentions semantic Evidence or whole-report equality. -/
namespace Yulang.GeneralNominalInspectionTrace197
open GeneralNominalInspection (Query Bounds)
open GeneralNominalRecursiveInspection
open GeneralNominalViewTransport196

mutual
  inductive Trace (state : GeneralNominalState.State) (next : View state) :
      Query → Bounds state → Prop where
    | variables : Trace state next (.variables names) bounds
    | scalar
        (oldNominal : state.nominals bounds.1 = none)
        (newNominal : next.nominals bounds.1 = none)
        (oldHead : state.view.heads bounds.1 = .scalar expected)
        (newHead : next.view.heads bounds.1 = .scalar expected) :
        Trace state next (.scalar expected) bounds
    | structural
        (oldLower : state.view.heads bounds.1 = .structural lower left)
        (oldUpper : state.view.heads bounds.2 = .structural upper right)
        (newLower : next.view.heads bounds.1 = .structural newLowerKind newLeft)
        (newUpper : next.view.heads bounds.2 = .structural newUpperKind newRight)
        (lowerShape : state.view.shapes lower = expected)
        (upperShape : state.view.shapes upper = expected)
        (newLowerShape : next.view.shapes newLowerKind = expected)
        (newUpperShape : next.view.shapes newUpperKind = expected)
        (leftSame : List.ofFn newLeft = List.ofFn left)
        (rightSame : List.ofFn newRight = List.ofFn right)
        (children : Traces state next patterns ((List.ofFn left).zip (List.ofFn right))) :
        Trace state next (.node expected patterns) bounds
    | nominalPoint
        (oldNominal : state.nominals slot = some descriptor)
        (newNominal : next.nominals slot = some descriptor)
        (name : descriptor.declaration.name = expected)
        (arguments : typeArguments descriptor.arguments = some actuals)
        (children : Traces state next patterns actuals) :
        Trace state next (.nominal expected patterns) (slot,slot)
    | nominalInterval
        (different : bounds.1 ≠ bounds.2)
        (oldLower : state.nominals bounds.1 = some lower)
        (newLower : next.nominals bounds.1 = some lower)
        (oldUpper : state.nominals bounds.2 = some upper)
        (newUpper : next.nominals bounds.2 = some upper)
        (lowerName : lower.declaration.name = expected)
        (upperName : upper.declaration.name = expected)
        (lowerArguments : typeArguments lower.arguments = some left)
        (upperArguments : typeArguments upper.arguments = some right)
        (lowerChildren : Traces state next patterns left)
        (upperChildren : Traces state next patterns right) :
        Trace state next (.nominal expected patterns) bounds
  inductive Traces (state : GeneralNominalState.State) (next : View state) :
      List Query → List (Bounds state) → Prop where
    | nil : Traces state next [] []
    | cons : Trace state next query bounds → Traces state next queries intervals →
        Traces state next (query :: queries) (bounds :: intervals)
end

theorem report_visit (state : GeneralNominalState.State) (next : View state)
    (bounds : Bounds state) (origin : Option Origin) (test : Test) (value : Report state) :
    report next (Report.visit bounds origin test value) =
      Report.visit (state := replace state next) bounds origin test (report next value) := rfl

@[simp] theorem replace_nominals (state : GeneralNominalState.State) (next : View state) :
    (replace state next).nominals = next.nominals := rfl

mutual
  theorem trace_report (trace : Trace state next query bounds) (origin : Option Origin) :
      inspect (replace state next) query bounds origin = report next (inspect state query bounds origin) := by
    cases trace with
    | variables => exact GeneralNominalVariableView196.inspect_variable _ _ _ _ _
    | scalar oldNominal newNominal oldHead newHead =>
      simp [inspect,replace,oldNominal,newNominal,oldHead,newHead,report,Report.visit]
    | structural oldLower oldUpper newLower newUpper lowerShape upperShape
        newLowerShape newUpperShape leftSame rightSame children =>
      rename_i lower left upper right newLowerKind newLeft newUpperKind newRight expected patterns
      change (replace state next).view.heads bounds.1 = .structural newLowerKind newLeft at newLower
      change (replace state next).view.heads bounds.2 = .structural newUpperKind newRight at newUpper
      change (replace state next).view.shapes newLowerKind = expected at newLowerShape
      change (replace state next).view.shapes newUpperKind = expected at newUpperShape
      simp only [inspect,oldLower,oldUpper,newLower,newUpper,lowerShape,upperShape,
        newLowerShape,newUpperShape,and_self,↓reduceIte,leftSame,rightSame]
      rw [traces_report children,report_visit]
    | nominalPoint oldNominal newNominal name arguments children =>
      simp only [inspect,replace_nominals,oldNominal,newNominal,name,arguments,↓reduceIte]
      rw [traces_report children,report_visit]
      rfl
    | nominalInterval different oldLower newLower oldUpper newUpper lowerName upperName
        lowerArguments upperArguments lowerChildren upperChildren =>
      simp only [inspect,replace_nominals,oldLower,newLower,oldUpper,newUpper,lowerName,upperName,
        lowerArguments,upperArguments,different,↓reduceIte]
      rw [traces_report lowerChildren,traces_report upperChildren,
        report_visit,GeneralNominalVariableView196.report_append]
      rfl
  termination_by sizeOf query

  theorem traces_report (traces : Traces state next queries intervals)
      (origins : Nat → Option Origin) (index : Nat) :
      inspectMany (replace state next) queries intervals origins index =
        report next (inspectMany state queries intervals origins index) := by
    cases traces with
    | nil => simp [inspectMany,report]
    | cons first rest =>
      simp only [inspectMany]
      rw [trace_report first,traces_report rest,GeneralNominalVariableView196.report_append]
  termination_by sizeOf queries
end

/-- Compute the real finite queries first; preserve only the descriptor/head
observations traversed by this successful nominal/scalar/variable trace. -/
theorem rechecked_of_trace (old : GeneralNominalCandidates.Context) (next : View old.state)
    (declaration : GeneralDeclarations.Declaration) (bounds : List (Bounds old.state))
    (trace : Traces old.state next
      (GeneralNominalInspection.queries old.state old.interpretation declaration) bounds) :
    Rechecked old next declaration bounds := by
  unfold Rechecked GeneralNominalRecursiveCandidates.report
  have h : inspectMany (context old next).state
      (GeneralNominalInspection.queries (context old next).state (context old next).interpretation declaration)
      bounds (fun _ => none) 0 = report next (inspectMany old.state
        (GeneralNominalInspection.queries old.state old.interpretation declaration)
        bounds (fun _ => none) 0) := traces_report trace _ _
  dsimp only
  rw [h]
  rfl
end Yulang.GeneralNominalInspectionTrace197
