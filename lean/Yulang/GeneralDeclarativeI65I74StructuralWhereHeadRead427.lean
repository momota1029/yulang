import Yulang.GeneralDeclarativeI65I74StructuralWherePair427

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere427
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeHead320 (Equation Read)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open I72.List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)

inductive PositiveShapeWire427 where
  | scalar (leafRow : Nat)
  | nested (innerRow : Nat) (innerEmptyRow : Nat) (binderEscape innerTailEscape : ExactEscapeWire)

structure PositiveHeadWire427 where
  ordinal : Nat
  outerRow : Nat
  outerEmptyRow : Nat
  rootEscape : ExactEscapeWire
  fieldEscape : ExactEscapeWire
  outerTailEscape : ExactEscapeWire
  payload : PositiveShapeWire427

def positiveCaptureOf427 {s q d} : SourceHead s q d → Option (Nat → Capture)
  | .ordered captures _ => some captures
  | _ => none

structure ReadPositiveHead427 (s : State) (q : Request) where
  ordinal : Nat
  decl : Declaration
  fromRegistry : (authoredRegistry s.current).declarations[ordinal]? = some decl
  visibleDecl : decl ∈ visible s q
  capture : Nat → Capture
  head : SourceHead s q decl
  sameCapture : positiveCaptureOf427 head = some capture
  safe (atlas : B6OccurrenceAtlas401 s) : ¬ I72.RootCycle ⟨s,atlas⟩ q

private theorem is_point427 (a : Capture) (n : Nat)
    (h : a.lower = n ∧ a.center = n ∧ a.upper = n) : a = point n := by
  cases a
  dsimp at h
  obtain ⟨rfl,rfl,rfl⟩ := h
  rfl

private theorem empty_read427 {s : GeneralDeclarativeHead320.State} {cap : Nat → Capture} {n : Nat}
    (h : ⟨n, .primitive .emptyRecord []⟩ ∈ s.equations) :
    Read s cap .actual n (.primitive .emptyRecord []) :=
  .primitive (n:=0) (fun i => i.elim0) (fun i => i.elim0) h (fun i => i.elim0)

private theorem scalar_read427 {s : GeneralDeclarativeHead320.State} {cap : Nat → Capture} {n : Nat}
    (h : ⟨n, .primitive (.scalar .int) []⟩ ∈ s.equations) :
    Read s cap .actual n (.primitive (.scalar .int) []) :=
  .primitive (n:=0) (fun i => i.elim0) (fun i => i.elim0) h (fun i => i.elim0)

private def event_head427 {s : State} {q : Request} {d : Declaration} {root : Nat}
    (cap : Nat → Capture) (p : Pattern) (code : Expr)
    (arr : q.demand.arguments = [point root]) (head : d.head = [p])
    (comp : translateWhere427 s p = some code) (read : Read s.current.ordinary cap .actual root code) :
    SourceHead s q d := by
  refine .ordered cap ?_
  rw [arr,head]
  exact .cons (.ordinary ⟨⟨.refl _,.refl _⟩,code,comp,.direct (.structural read)⟩) .nil

private theorem event_head_capture427 {s : State} {q : Request} {d : Declaration} {root : Nat}
    (cap : Nat → Capture) (p : Pattern) (code : Expr)
    (arr : q.demand.arguments = [point root]) (head : d.head = [p])
    (comp : translateWhere427 s p = some code) (read : Read s.current.ordinary cap .actual root code) :
    positiveCaptureOf427 (event_head427 cap p code arr head comp read) = some cap := rfl

private theorem rawRoot427 {s : State} {q : Request} {n : Nat}
    (arr : q.demand.arguments = [point n]) {w : ExactEscapeWire}
    (ok : checkExactEscape s.current.ordinary n w = true) :
    ∀ atlas : B6OccurrenceAtlas401 s, ¬ I72.RootCycle ⟨s,atlas⟩ q := by
  rintro atlas ⟨c,mem,cycle⟩
  change c ∈ q.demand.arguments at mem
  rw [arr] at mem
  cases List.mem_singleton.mp mem
  exact exact_escape_refutes_raw_root_K2410 ok cycle

/-- Read the exact original point, candidate ordinal, normalized
record equations and visible authored head. The optional nested wire
gives only row addresses and finite raw-graph ranks; the binder ID is
read from the declaration and its actual captured point from the
inner record's original field. No head/capture/acceptance is supplied. -/
def readPositiveHead427 (s : State) (q : Request) (w : PositiveHeadWire427) :
    Option (ReadPositiveHead427 s q) := do
  match hd : (authoredRegistry s.current).declarations[w.ordinal]? with
  | none => none
  | some d =>
    if vis : d ∈ visible s q then
      match arg : q.demand.arguments, dh : d.head with
      | [a], [p] =>
        match rr : s.current.ordinary.equations[w.outerRow]? with
        | some ⟨r,.record outer (.variable field) (.variable tail)⟩ =>
          match er : s.current.ordinary.equations[w.outerEmptyRow]? with
          | some ⟨empty,.primitive .emptyRecord []⟩ =>
            if tailEq : empty = tail then
             if pointEq : a.lower = r ∧ a.center = r ∧ a.upper = r then
              if rootSafe : checkExactEscape s.current.ordinary r w.rootEscape = true then
               if checkExactEscape s.current.ordinary field w.fieldEscape &&
                   checkExactEscape s.current.ordinary tail w.outerTailEscape then
                let args : q.demand.arguments = [point r] :=
                  arg.trans (congrArg (fun x => [x]) (is_point427 a r pointEq))
                let original := rawRoot427 args rootSafe
                have outerMem := List.mem_of_getElem? rr
                have emptyMem : ⟨tail,.primitive .emptyRecord []⟩ ∈ s.current.ordinary.equations :=
                  tailEq ▸ List.mem_of_getElem? er
                match comp : translateWhere427 s p with
                | none => none
                | some compiled =>
                  match w.payload with
                  | .scalar leafRow =>
                    match sr : s.current.ordinary.equations[leafRow]? with
                    | some ⟨found,.primitive (.scalar .int) []⟩ =>
                      if fieldEq : found = field then
                        let cap := fun (_ : Nat) => point 0
                        let code : Expr :=
                          .record outer (.primitive (.scalar .int) []) (.primitive .emptyRecord [])
                        if exact : eqExpr compiled code = true then
                          let translated := comp.trans (congrArg some ((eq_expr ..).mp exact))
                          let fieldMem : ⟨field,.primitive (.scalar .int) []⟩ ∈ s.current.ordinary.equations :=
                            fieldEq ▸ List.mem_of_getElem? sr
                          let proof : Read s.current.ordinary cap .actual r code :=
                            .record outerMem (scalar_read427 fieldMem) (empty_read427 emptyMem)
                          pure ⟨w.ordinal,d,hd,vis,cap,event_head427 cap p code args dh translated proof,
                            event_head_capture427 cap p code args dh translated proof,original⟩
                        else none
                      else none
                    | _ => none
                  | .nested innerRow innerEmptyRow escape tailEscape =>
                    match compiled with
                    | .record _ (.record _ (.variable binder) _) _ =>
                      match ir : s.current.ordinary.equations[innerRow]?,
                          ie : s.current.ordinary.equations[innerEmptyRow]? with
                      | some ⟨inRoot,.record inner (.variable captured) (.variable inTail)⟩,
                        some ⟨inEmpty,.primitive .emptyRecord []⟩ =>
                        if sites : inRoot = field ∧ inEmpty = inTail then
                         if checkExactEscape s.current.ordinary captured escape &&
                            checkExactEscape s.current.ordinary inTail tailEscape then
                          let cap := fun n => if n = binder then point captured else point 0
                          let code : Expr := .record outer
                            (.record inner (.variable binder) (.primitive .emptyRecord []))
                            (.primitive .emptyRecord [])
                          if exact : eqExpr compiled code = true then
                            let translated := comp.trans (congrArg some ((eq_expr ..).mp exact))
                            let inMem : ⟨field,.record inner (.variable captured) (.variable inTail)⟩ ∈
                                s.current.ordinary.equations := sites.1 ▸ List.mem_of_getElem? ir
                            let inEmptyMem : ⟨inTail,.primitive .emptyRecord []⟩ ∈ s.current.ordinary.equations :=
                              sites.2 ▸ List.mem_of_getElem? ie
                            have bound : Bound s.current.ordinary.normal captured
                                (GeneralDeclarativeHead320.byMode (cap binder) .actual) := by
                              simpa [cap,GeneralDeclarativeHead320.byMode,point] using
                                (Bound.refl captured : Bound s.current.ordinary.normal captured captured)
                            have back : Bound s.current.ordinary.normal
                                (GeneralDeclarativeHead320.byMode (cap binder) .actual) captured := by
                              simpa [cap,GeneralDeclarativeHead320.byMode,point] using
                                (Bound.refl captured : Bound s.current.ordinary.normal captured captured)
                            let proof : Read s.current.ordinary cap .actual r code :=
                              .record outerMem (.record inMem (.capture bound back) (empty_read427 inEmptyMem))
                                (empty_read427 emptyMem)
                            pure ⟨w.ordinal,d,hd,vis,cap,event_head427 cap p code args dh translated proof,
                              event_head_capture427 cap p code args dh translated proof,original⟩
                          else none
                         else none
                        else none
                      | _,_ => none
                    | _ => none
               else none
              else none
             else none
            else none
          | _ => none
        | _ => none
      | _,_ => none
    else none

end Yulang.GeneralDeclarativeI65.StructuralWhere427
