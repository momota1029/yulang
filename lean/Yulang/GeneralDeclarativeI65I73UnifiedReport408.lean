import Yulang.GeneralDeclarativeI65I73UnifiedCheck408

namespace Yulang.GeneralDeclarativeI65.I72.Check408
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Summarizes)
open CommonDeclaredNominalInspection (Kind Parameter)
open CommonDeclaredNominalVariance (Variance)
open GeneralDeclarativeWhere319 (Capture)

/-- A serialization of the *logical typed tree itself*, not an Expr
code or model denotation. Type tags and argument tags are separate
constructors of the encoding; named leaves keep all three interval
names and their literal binder. -/
def kindCode : Kind → Nat
  | .value => 0
  | .row => 1

def varianceCode : Variance → Nat
  | .covariant => 0
  | .contravariant => 1
  | .invariant => 2
  | .unused => 3

def baseCode : Inference.Base → Nat
  | .int => 0
  | .str => 1
  | .bool => 2
  | .unit => 3

def nameTriple (n : Nat) (cap : Capture) : List Nat := [n,cap.lower,cap.center,cap.upper]

def paramCode (p : Parameter) : List Nat := [kindCode p.kind,varianceCode p.variance]

mutual
def encodeRhs {s slots c pat} : NamedMixedTree401 s slots c pat → TypeWire
  | .binder n cap => .node 0 (nameTriple n cap.val) []
  | .record l a b => .node 1 [l] [encodeRhs a,encodeRhs b]
  | .variant l a => .node 2 [l] [encodeRhs a]
  | .join a b => .node 3 [] [encodeRhs a,encodeRhs b]
  | .declaredApp n _ _ _ args => .node 4 [n] (encodeArgs args)
  | .scalar n base _ _ => .node 5 [n,baseCode base] []
  | .emptyRecord n _ _ => .node 6 [n] []
  | .exactEmpty n _ _ => .node 7 [n] []
  | .pair n _ _ a b => .node 8 [n] [encodeRhs a,encodeRhs b]

def encodeArg {s slots c p pat} : MixedArg401 s (NamedSlot401 slots) c p pat → TypeWire
  | .valuePoint n _ _ cap => .node 9 (paramCode p ++ nameTriple n cap.val) []
  | .valueInterval n _ _ cap => .node 10 (paramCode p ++ nameTriple n cap.val) []
  | .rowPoint n _ _ cap => .node 11 (paramCode p ++ nameTriple n cap.val) []
  | .rowInterval n _ _ cap => .node 12 (paramCode p ++ nameTriple n cap.val) []
  | .valueTree _ _ tree => .node 13 (paramCode p) [encodeRhs tree]

def encodeArgs {s slots c ps pats} : MixedArgs401 s (NamedSlot401 slots) c ps pats → List TypeWire
  | .nil => []
  | .cons a b => encodeArg a :: encodeArgs b
end

def encodedEventWrites {s q} (event : Event s q) : List Write :=
  List.ofFn fun i : Fin q.demand.outputs.length =>
    let out := event.outputs i
    ⟨q.occurrence,event.frame.ordinal,i.val,q.demand.outputs[i],out.body,encodeRhs out.rhs⟩

/-- Writes belong to actual events in the diagnostic tree and retain
their original order. Support proofs certify input readiness; they
are not children or repeated writes in the reported diagnostic. -/
noncomputable def traceWrites {s q t e} (trace : SourceTrace R0 s q t e) : List Write :=
  SourceTrace.rec (R := R0) (s := s)
    (motive_1 := fun _ _ _ _ => List Write)
    (motive_2 := fun _ _ _ => List Write)
    (motive_3 := fun _ _ => Unit)
    (fun _ => []) (fun _ _ _ _ _ => [])
    (fun event _ _ _ _ _ kids => encodedEventWrites event ++ kids)
    [] (fun _ _ a b => a ++ b)
    () (fun _ _ _ _ _ _ => ()) trace

noncomputable def forestWrites {s qs ts} (forest : WhereForest R0 s qs ts) : List Write :=
  WhereForest.rec (R := R0) (s := s)
    (motive_1 := fun _ _ _ _ => List Write)
    (motive_2 := fun _ _ _ => List Write)
    (motive_3 := fun _ _ => Unit)
    (fun _ => []) (fun _ _ _ _ _ => [])
    (fun event _ _ _ _ _ kids => encodedEventWrites event ++ kids)
    [] (fun _ _ a b => a ++ b)
    () (fun _ _ _ _ _ _ => ()) forest

theorem empty_diag_forest_has_no_writes408 {s qs} (kids : WhereForest R0 s qs []) :
    forestWrites kids = [] := by cases kids; rfl

theorem trace_writes_keep_tree_transport408 {s q a b e} (eq : a = b)
    (trace : SourceTrace R0 s q a e) : traceWrites (eq ▸ trace) = traceWrites trace := by
  cases eq
  rfl

def ClassifiedAs (s : I72.State) (q : I72.Request) (r : Result) : Prop :=
  ∃ e, ∃ actual : SourceTrace R0 s q r.tree e,
    Summarizes r.tree r.verdict ∧ r.writes = traceWrites actual

theorem exact_report_is_R0_classification408 {s q r} (report : ClassifiedAs s q r) :
    Classifies R0 s q r.verdict := by
  obtain ⟨e,actual,summary,_⟩ := report
  exact ⟨r.tree,e,⟨actual⟩,summary⟩

end Yulang.GeneralDeclarativeI65.I72.Check408
