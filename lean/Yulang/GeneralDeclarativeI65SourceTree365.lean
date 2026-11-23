import Yulang.GeneralDeclarativeI65SourceNode365

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open CommonRoleOutermostResolver (Dictionary)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarations (Declaration)

structure FixedReceipt where
  occurrence : List Nat
  rows : List Equation

def captureReceipt {s : State} {q : Request} {row : Declaration} {kids : List Request}
    (n : SourceNode s q row kids) : FixedReceipt :=
  ⟨q.occurrence,n.actual.body.finished.fixed⟩

mutual
inductive SourceTree (s : State) : Request → Dictionary → List FixedReceipt → Prop where
  | node (statement : SourceNode s q row kids) :
      SourceForest s kids dictionaries later →
      SourceTree s q (.node row.id dictionaries) (captureReceipt statement :: later)

inductive SourceForest (s : State) : List Request → List Dictionary → List FixedReceipt → Prop where
  | nil : SourceForest s [] [] []
  | cons :
      SourceTree s here d current → SourceForest s more ds after →
      SourceForest s (here::more) (d::ds) (current ++ after)
end

mutual
inductive TreeEvidence (s : State) (m : Model) : Request → Dictionary → List FixedReceipt → Prop where
  | node (statement : SourceNode s q row kids) :
      SourceNodeMeaning statement m →
      ForestEvidence s m kids dictionaries later →
      TreeEvidence s m q (.node row.id dictionaries) (captureReceipt statement :: later)

inductive ForestEvidence (s : State) (m : Model) : List Request → List Dictionary → List FixedReceipt → Prop where
  | nil : ForestEvidence s m [] [] []
  | cons :
      TreeEvidence s m here d current → ForestEvidence s m more ds after →
      ForestEvidence s m (here::more) (d::ds) (current ++ after)
end

/-- Mathematical assembly of an already source-justified ordered tree.
The dictionary and the complete literal receipt list remain indices.
This does not decide which source declarations are uniquely applicable. -/
theorem source_tree_sound {s : State} {q : Request} {d : Dictionary} {rows : List FixedReceipt}
    (source : SourceTree s q d rows) (m : Model) (fit : Fits s m) : TreeEvidence s m q d rows := by
  exact SourceTree.rec
    (motive_1 := fun q d r _ => TreeEvidence s m q d r)
    (motive_2 := fun qs ds rs _ => ForestEvidence s m qs ds rs)
    (fun n _ ih => .node n (source_node_sound n m fit) ih)
    .nil
    (fun _ _ first rest => .cons first rest)
    source

/-- No chosen model or replacement receipt is taken at a node.
Every occurrence's already indexed fixed equations hold in this one
fitting model, in the same depth-first order. -/
theorem every_fixed_row_comes_from_the_same_model {s : State} {m : Model} {q : Request}
    {d : Dictionary} {rows : List FixedReceipt} (e : TreeEvidence s m q d rows) :
    ∀ r ∈ rows, ∀ eq ∈ r.rows, Holds m.assignment eq := by
  exact TreeEvidence.rec
    (motive_1 := fun _ _ rows _ => ∀ r ∈ rows, ∀ eq ∈ r.rows, Holds m.assignment eq)
    (motive_2 := fun _ _ rows _ => ∀ r ∈ rows, ∀ eq ∈ r.rows, Holds m.assignment eq)
    (fun source meaning _ after r seen eq row => by
      rcases List.mem_cons.mp seen with same | rest
      · subst r
        exact meaning.allFixed eq row
      · exact after r rest eq row)
    (fun _ no => by cases no)
    (fun _ _ first after r seen eq row => by
      rcases List.mem_append.mp seen with l | t
      · exact first r l eq row
      · exact after r t eq row)
    e

end Yulang.GeneralDeclarativeI65
