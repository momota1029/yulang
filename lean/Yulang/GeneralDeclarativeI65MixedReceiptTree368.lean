import Yulang.GeneralDeclarativeI65UnionReceipts368

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open CommonRoleOutermostResolver (Dictionary)
open GeneralDeclarativeWitnessTypedOutput354 (Write ordinary)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeWitnessDeclaredState357 (Value)
open GeneralDeclarations (Declaration)

structure OrderedWriteReceipt where
  occurrence : List Nat
  writes : List Write

structure ReceiptNode (s : State) (q : Request) (row : Declaration) (kids : List Request) where
  picked : AuthoredCandidate s q row
  body : SourceReceipt picked kids

def ReceiptNode.report {s : State} {q : Request} {row : Declaration} {kids : List Request}
    (node : ReceiptNode s q row kids) : OrderedWriteReceipt :=
  ⟨q.occurrence,node.body.trace⟩

mutual
inductive ReceiptTree (s : State) : Request → Dictionary → List OrderedWriteReceipt → Prop where
  | node (body : ReceiptNode s q row kids) :
      ReceiptForest s kids dicts rest →
      ReceiptTree s q (.node row.id dicts) (body.report :: rest)

inductive ReceiptForest (s : State) : List Request → List Dictionary → List OrderedWriteReceipt → Prop where
  | nil : ReceiptForest s [] [] []
  | cons : ReceiptTree s first d written →
      ReceiptForest s after ds remaining →
      ReceiptForest s (first::after) (d::ds) (written ++ remaining)
end

mutual
inductive ReceiptTreeMeaning (s : State) (m : Model) : Request → Dictionary → List OrderedWriteReceipt → Prop where
  | node (body : ReceiptNode s q row kids) :
      ReceiptMeaning body.body m → ReceiptForestMeaning s m kids dicts rest →
      ReceiptTreeMeaning s m q (.node row.id dicts) (body.report :: rest)

inductive ReceiptForestMeaning (s : State) (m : Model) : List Request → List Dictionary →
    List OrderedWriteReceipt → Prop where
  | nil : ReceiptForestMeaning s m [] [] []
  | cons : ReceiptTreeMeaning s m first d written →
      ReceiptForestMeaning s m after ds remaining →
      ReceiptForestMeaning s m (first::after) (d::ds) (written ++ remaining)
end

/-- Literal heterogeneous receipts and their exact depth-first output
order survive the source-to-meaning fold, in one model. The remaining
source-frontier producer is not assumed to exist for all selections. -/
theorem emitted_receipt_tree_sound {s : State} {q : Request} {d : Dictionary}
    {written : List OrderedWriteReceipt} (tree : ReceiptTree s q d written)
    (m : Model) (fit : Fits s m) : ReceiptTreeMeaning s m q d written := by
  exact ReceiptTree.rec
    (motive_1 := fun root dict rows _ => ReceiptTreeMeaning s m root dict rows)
    (motive_2 := fun roots dicts rows _ => ReceiptForestMeaning s m roots dicts rows)
    (fun n _ ih => .node n (source_receipt_in_one_model n.body m fit) ih)
    .nil
    (fun _ _ now later => .cons now later)
    tree

structure WrittenIn (m : Model) (report : OrderedWriteReceipt) : Prop where
  ordinary : ∀ e ∈ ordinary report.writes, Holds m.assignment e
  typed : ∀ row, .typed row ∈ report.writes →
    ∃ v : Value, m.authoredValues row.root = some v ∧ v.tag = row.tag ∧ v.name = row.box ∧
      v.arguments = [.inl (m.assignment row.valueName).1]

theorem every_written_receipt_in_one_model {s : State} {m : Model} {q : Request}
    {d : Dictionary} {written : List OrderedWriteReceipt}
    (evidence : ReceiptTreeMeaning s m q d written) :
    ∀ w ∈ written, WrittenIn m w := by
  exact ReceiptTreeMeaning.rec
    (motive_1 := fun _ _ rows _ => ∀ w ∈ rows,WrittenIn m w)
    (motive_2 := fun _ _ rows _ => ∀ w ∈ rows,WrittenIn m w)
    (fun n known _ next w seen => by
      rcases List.mem_cons.mp seen with here|later
      · subst w
        exact ⟨known.equations,known.nominal⟩
      · exact next w later)
    (fun _ no => by cases no)
    (fun _ _ left right w seen => by
      rcases List.mem_append.mp seen with before|after
      · exact left w before
      · exact right w after)
    evidence

end Yulang.GeneralDeclarativeI65
