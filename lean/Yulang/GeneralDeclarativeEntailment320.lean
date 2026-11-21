import Yulang.GeneralDeclarativeNodeFacts320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
set_option maxHeartbeats 3800000
namespace Yulang.GeneralDeclarativeEntailment320
open GeneralDeclarations (Declaration Registry Checked)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatExpressions (value)
open GeneralDeclarativeHead320 (State Equation Models environment)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeAssembly320 (Meaning Node)
open GeneralDeclarativeNodeFacts320 (nodeFacts batch_node_sound)

def Holds (m : Assignment) (row : Equation) : Prop :=
  Equivalent (m row.left).1 (value (environment m) .actual row.right)

/-- Consequence of ordinary constraints, not a local typing or dictionary
predicate. It does not choose a model or postulate that a demand resolves. -/
def Entails (s : State) (row : Equation) : Prop :=
  ∀ m, Models s m → Holds m row

def appendFacts (s : State) (rows : List Equation) : State :=
  ⟨s.normal,s.equations ++ rows⟩

theorem literal {s : State} {row : Equation} (found : row ∈ s.equations) : Entails s row :=
  fun _m valid => valid.2 row found

theorem model_append {s : State} {rows : List Equation} (m : Assignment) :
    Models (appendFacts s rows) m ↔ Models s m ∧ ∀ row ∈ rows, Holds m row := by
  constructor
  · intro valid
    exact ⟨⟨valid.1,fun row present => valid.2 row (List.mem_append_left _ present)⟩,
      fun row present => valid.2 row (List.mem_append_right _ present)⟩
  · rintro ⟨valid,extra⟩
    refine ⟨valid.1,?_⟩
    intro row member
    exact (List.mem_append.mp member).elim (valid.2 row) (extra row)

theorem conservative_append {s : State} {rows : List Equation}
    (settled : ∀ row ∈ rows, Entails s row) (m : Assignment) :
    Models (appendFacts s rows) m ↔ Models s m :=
  (model_append m).trans ⟨And.left,fun valid => ⟨valid,fun row member => settled row member m valid⟩⟩

theorem entailed_batch_sound {s r interp capture decl d kids facts}
    (checked : Checked r) (visible : decl ∈ r.declarations)
    (captures : ∀ n ∈ decl.inputNames, Bounds s (capture n))
    (bounds : ∀ arg ∈ d.arguments, Bounds s arg)
    (generated : nodeFacts r interp capture decl d kids = some facts)
    (settled : ∀ row ∈ facts, Entails s row)
    (m : Assignment) (valid : Models s m) : Meaning r interp m d decl capture kids := by
  have extended : Models (appendFacts s facts) m := (conservative_append settled m).mpr valid
  exact batch_node_sound (s := appendFacts s facts) checked visible captures bounds generated
    (fun _ member => List.mem_append_right _ member) m extended

/-- The actual compiler-produced predicate: it only requires the logical
capture assignment, its ordinary bounds and the finite ordinary conclusions.
In particular, there is no independently asserted per-model node certificate. -/
def BatchRecipe (s : State) (r : Registry) (interp : Interpretation) (d : Demand)
    (key : Nat) (kids : List Demand) : Prop :=
  ∃ decl capture facts, decl.id = key ∧ decl ∈ r.declarations ∧
    (∀ n ∈ decl.inputNames, Bounds s (capture n)) ∧ (∀ arg ∈ d.arguments, Bounds s arg) ∧
    nodeFacts r interp capture decl d kids = some facts ∧
    (∀ row ∈ facts, Entails s row)

theorem batch_recipe_sound {s r interp d key kids} (checked : Checked r)
    (recipe : BatchRecipe s r interp d key kids) (m : Assignment) (valid : Models s m) :
    Node r interp m d key kids := by
  obtain ⟨decl,capture,_,key_eq,visible,bounds,args,generated,settled⟩ := recipe
  exact ⟨decl,capture,key_eq,entailed_batch_sound checked visible bounds args generated settled m valid⟩

end Yulang.GeneralDeclarativeEntailment320
