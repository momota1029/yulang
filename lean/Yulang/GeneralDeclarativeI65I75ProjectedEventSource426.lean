import Yulang.GeneralDeclarativeI65I75ProjectedCoreRetention426
import Yulang.GeneralDeclarativeK2Alias321

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDeclarativeI65.ProjectedCore425
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration Checked)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open CommonRoleOutermostResolver (Dictionary)
open CommonNominalFullCarrier (Ty Equivalent)
open GeneralDeclarativeRecordChannel330 (project)

/-- A record endpoint head at the original arguments and literal
declaration, with the payload of the I-75 head constructor. The
declaration ordinal is stored separately on the actual B6 output. -/
structure EventHead426 (s : State) (q : Request) (row : Declaration) where
  arg : Capture
  request : q.demand.arguments = [arg]
  label : Nat
  fieldBinder : Nat
  tailBinder : Nat
  distinct : fieldBinder ≠ tailBinder
  pattern : row.head = [.record label (.var fieldBinder) (.var tailBinder)]
  endpoints : EndpointHead423.Inputs s arg label

def Output.headAtOccurrence426 {s atlas q i} (o : Output s atlas q i) :
    EventHead426 s q o.row :=
  ⟨o.arg,o.request,o.label,o.fieldBinder,o.tailBinder,o.distinct,o.pattern,o.head⟩

/-- This head's payload is tied to the *same* original authored lower
and upper observations as the output, not merely to a declaration id
or to the same numerical label/center. -/
theorem shared_head_keeps_original_endpoints_and_binders426 {s atlas q i}
    (o : Output s atlas q i) :
    let h := o.headAtOccurrence426
    h.endpoints.lower.origin = o.head.lower.origin ∧
    h.endpoints.upper.origin = o.head.upper.origin ∧
    h.fieldBinder = o.fieldBinder ∧ h.tailBinder = o.tailBinder := by
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Raw root K2 exactly as in I72. No removal of incomplete output,
no visited positions manufactured from the endpoint interval. -/
def OriginalRootCycle426 (s : State) (q : Request) : Prop :=
  ∃ a ∈ q.demand.arguments,
    GeneralDeclarativeK2Alias321.AliasCycle s.current.ordinary
      (GeneralDeclarativeGraphRows321.observed s.current.ordinary) a.lower

/-- Independently positive authored leaf fragment. Each field is taken
from genuinely visible original source, not a reported result,
model-valued witness, or checker. This distinguishes an endpoint head
from the old named pre-output table. -/
structure OriginalProjectedLeaf426 (s : State) (atlas : B6OccurrenceAtlas401 s)
    (q : Request) where
  outIndex : Fin q.demand.outputs.length
  onlyOutput : q.demand.outputs.length = 1
  out : Output s atlas q outIndex
  checked : Checked (authoredRegistry s.current)
  distinctEnds : out.arg.lower ≠ out.arg.upper
  noWhere : out.row.requirements = []
  noOutBinders : out.row.outputBinders = []
  singleAssoc : out.row.associated = [out.assoc]
  rootSafe : ¬ OriginalRootCycle426 s q

def OriginalProjectedLeaf426.dictionary {s atlas q} (e : OriginalProjectedLeaf426 s atlas q) :
    Dictionary := .node e.out.row.id []

def OriginalProjectedLeaf426.head {s atlas q} (e : OriginalProjectedLeaf426 s atlas q) :
    EventHead426 s q e.out.row := e.out.headAtOccurrence426

theorem projected_leaf_always_uses_exact_only_output426 {s atlas q}
    (e : OriginalProjectedLeaf426 s atlas q) (i : Fin q.demand.outputs.length) :
    i = e.outIndex := by
  apply Fin.eq_of_val_eq
  have one := i.isLt
  have two := e.outIndex.isLt
  have len := e.onlyOutput
  omega

theorem raw_cycle_vetoes_projected_leaf426 {s atlas q}
    (raw : OriginalRootCycle426 s q) : ¬ Nonempty (OriginalProjectedLeaf426 s atlas q) :=
  fun ⟨leaf⟩ => leaf.rootSafe raw

/-- Same-model meaning for the exact leaf before canonical migration.
Witness-only checking must still reflect this source rule in the
public classifier. This theorem does not claim that migration. -/
theorem one_projected_leaf_keeps_output_at_original_target426 {s atlas q}
    (leaf : OriginalProjectedLeaf426 s atlas q) (retain : RequiredRetention426 leaf.out)
    (m : Model) (fit : Fits s m) :
    EndpointHead423.Meaning leaf.head.endpoints m ∧
    (∀ i : Fin q.demand.outputs.length, ∃ v : Ty,
      project leaf.head.label false [] (m.assignment leaf.head.arg.center).1 = some v ∧
      leaf.out.valueAt m = some (q.occurrence,leaf.out.ordinal,i.val,q.demand.outputs[i].target,v) ∧
      Equivalent (m.assignment q.demand.outputs[i].target).1 v) := by
  obtain ⟨head,v,value,source,fixed⟩ :=
    original_core_and_required_rows_produce_same_model_meaning426 leaf.out retain m fit
  refine ⟨head,fun i => ?_⟩
  cases projected_leaf_always_uses_exact_only_output426 leaf i
  exact ⟨v,value,source,fixed⟩

end Yulang.GeneralDeclarativeI65.ProjectedCore425
