import Yulang.GeneralNominalOutputMenu254
import Yulang.GeneralNominalExprDepth253
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRawOutputBudget254
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralDictionaryAssociatedProvenance (Body Supplies)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translateDefault)
open GeneralNominalExprDepth253 (rawDepth materializedDepth)
variable {roles : Roles.RoleDecls} {state : State roles}

/-- Exact raw compileBody syntax, without normalizing an explicit RHS. -/
def compile (registry : Registry) (context : GeneralNominalCandidates.Context) : Body → Option Expr
 | .explicit equation => translate registry.constructors context.interpretation equation.rhs
 | .default _ _ term => translateDefault registry.constructors context.interpretation term

def templates (registry : Registry) (context : GeneralNominalCandidates.Context)
 (root : Occurrence roles) : List Expr :=
 (GeneralNominalOutputMenu254.bodies registry roles (GeneralNominalOutputMenu254.names registry root)).flatMap
   (fun body => (compile registry context body).toList)

def budget (registry : Registry) (context : GeneralNominalCandidates.Context)
 (root : Occurrence roles) : Nat :=
 GeneralNominalProducerOrder254.ceiling ((templates registry context root).map rawDepth)

/-- A reachable actual frame and output provenance suffice. No semantic model,
Evidence tree, or assumed finiteness of intermediate state is required. -/
theorem source_template
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key plan)
 (requested : output ∈ focus.demand.outputs)
 (supplied : Supplies roles plan.packet.declaration output.name body)
 (compiled : GeneralNominalCenteredHeadMatEffects.compileBody plan body = some expression) :
 expression ∈ templates registry context root := by
 have named := GeneralNominalOutputMenu254.source_names path plan.input frame.center_recorded output
   (by simpa only [plan.input_exact,frame.occurrence_eq] using requested)
 have present := GeneralNominalOutputMenu254.supplied_mem frame.visible named supplied
 have interpretation : state.core.erased.current.context.interpretation = context.interpretation :=
   (GeneralNominalVersionedMixedAncestry237.configuration_trace path).2.2
 have translated : compile registry context body = some expression := by
   cases body <;> simpa only [compile,GeneralNominalCenteredHeadMatEffects.compileBody,
     frame.registry_eq,frame.context_eq,interpretation] using compiled
 exact List.mem_flatMap.mpr ⟨body,present,by simp only [translated,Option.toList_some]; exact List.mem_singleton_self _⟩

theorem source_depth
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key plan)
 (requested : output ∈ focus.demand.outputs)
 (supplied : Supplies roles plan.packet.declaration output.name body)
 (compiled : GeneralNominalCenteredHeadMatEffects.compileBody plan body = some expression) :
 rawDepth expression ≤ budget registry context root :=
 GeneralNominalProducerOrder254.below_ceiling
   (List.mem_map.mpr ⟨expression,source_template path frame requested supplied compiled,rfl⟩)

/-- Name references may vary arbitrarily but are not expanded into meanings.
This is the template half only; no finite support pool is asserted. -/
theorem reference_depth
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key plan)
 (requested : output ∈ focus.demand.outputs)
 (supplied : Supplies roles plan.packet.declaration output.name body)
 (compiled : GeneralNominalCenteredHeadMatEffects.compileBody plan body = some expression)
 (names : GeneralNominalMaterialization.Mode → Nat → Nat) (mode : GeneralNominalMaterialization.Mode) :
 materializedDepth (GeneralNominalRebaseEffectView243.compile (fun mode name => .var (names mode name)) mode expression)
   ≤ budget registry context root := by
 rw [GeneralNominalExprDepth253.reference_depth]
 exact source_depth path frame requested supplied compiled
end Yulang.GeneralNominalRawOutputBudget254
