import Yulang.GeneralRebaseHeadSupport263
import Yulang.GeneralNominalVersionedMixedAncestry237
import Yulang.GeneralNominalVersionedCurrentProjection237

namespace Yulang.GeneralRebaseRegisteredPlan263
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234

/-- Metadata retained by actual versioned plan installations. It intentionally
refers to state.plans, not the separate legacy plan journal. -/
structure Metadata (registry : Registry) (context : GeneralNominalCandidates.Context) (plan : Plan roles) : Prop where
 registry_eq : plan.packet.registry = registry
 seed : plan.packet.context.state.seed = context.state.seed
 constructors : plan.packet.context.state.constructors = context.state.constructors
 interpretation : plan.packet.context.interpretation = context.interpretation
 visible : plan.packet.declaration ∈ registry.declarations
 finished : GeneralNominalRecursiveInspection.Finished (GeneralNominalQueryProvenance183.headInspection plan)

theorem metadata (registry : Registry) (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
 (state : State roles) (path : B4Target.Steps (Step registry root) (initial context root) state) :
 ∀ plan ∈ state.plans, Metadata registry context plan := by
 induction path with
 | refl => intro plan member; cases member
 | @tail before after path step ih =>
   obtain ⟨focus,_,action⟩ := step
   cases action with
   | administrative action =>
     cases action with
     | enqueue | refresh | equate | reobserve => exact ih
   | refresh | merge => exact ih
   | install effect enabled novel =>
     intro plan member
     rcases List.mem_cons.mp member with rfl | old
     · have frame := GeneralNominalVersionedMixedAncestry237.frame enabled
       have config := GeneralNominalVersionedMixedAncestry237.configuration_trace path
       refine ⟨frame.registry_eq,?_,?_,?_,frame.visible,
         GeneralNominalVersionedCurrentProjection237.frame_finished effect.plan frame⟩
       · rw [frame.context_eq]; exact config.1
       · rw [frame.context_eq]; exact config.2.1
       · rw [frame.context_eq]; exact config.2.2
     · exact ih plan old

/-- Existing Models contains every registered versioned packet's Inputs. -/
theorem inputs (state : State roles) (assignment : GeneralNominalCommonBridge.Assignment)
 (valid : Models state assignment) (plan : Plan roles) (member : plan ∈ state.plans) :
 GeneralNominalVersionedPlans231.Inputs plan assignment :=
 (plan_models valid member).2.1


/-- Same owner in a checked registry fixes the entire declaration, not merely
its identifier. The two snapshots can be independently reachable. -/
theorem layout (registry : Registry) (checked : Checked registry)
 (context : GeneralNominalCandidates.Context) (first last : Plan roles)
 (one : Metadata registry context first) (two : Metadata registry context last)
 (key : first.packet.declaration.id = last.packet.declaration.id) :
 GeneralRebasePlanSemantic262.Layout first last := by
 refine ⟨GeneralDictionaryEmissionPlans.declaration_key_unique registry checked _ _ one.visible two.visible key,?_,?_⟩
 · rw [one.registry_eq,two.registry_eq]
 · exact one.interpretation.trans two.interpretation.symm

/-- Registered actual plans supply Finished, head satisfaction, configuration
and allocation identity. Only positional semantic center agreement remains an
extra semantic premise. No output-effect equivalence is assumed. -/
theorem compatible (registry : Registry) (checked : Checked registry)
 (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
 (before after : State roles)
 (pathOne : B4Target.Steps (Step registry root) (initial context root) before)
 (pathTwo : B4Target.Steps (Step registry root) (initial context root) after)
 (first last : Plan roles) (memberOne : first ∈ before.plans) (memberTwo : last ∈ after.plans)
 (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
 (key : first.packet.declaration.id = last.packet.declaration.id)
 (assignment : GeneralNominalCommonBridge.Assignment)
 (validOne : Models before assignment) (validTwo : Models after assignment)
 (centers : ∀ index : Nat, CommonNominalFullCarrier.Equivalent
   (assignment ((List.ofFn first.input.center)[index]?.getD 0)).1
   (assignment ((List.ofFn last.input.center)[index]?.getD 0)).1) :
 GeneralRebaseNormalizedBody263.Compatible first last assignment := by
 have one := metadata registry context root before pathOne first memberOne
 have two := metadata registry context root after pathTwo last memberTwo
 exact GeneralRebaseHeadSupport263.from_inputs first last assignment
   (layout registry checked context first last one two key)
   (one.constructors.trans two.constructors.symm)
   (one.seed.trans two.seed.symm) identity centers
   (inputs before assignment validOne first memberOne)
   (inputs after assignment validTwo last memberTwo) one.finished



/-- Source-boundary specialization. The two paths share the same actual source
start; no execution from the first snapshot to the second is required. -/
theorem source_compatible (registry : Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : Occurrence roles) (start before after : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start)
 (pathOne : B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root) start before)
 (pathTwo : B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root) start after)
 (first last : Plan roles) (memberOne : first ∈ before.plans) (memberTwo : last ∈ after.plans)
 (owner : (first.packet.site.occurrence.identity,first.packet.declaration.id) =
          (last.packet.site.occurrence.identity,last.packet.declaration.id))
 (assignment : GeneralNominalCommonBridge.Assignment)
 (validOne : Models before assignment) (validTwo : Models after assignment)
 (centers : ∀ index : Nat, CommonNominalFullCarrier.Equivalent
   (assignment ((List.ofFn first.input.center)[index]?.getD 0)).1
   (assignment ((List.ofFn last.input.center)[index]?.getD 0)).1) :
 GeneralRebaseNormalizedBody263.Compatible first last assignment := by
 have compiled := GeneralNominalVersionedMixedSourceBoundary234.initial_compiled source
 obtain ⟨legacy,⟨context,labels,formed,point,ground,coverage,rfl⟩,rfl⟩ := compiled
 exact compatible _ (GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked).2
   context root before after pathOne pathTwo first last memberOne memberTwo
   (congrArg Prod.fst owner) (congrArg Prod.snd owner) assignment validOne validTwo centers


/-- Pure structural layout for same-owner actual registered source plans.
There are no Models or semantic center premises. -/
theorem source_layout (registry : Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : Occurrence roles) (start before after : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start)
 (pathOne : B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root) start before)
 (pathTwo : B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root) start after)
 (first last : Plan roles) (memberOne : first ∈ before.plans) (memberTwo : last ∈ after.plans)
 (owner : (first.packet.site.occurrence.identity,first.packet.declaration.id) =
          (last.packet.site.occurrence.identity,last.packet.declaration.id)) :
 GeneralRebasePlanSemantic262.Layout first last := by
 have compiled := GeneralNominalVersionedMixedSourceBoundary234.initial_compiled source
 obtain ⟨legacy,⟨context,labels,formed,point,ground,coverage,rfl⟩,rfl⟩ := compiled
 exact layout _ (GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked).2 context first last
   (metadata _ context root before pathOne first memberOne)
   (metadata _ context root after pathTwo last memberTwo) (congrArg Prod.snd owner)
end Yulang.GeneralRebaseRegisteredPlan263
