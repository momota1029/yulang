import Yulang.GeneralRebaseNormalizedFacts263
import Yulang.GeneralRebaseBinderShape262
import Yulang.GeneralNominalHeadSchemaSemantic186
import Yulang.GeneralNominalHeadSchemaNames186

namespace Yulang.GeneralRebaseHeadSupport263
open GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

/-- Source-origin agreement is exactly semantic type agreement at those names;
no equality of source identities or model values is required. -/
theorem source_same (assignment : Assignment) (first last : Nat)
 (same : Equivalent (assignment first).1 (assignment last).1) :
 GeneralNominalOriginTerms.Same assignment (.source first) (.source last) :=
 ⟨⟨_,.source _⟩,⟨_,.source _⟩,by intro a b one two; cases one; cases two; exact same⟩

/-- Actual head entries ignore versioned lower/upper aggregate allocation. -/
theorem head_iff (plan : Plan roles) (assignment : Assignment) :
 GeneralNominalVersionedPlans231.SchemaHolds plan plan.headSchema assignment ↔
 plan.SchemaHolds plan.headSchema assignment := by
 constructor
 · intro valid
   refine ⟨valid.1,?_⟩
   intro entry member
   have actual := GeneralNominalHeadSchemaNames186.head_actual plan entry member
   have found := valid.2 entry member
   simpa only [actual,ite_true,GeneralNominalVersionedFrame231.binder_eq] using found
 · intro valid
   refine ⟨valid.1,?_⟩
   intro entry member
   have actual := GeneralNominalHeadSchemaNames186.head_actual plan entry member
   have found := valid.2 entry member
   simpa only [actual,ite_true,GeneralNominalVersionedFrame231.binder_eq] using found

theorem input_binder (first last : Plan roles) (assignment : Assignment)
 (declaration : first.packet.declaration = last.packet.declaration)
 (constructors : first.packet.context.state.constructors = last.packet.context.state.constructors)
 (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
 (centers : ∀ index : Nat, Equivalent
   (assignment ((List.ofFn first.input.center)[index]?.getD 0)).1
   (assignment ((List.ofFn last.input.center)[index]?.getD 0)).1)
 (one : GeneralNominalVersionedPlans231.SchemaHolds first first.headSchema assignment)
 (two : GeneralNominalVersionedPlans231.SchemaHolds last last.headSchema assignment)
 (finished : GeneralNominalRecursiveInspection.Finished (GeneralNominalQueryProvenance183.headInspection first))
 (name : Nat) (member : name ∈ first.packet.declaration.inputNames) :
 Equivalent (assignment (first.binder name)).1 (assignment (last.binder name)).1 := by
 have same := GeneralNominalHeadSchemaSemantic186.binder_same first last declaration constructors interpretation
   (fun index => source_same assignment _ _ (centers index))
   ((head_iff first assignment).mp one) ((head_iff last assignment).mp two) finished name member
 exact same.2.2 _ _ (.source _) (.source _)

theorem output_binder (first last : Plan roles) (assignment : Assignment)
 (declaration : first.packet.declaration = last.packet.declaration)
 (seed : first.packet.context.state.seed = last.packet.context.state.seed)
 (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
 (name : Nat) (member : name ∈ first.packet.declaration.outputNames) :
 Equivalent (assignment (first.binder name)).1 (assignment (last.binder name)).1 := by
 have other : name ∈ last.packet.declaration.outputNames := declaration ▸ member
 simp only [Plan.binder,member,other,ite_true]
 rw [GeneralRebaseBinderShape262.outputs first last declaration seed identity name]
 exact GeneralDictionaryDefaultExpression209.equivalent_refl _

/-- Declaration.Scoped is already part of the actual checked packet. It
classifies normalized RHS support, not the names of a raw total expression. -/
theorem from_heads (first last : Plan roles) (assignment : Assignment)
 (layout : GeneralRebasePlanSemantic262.Layout first last)
 (constructors : first.packet.context.state.constructors = last.packet.context.state.constructors)
 (seed : first.packet.context.state.seed = last.packet.context.state.seed)
 (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
 (centers : ∀ index : Nat, Equivalent
   (assignment ((List.ofFn first.input.center)[index]?.getD 0)).1
   (assignment ((List.ofFn last.input.center)[index]?.getD 0)).1)
 (one : GeneralNominalVersionedPlans231.SchemaHolds first first.headSchema assignment)
 (two : GeneralNominalVersionedPlans231.SchemaHolds last last.headSchema assignment)
 (finished : GeneralNominalRecursiveInspection.Finished (GeneralNominalQueryProvenance183.headInspection first)) :
 GeneralRebaseNormalizedBody263.Compatible first last assignment := by
 refine ⟨layout,?_,centers⟩
 intro equation present name used
 rcases first.packet.checked.scope.2.1 equation present name used with input | output
 · exact input_binder first last assignment layout.declaration constructors layout.interpretation centers one two finished name input
 · exact output_binder first last assignment layout.declaration seed identity name output

/-- Actual versioned packet Inputs supply both head-schema premises. Finished,
configuration, common owner and semantic centers remain explicit obligations. -/
theorem from_inputs (first last : Plan roles) (assignment : Assignment)
 (layout : GeneralRebasePlanSemantic262.Layout first last)
 (constructors : first.packet.context.state.constructors = last.packet.context.state.constructors)
 (seed : first.packet.context.state.seed = last.packet.context.state.seed)
 (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
 (centers : ∀ index : Nat, Equivalent
   (assignment ((List.ofFn first.input.center)[index]?.getD 0)).1
   (assignment ((List.ofFn last.input.center)[index]?.getD 0)).1)
 (one : GeneralNominalVersionedPlans231.Inputs first assignment)
 (two : GeneralNominalVersionedPlans231.Inputs last assignment)
 (finished : GeneralNominalRecursiveInspection.Finished (GeneralNominalQueryProvenance183.headInspection first)) :
 GeneralRebaseNormalizedBody263.Compatible first last assignment :=
 from_heads first last assignment layout constructors seed identity centers one.2.2.2.2.1 two.2.2.2.2.1 finished
end Yulang.GeneralRebaseHeadSupport263
