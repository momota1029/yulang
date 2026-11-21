import Yulang.GeneralDeclarativeOutputs320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000
namespace Yulang.GeneralDeclarativeLocal320
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeDemand320 (Demand Bounds HeadArg HeadMeaning WhereArg WhereMeaning bounds_sound head_args where_args)
open GeneralDeclarativeOutputs320 (ChildOutput ChildOutputMeaning RootOutput OutputMeaning child_outputs root_output)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Declaration Clause Registry Checked)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarationPatterns (Constructors)
open CommonRoleOutermostResolver (All₂)

structure ChildRead (s : State) (catalogue : Constructors) (interp : Interpretation)
    (capture : Nat → Capture) (clause : Clause) (d : Demand) : Prop where
  role : d.role = clause.role
  arguments : All₂ (WhereArg s catalogue interp capture) d.arguments clause.arguments
  outputs : All₂ (ChildOutput s catalogue interp capture) clause.outputs d.outputs

structure ChildMeaning (catalogue : Constructors) (interp : Interpretation)
    (capture : Nat → Capture) (m : Assignment) (clause : Clause) (d : Demand) : Prop where
  role : d.role = clause.role
  arguments : All₂ (WhereMeaning catalogue interp capture m) d.arguments clause.arguments
  outputs : All₂ (ChildOutputMeaning catalogue interp capture m) clause.outputs d.outputs

theorem child_sound {s catalogue interp capture clause d}
    (read : ChildRead s catalogue interp capture clause d) (model : Assignment) (valid : Models s model) :
    ChildMeaning catalogue interp capture model clause d :=
  ⟨read.role,where_args read.arguments model valid,child_outputs read.outputs model valid⟩

theorem children_sound {s catalogue interp capture clauses children}
    (read : All₂ (ChildRead s catalogue interp capture) clauses children)
    (model : Assignment) (valid : Models s model) :
    All₂ (ChildMeaning catalogue interp capture model) clauses children := by
  induction read with
  | nil => exact .nil
  | cons first _ ih => exact .cons (child_sound first model valid) ih

/-- Syntactic sufficient evidence for a local dictionary branch; producing
this evidence from approved logical selection is a separate obligation. -/
structure LocalRead (s : State) (r : Registry) (interp : Interpretation)
    (d : Demand) (decl : Declaration) (capture : Nat → Capture) (children : List Demand) : Prop where
  visible : decl ∈ r.declarations
  role : decl.role = d.role
  captures : ∀ name ∈ decl.inputNames, Bounds s (capture name)
  head : All₂ (HeadArg s r.constructors interp capture) d.arguments decl.head
  children : All₂ (ChildRead s r.constructors interp capture) decl.requirements children
  outputs : ∀ request ∈ d.outputs, RootOutput s r.roles r.constructors interp decl d capture request

structure NodeMeaning (r : Registry) (interp : Interpretation) (m : Assignment)
    (d : Demand) (decl : Declaration) (capture : Nat → Capture) (children : List Demand) : Prop where
  visible : decl ∈ r.declarations
  role : decl.role = d.role
  captures : ∀ name ∈ decl.inputNames,
    InInterval (m (capture name).lower).1 (m (capture name).upper).1 (m (capture name).center).1
  head : All₂ (HeadMeaning r.constructors interp capture m) d.arguments decl.head
  children : All₂ (ChildMeaning r.constructors interp capture m) decl.requirements children
  outputs : ∀ request ∈ d.outputs, OutputMeaning r.roles r.constructors interp decl d capture m request

/-- All locally materialized endpoints and named results, the actual source
head, and the child-demand equations hold in one given model. This does not
assume or conclude that any child has itself selected a dictionary. -/
theorem node_sound {s r interp d decl capture children} (checked : Checked r)
    (read : LocalRead s r interp d decl capture children) (m : Assignment) (valid : Models s m) :
    NodeMeaning r interp m d decl capture children := by
  have unique := (checked.2 decl read.visible).identified.2.2.1
  exact ⟨read.visible,read.role,fun name used => bounds_sound (read.captures name used) m valid,
    head_args read.head m valid,children_sound read.children m valid,
    fun out used => root_output unique (read.outputs out used) m valid⟩

end Yulang.GeneralDeclarativeLocal320
