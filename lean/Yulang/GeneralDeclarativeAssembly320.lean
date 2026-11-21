import Yulang.GeneralDeclarativeNormalized320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 13500
set_option maxHeartbeats 3400000
namespace Yulang.GeneralDeclarativeAssembly320
open GeneralDeclarations (Clause Declaration Registry Checked)
open GeneralDeclarationPatterns (Constructors Pattern)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Subtype Equivalent)
open GeneralDeclarativeWhere319 (Capture InInterval variables)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand Bounds HeadMeaning bounds_sound)
open GeneralDeclarativeNormalized320 (Center NormalArg NormalMeaning ordered_map center_sound normalized_where_clause)
open GeneralDeclarativeOutputs320 (ChildOutput ChildOutputMeaning child_outputs OutputMeaning compile compile_exact bodyCapture bodyPattern)
open GeneralDeclarativeSubstitution320 (EquationRead equation_read)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralNominalCenteredHeadMatCompilerSemantics (compiled_normalized)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open GeneralDictionaryAssociatedProvenance (lookup lookup_exact)
open GeneralSourceState (Output)
open CommonRoleOutermostResolver (All₂ Frontier)

def Head (s : State) (c : Constructors) (interp : Interpretation) (capture : Nat → Capture)
    (arg : Capture) (p : Pattern) : Prop :=
  Bounds s arg ∧ ∃ exp, translate c interp p = some exp ∧ Center s capture arg exp

theorem head_sound {s c interp capture arg p} (h : Head s c interp capture arg p)
    (m : Assignment) (valid : Models s m) : HeadMeaning c interp capture m arg p := by
  obtain ⟨bound,exp,compiled,center⟩ := h
  exact ⟨eqv_trans (center_sound center m valid) (compiled_normalized compiled),bounds_sound bound m valid⟩

def Named (s : State) (r : Registry) (interp : Interpretation) (d : Demand) (decl : Declaration)
    (capture : Nat → Capture) (out : Output) : Prop :=
  ∃ body exp, lookup r.roles decl out.name = some body ∧ compile r.constructors interp body = some exp ∧
    EquationRead s (bodyCapture d capture body) .actual out.target exp

theorem named_sound {s r interp d decl capture out} (checked : Checked r) (visible : decl ∈ r.declarations)
    (equation : Named s r interp d decl capture out)
    (m : Assignment) (valid : Models s m) : OutputMeaning r.roles r.constructors interp decl d capture m out := by
  obtain ⟨body,exp,provenance,compiled,fact⟩ := equation
  have unique := (checked.2 decl visible).identified.2.2.1
  exact ⟨body,(lookup_exact r.roles decl unique out.name body).mp provenance,
    eqv_trans (equation_read fact m valid) (compiled_normalized ((compile_exact _ _ _).trans compiled))⟩

structure WhereChild (s : State) (c : Constructors) (interp : Interpretation) (capture : Nat → Capture)
    (clause : Clause) (demand : Demand) : Prop where
  role : demand.role = clause.role
  arguments : All₂ (NormalArg s c interp capture) demand.arguments clause.arguments
  outputs : All₂ (ChildOutput s c interp capture) clause.outputs demand.outputs

structure ChildDenotes (c : Constructors) (interp : Interpretation) (capture : Nat → Capture)
    (m : Assignment) (clause : Clause) (demand : Demand) : Prop where
  role : demand.role = clause.role
  arguments : All₂ (NormalMeaning c interp capture m) demand.arguments clause.arguments
  outputs : All₂ (ChildOutputMeaning c interp capture m) clause.outputs demand.outputs

structure Prepared (s : State) (r : Registry) (interp : Interpretation) (decl : Declaration)
    (d : Demand) (capture : Nat → Capture) (children : List Demand) : Prop where
  visible : decl ∈ r.declarations
  role : decl.role = d.role
  captures : ∀ name ∈ decl.inputNames, Bounds s (capture name)
  head : All₂ (Head s r.constructors interp capture) d.arguments decl.head
  children : All₂ (WhereChild s r.constructors interp capture) decl.requirements children
  outputs : ∀ out ∈ d.outputs, Named s r interp d decl capture out

structure Meaning (r : Registry) (interp : Interpretation) (m : Assignment) (d : Demand)
    (decl : Declaration) (capture : Nat → Capture) (children : List Demand) : Prop where
  visible : decl ∈ r.declarations
  role : decl.role = d.role
  captures : ∀ name ∈ decl.inputNames,
    InInterval (m (capture name).lower).1 (m (capture name).upper).1 (m (capture name).center).1
  head : All₂ (HeadMeaning r.constructors interp capture m) d.arguments decl.head
  children : All₂ (ChildDenotes r.constructors interp capture m) decl.requirements children
  outputs : ∀ out ∈ d.outputs, OutputMeaning r.roles r.constructors interp decl d capture m out

/-- For every model, compose syntactic ordinary head/output reads and the
actual source where clause scope without per-clause assumptions about
capture bounds. The same capture is used for the complete local node. -/
theorem prepared_sound {s r interp decl d capture children} (checked : Checked r)
    (prepared : Prepared s r interp decl d capture children) (m : Assignment) (valid : Models s m) :
    Meaning r interp m d decl capture children := by
  refine ⟨prepared.visible,prepared.role,fun n h => bounds_sound (prepared.captures n h) m valid,
    ordered_map prepared.head (fun _ _ _ _ h => head_sound h m valid),?_,
    fun out member => named_sound checked prepared.visible (prepared.outputs out member) m valid⟩
  apply ordered_map prepared.children
  intro clause present child _ info
  exact ⟨info.role,normalized_where_clause (checked.2 decl prepared.visible) present prepared.captures info.arguments m valid,
    child_outputs info.outputs m valid⟩

def ChosenRecipe (s : State) (r : Registry) (interp : Interpretation) (d : Demand)
    (key : Nat) (children : List Demand) : Prop :=
  ∃ decl capture, decl.id = key ∧ Prepared s r interp decl d capture children

def Node (r : Registry) (interp : Interpretation) (m : Assignment) (d : Demand)
    (key : Nat) (children : List Demand) : Prop :=
  ∃ decl capture, decl.id = key ∧ Meaning r interp m d decl capture children

theorem chosen_sound {s r interp d key children} (checked : Checked r)
    (recipe : ChosenRecipe s r interp d key children) (m : Assignment) (valid : Models s m) :
    Node r interp m d key children := by
  obtain ⟨decl,capture,key_eq,prepared⟩ := recipe
  exact ⟨decl,capture,key_eq,prepared_sound checked prepared m valid⟩

end Yulang.GeneralDeclarativeAssembly320
