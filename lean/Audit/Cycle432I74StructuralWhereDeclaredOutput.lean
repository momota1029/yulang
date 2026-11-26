import Yulang.GeneralDeclarativeI65I74StructuralWhereDeclaredOutput432

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
namespace Yulang.GeneralDeclarativeI65.I72.WrapOutputAudit432
open GeneralDeclarativeI65 WhereAssociated432
open GeneralDeclarations (Declaration Clause Equation OutputBinder DeclarationChecked)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment Use readUse)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open CommonDeclaredNominalInspection (Parameter)
open GeneralDeclarativeEmissionForest322 (Placement)
open CommonNominalFullCarrier (nominal)

def ctor : Nat := 40
def inputBinder : Nat := 8
def outputBinder : OutputBinder := ⟨9,50,51⟩
def getItem : Clause := ⟨50,21,[.var inputBinder],[⟨51,4,.var outputBinder.name⟩]⟩
def supplySibling : Clause := ⟨60,22,[.var inputBinder],[⟨61,5,.var outputBinder.name⟩]⟩
def forbiddenSibling : Clause := ⟨62,23,[.var outputBinder.name],[]⟩
def wrapRhs : Equation := ⟨52,3,.app ctor [.var outputBinder.name]⟩
def wrap : Declaration :=
  ⟨218,20,[.app ctor [.var inputBinder]],[getItem],[wrapRhs],[outputBinder]⟩
def wrapWithSibling : Declaration := {wrap with requirements := [getItem,supplySibling]}
def showLikeForbidden : Declaration := {wrap with requirements := [getItem,forbiddenSibling]}
def container : Declaration := ⟨219,21,[.var inputBinder],[],[⟨53,4,.var inputBinder⟩],[]⟩
def invariantParam : Parameter := ⟨.value,.invariant⟩

private def bodySource : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
private def authoredInput (parent : Declaration) : InputBundle :=
  let catalogue : List Row := [⟨ctor,some ⟨[.type],ctor⟩,.invariant⟩]
  ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,
    ⟨0,[⟨20,1,[(3,none)]⟩,⟨21,1,[(4,none)]⟩,⟨22,1,[(5,none)]⟩,⟨23,1,[]⟩]⟩,[parent,container]⟩

private def make (parent : Declaration) : Option Environment := do
  let graph ← compile bodySource
  let source ← GeneralSourceMetadataBareBundle291.compile (authoredInput parent)
  pure ⟨0,0,0,bodySource,graph,source⟩

def environment : Environment := (make wrap).get (by decide +kernel)
def actualCore : GeneralDeclarativeI65.State :=
  ⟨⟨environment,⟨⟨[],[]⟩,[]⟩,[]⟩,List.replicate 40 [] ++ [[invariantParam]],[],[]⟩

def use : Use actualCore.current.environment ctor 1 :=
  (readUse actualCore.current.environment ctor 1).get (by decide +kernel)

def authoredReq : Request := ⟨[72],⟨20,[point 0],[⟨3,12⟩]⟩⟩
def site : Placement := ⟨fun _ _ => point 0,fun _ _ => 4⟩
def authoredFrame : AuthoredBodyFrame393 actualCore authoredReq :=
  ⟨0,wrap,by decide +kernel,by decide +kernel,site,fun n => if n = inputBinder then point 1 else point 0⟩

theorem authored_wrap_has_original_output_only_scope432 :
    GeneralDeclarativeWitnessHeader349.checksDecl environment.source wrap = true ∧
    GeneralDeclarativeWitnessHeader349.checksDecl environment.source wrapWithSibling = true ∧
    GeneralDeclarativeWitnessHeader349.checksDecl environment.source showLikeForbidden = false := by
  decide +kernel

theorem positive_wrap_source_has_real_output_binder432 :
    ∃ origin : OriginalWhereBinder395 authoredFrame outputBinder wrapRhs,
      origin.clauseOrdinal = 0 ∧ origin.outputOrdinal = 0 ∧ origin.child.occurrence = [72,0] ∧
      origin.output.name = 4 ∧ origin.child.demand.arguments = [point 1] := by
  have checked : DeclarationChecked (authoredRegistry actualCore.current).constructors
      (authoredRegistry actualCore.current).roles wrap := by
    have explicit : GeneralSourceMetadataDeclarations291.explicitCheck
        (authoredRegistry actualCore.current)
        (GeneralSourceMetadataRows291.interpretation environment.source.snapshot) = true := by decide +kernel
    have covered := (GeneralSourceMetadataDeclarations291.explicit_exact _ _).mp explicit
    exact GeneralDeclarativeWitnessHeader349.decl_checked (covered wrap (by decide +kernel))
      authored_wrap_has_original_output_only_scope432.1
  have _frameProduced : authoredFrame.decl.Produced := checked.produced
  -- Witness the literal positions directly, rather than adopting any
  -- different equation or output binder advertised by a fixture.
  let entry := authoredFrame.whereFor getItem
  let output := (entry.demand.outputs[0]?).get (by decide +kernel)
  let origin : OriginalWhereBinder395 authoredFrame outputBinder wrapRhs :=
    ⟨0,0,entry,⟨51,4,.var outputBinder.name⟩,output,rfl,rfl,
      rfl,rfl,rfl,rfl,rfl,rfl⟩
  refine ⟨origin,?_⟩
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem authored_invariant_unary_plan_reads_the_where_value432
    (origin : OriginalWhereBinder395 authoredFrame outputBinder wrapRhs)
    (m : GeneralDeclarativeI65.Model) :
    evaluateMixedRhs401 (sourceRead401 m (authoredFrame.slots (.explicit wrapRhs)))
      (invariantUnaryValuePlan432 ctor outputBinder.name invariantParam use
        (by decide +kernel) (by decide +kernel) rfl rfl) =
    some (nominal ctor [.inl (m.assignment origin.output.target).1]) :=
  invariant_unary_RHS_reads_the_declared_where_slot432 origin m


def siblingEnvironment : Environment := (make wrapWithSibling).get (by decide +kernel)
def siblingCore : GeneralDeclarativeI65.State :=
  {actualCore with current := {actualCore.current with environment := siblingEnvironment}}
def siblingFrame : AuthoredBodyFrame393 siblingCore authoredReq :=
  ⟨0,wrapWithSibling,by decide +kernel,by decide +kernel,site,
    fun n => if n = inputBinder then point 1 else point 0⟩

theorem authored_sibling_uses_named_output_not_b_as_input432 :
    ∃ req : GeneralSourceState.Output,
      (frameWhereKids400 siblingFrame)[1]? = some
        ⟨[72,1],(siblingFrame.whereFor supplySibling).demand⟩ ∧
      (siblingFrame.whereFor supplySibling).demand.arguments = [point 1] ∧
      (siblingFrame.whereFor supplySibling).demand.outputs[0]? = some req ∧
      req.name = 5 ∧ req.target = siblingFrame.names.output outputBinder.name := by
  have inSource : outputBinder ∈ siblingFrame.decl.outputBinders := by decide +kernel
  obtain ⟨req,atSource,atOutput,key,target⟩ :=
    original_sibling_named_output_uses_parent_target432 siblingFrame inSource
      (whereOrdinal:=1) (outputOrdinal:=0)
      (clause:=supplySibling) (equation:=⟨61,5,.var outputBinder.name⟩) rfl rfl rfl
  exact ⟨req,atSource,rfl,atOutput,key,target⟩

theorem independently_forbidden_show_input_cannot_be_checked432 {constructors roles} :
    ¬ DeclarationChecked constructors roles showLikeForbidden :=
  GeneralDeclarations.output_input_rejected showLikeForbidden forbiddenSibling (by decide +kernel)
    outputBinder.name (by decide +kernel) (by decide +kernel)

#print axioms invariant_unary_RHS_reads_the_declared_where_slot432
#print axioms actual_parent_unary_output_uses_exact_where_target432
#print axioms original_output_binder_cannot_be_where_input432
#print axioms authored_wrap_has_original_output_only_scope432
#print axioms positive_wrap_source_has_real_output_binder432
#print axioms authored_invariant_unary_plan_reads_the_where_value432
#print axioms original_atlas_read_recovers_typed_plan432
#print axioms original_sibling_named_output_uses_parent_target432
#print axioms original_binder_reserves_the_named_shared_target432
#print axioms authored_sibling_uses_named_output_not_b_as_input432
#print axioms independently_forbidden_show_input_cannot_be_checked432
end Yulang.GeneralDeclarativeI65.I72.WrapOutputAudit432
