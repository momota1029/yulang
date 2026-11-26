import Yulang.GeneralDeclarativeI65I74StructuralWhereSiblingPermutation433

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
namespace Yulang.GeneralDeclarativeI65.I72.WrapPermutationAudit433
open GeneralDeclarativeI65 WhereAssociated432
open GeneralDeclarations (Declaration Clause OutputBinder DeclarationChecked)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeEmissionForest322 (Placement)

def binder : OutputBinder := ⟨9,50,51⟩
def producer : Clause := ⟨50,7,[.var 8],[⟨51,3,.var 9⟩]⟩
def sibling : Clause := ⟨54,8,[.var 8],[⟨55,5,.var 9⟩]⟩
def parent : Declaration :=
  ⟨218,20,[.app 40 [.var 8]],[producer,sibling],[⟨52,6,.app 40 [.var 9]⟩],[binder]⟩
def swapped : Declaration := {parent with requirements := [sibling,producer]}

private def inputBundle (d : Declaration) : InputBundle :=
  let catalogue : List Row := [⟨40,some ⟨[.type],40⟩,.invariant⟩]
  ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,
    ⟨1,[⟨7,1,[(3,none)]⟩,⟨8,1,[(5,none)]⟩,⟨20,1,[(6,none)]⟩]⟩,[d]⟩
private def bits : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
private def makeEnv (d : Declaration) : Option Environment := do
  let program ← compile bits
  let bundle ← GeneralSourceMetadataBareBundle291.compile (inputBundle d)
  pure ⟨0,0,0,bits,program,bundle⟩
def baseEnv : Environment := (makeEnv parent).get (by decide +kernel)
def swapEnv : Environment := (makeEnv swapped).get (by decide +kernel)

def core (e : Environment) : GeneralDeclarativeI65.State :=
  ⟨⟨e,⟨⟨[],[]⟩,[]⟩,[]⟩,[],[],[]⟩

def q : Request := ⟨[72],⟨20,[point 6],[⟨6,12⟩]⟩⟩
def place : Placement := ⟨fun _ _ => point 99,fun cl _ => if cl.id = 50 then 4 else 70⟩
def captured (n : Nat) := if n = 8 then point 0 else point 99
def before : AuthoredBodyFrame393 (core baseEnv) q :=
  ⟨0,parent,by decide +kernel,by decide +kernel,place,captured⟩
def after : AuthoredBodyFrame393 (core swapEnv) q :=
  ⟨0,swapped,by decide +kernel,by decide +kernel,place,captured⟩

theorem initialCheck : DeclarationChecked
    (authoredRegistry (core baseEnv).current).constructors
    (authoredRegistry (core baseEnv).current).roles before.decl := by
  have ok : GeneralSourceMetadataDeclarations291.explicitCheck
    (authoredRegistry (core baseEnv).current)
    (GeneralSourceMetadataRows291.interpretation baseEnv.source.snapshot) = true := by decide +kernel
  have complete := (GeneralSourceMetadataDeclarations291.explicit_exact _ _).mp ok
  exact GeneralDeclarativeWitnessHeader349.decl_checked (complete parent (by decide +kernel)) (by decide +kernel)

theorem both_exact_original_declared_orders_are_checked433 :
    GeneralDeclarativeWitnessHeader349.checksDecl baseEnv.source parent = true ∧
    GeneralDeclarativeWitnessHeader349.checksDecl swapEnv.source swapped = true := by decide +kernel

theorem original_ids_move_occurrences_but_no_named_output_target433 :
    (frameWhereKids400 before)[0]? = some ⟨[72,0],⟨7,[point 0],[⟨3,4⟩]⟩⟩ ∧
    (frameWhereKids400 after)[1]? = some ⟨[72,1],⟨7,[point 0],[⟨3,4⟩]⟩⟩ ∧
    (frameWhereKids400 before)[1]? = some ⟨[72,1],⟨8,[point 0],[⟨5,4⟩]⟩⟩ ∧
    (frameWhereKids400 after)[0]? = some ⟨[72,0],⟨8,[point 0],[⟨5,4⟩]⟩⟩ := by
  have swap : before.decl.requirements.Perm after.decl.requirements :=
    .swap sibling producer []
  have p :=
    same_source_where_clause_keeps_demand_under_permutation433 before after initialCheck rfl swap rfl rfl
      (clause := producer) (i := 0) (j := 1) rfl rfl
  have s :=
    same_source_where_clause_keeps_demand_under_permutation433 before after initialCheck rfl swap rfl rfl
      (clause := sibling) (i := 1) (j := 0) rfl rfl
  exact ⟨p.1,p.2,s.1,s.2⟩

theorem sibling_fallback_70_is_not_used_for_original_binder433 :
    place.targets sibling 55 = 70 ∧ before.names.output binder.name = 4 ∧ after.names.output binder.name = 4 :=
  ⟨rfl,rfl,rfl⟩

#print axioms checked_where_permutation_keeps_lexical_binder_targets433
#print axioms same_source_where_clause_keeps_demand_under_permutation433
#print axioms both_exact_original_declared_orders_are_checked433
#print axioms original_ids_move_occurrences_but_no_named_output_target433
#print axioms sibling_fallback_70_is_not_used_for_original_binder433
end Yulang.GeneralDeclarativeI65.I72.WrapPermutationAudit433
