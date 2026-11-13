import Yulang.GeneralDictionaryMixed168Tree
import Yulang.GeneralDictionaryOrdinary168Relocation

/-! Structural leaf certificates persist when only ordinary constraints and
reservation ledgers grow. Descriptor-changing refresh is excluded. -/
namespace Yulang.GeneralDictionary169LeafPersistence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveCandidates
open GeneralDictionaryOrdinaryTransport
open GeneralNominalSpineFacts
variable {roles : Roles.RoleDecls}

def scalar (context : Context) (reserved atoms allocated)
    (shape : GeneralDictionaryScalarLeaf.ScalarLeafShape context (roles := roles) root declaration) :
    GeneralDictionaryScalarLeaf.ScalarLeafShape (extend context reserved atoms allocated) root declaration where
  terminal := shape.terminal
  outputs := shape.outputs
  role := shape.role
  slot := shape.slot
  base := shape.base
  noNominal := shape.noNominal
  head := shape.head
  inputs := shape.inputs
  query := shape.query
  located := shape.located

def spine (state : GeneralNominalState.State) (reserved atoms allocated)
    {names : Fin n → Nat} {bounds} {slot} (shape : Spine state names bounds slot) :
    Spine (extendState state reserved atoms allocated) names bounds slot :=
  match shape with
  | .leaf s descriptor recorded parameters => Spine.leaf (state := extendState state reserved atoms allocated) s descriptor recorded parameters
  | .wrap s child descriptor recorded parameters rest =>
      Spine.wrap (state := extendState state reserved atoms allocated) s child descriptor recorded parameters (spine state reserved atoms allocated rest)

theorem spine_query (state : GeneralNominalState.State) (reserved atoms allocated)
    {names : Fin n → Nat} {bounds} {slot} (shape : Spine state names bounds slot) :
    (spine state reserved atoms allocated shape).query = shape.query := by
  induction shape with
  | leaf => rfl
  | wrap s child descriptor recorded parameters rest ih =>
    simp only [spine,Spine.query,ih]

def nominal (context : Context) (reserved atoms allocated)
    (shape : GeneralDictionarySpineLeaf.SpineLeafShape context (roles := roles) root declaration) :
    GeneralDictionarySpineLeaf.SpineLeafShape (extend context reserved atoms allocated) root declaration where
  terminal := shape.terminal
  outputs := shape.outputs
  role := shape.role
  slot := shape.slot
  arity := shape.arity
  names := shape.names
  distinct := shape.distinct
  inputs := shape.inputs
  bounds := shape.bounds
  spine := spine context.state reserved atoms allocated shape.spine
  query := by rw [spine_query]; exact shape.query
  located := shape.located
end Yulang.GeneralDictionary169LeafPersistence
