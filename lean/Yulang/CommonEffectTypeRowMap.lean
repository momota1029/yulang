import Yulang.CommonEffectFreshRows

/-! Uniform static row transport through every immediate and latent row of
arbitrary Common finite/regular syntax. The same static action is used in
arrow arguments, as in OperationalTransportTyping; runtime wrappers reverse
their argument action. This is a syntax map, not source boundary insertion. -/
namespace Yulang.CommonEffectTypeRowMap
open Common (Row Ty)
open CommonSyntax (Layer State)

def layer (onRow : Row → Row) (onRef : α → β) : Layer Row α → Layer Row β
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union a b => .union (layer onRow onRef a) (layer onRow onRef b)
  | .inter a b => .inter (layer onRow onRef a) (layer onRow onRef b)
  | .pair a b => .pair (onRef a) (onRef b)
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .record label head tail => .record label (onRef head) (layer onRow onRef tail)
  | .recordDefault label source fallback => .recordDefault label (layer onRow onRef source) (onRef fallback)
  | .variant label payload => .variant label (onRef payload)
  | .arrow arg incoming result outgoing => .arrow (onRef arg) (onRow incoming) (onRef result) (onRow outgoing)
  | .mask hidden body => .mask hidden (layer onRow onRef body)

mutual
  def oldState (onRow : Row → Row) : RegularInferenceModel.State Row → RegularInferenceModel.State Row
    | .node body => .node (oldType onRow body)
    | .block body root => .block (oldBlockList onRow body) root

  def oldType (onRow : Row → Row) : RegularValueTypes.Layer Row (RegularInferenceModel.State Row) → RegularValueTypes.Layer Row (RegularInferenceModel.State Row)
    | .base scalar => .base scalar
    | .bottom => .bottom
    | .top => .top
    | .union a b => .union (oldType onRow a) (oldType onRow b)
    | .inter a b => .inter (oldType onRow a) (oldType onRow b)
    | .pair a b => .pair (oldState onRow a) (oldState onRow b)
    | .emptyRecord => .emptyRecord
    | .record label head tail => .record label (oldState onRow head) (oldType onRow tail)
    | .variant label payload => .variant label (oldState onRow payload)
    | .arrow arg incoming result outgoing => .arrow (oldState onRow arg) (onRow incoming) (oldState onRow result) (onRow outgoing)

  def oldBlockLayer (onRow : Row → Row) : RegularValueTypes.Layer Row (Nat ⊕ RegularInferenceModel.State Row) → RegularValueTypes.Layer Row (Nat ⊕ RegularInferenceModel.State Row)
    | .base scalar => .base scalar
    | .bottom => .bottom
    | .top => .top
    | .union a b => .union (oldBlockLayer onRow a) (oldBlockLayer onRow b)
    | .inter a b => .inter (oldBlockLayer onRow a) (oldBlockLayer onRow b)
    | .pair a b => .pair (oldRef onRow a) (oldRef onRow b)
    | .emptyRecord => .emptyRecord
    | .record label head tail => .record label (oldRef onRow head) (oldBlockLayer onRow tail)
    | .variant label payload => .variant label (oldRef onRow payload)
    | .arrow arg incoming result outgoing => .arrow (oldRef onRow arg) (onRow incoming) (oldRef onRow result) (onRow outgoing)

  def oldBlockList (onRow : Row → Row) : List (RegularValueTypes.Layer Row (Nat ⊕ RegularInferenceModel.State Row)) → List (RegularValueTypes.Layer Row (Nat ⊕ RegularInferenceModel.State Row))
    | [] => []
    | head :: tail => oldBlockLayer onRow head :: oldBlockList onRow tail

  def oldRef (onRow : Row → Row) : Nat ⊕ RegularInferenceModel.State Row → Nat ⊕ RegularInferenceModel.State Row
    | .inl index => .inl index
    | .inr source => .inr (oldState onRow source)
end

mutual
  def state (onRow : Row → Row) : State Row → State Row
    | .node body => .node (type onRow body)
    | .block body root => .block (blockList onRow body) root
    | .legacy source => .legacy (oldState onRow source)

  def type (onRow : Row → Row) : Layer Row (State Row) → Layer Row (State Row)
    | .base scalar => .base scalar
    | .bottom => .bottom
    | .top => .top
    | .union a b => .union (type onRow a) (type onRow b)
    | .inter a b => .inter (type onRow a) (type onRow b)
    | .pair a b => .pair (state onRow a) (state onRow b)
    | .emptyRecord => .emptyRecord
    | .exactEmpty => .exactEmpty
    | .record label head tail => .record label (state onRow head) (type onRow tail)
    | .recordDefault label source fallback => .recordDefault label (type onRow source) (state onRow fallback)
    | .variant label payload => .variant label (state onRow payload)
    | .arrow arg incoming result outgoing => .arrow (state onRow arg) (onRow incoming) (state onRow result) (onRow outgoing)
    | .mask hidden body => .mask hidden (type onRow body)

  def blockLayer (onRow : Row → Row) : Layer Row (Nat ⊕ State Row) → Layer Row (Nat ⊕ State Row)
    | .base scalar => .base scalar
    | .bottom => .bottom
    | .top => .top
    | .union a b => .union (blockLayer onRow a) (blockLayer onRow b)
    | .inter a b => .inter (blockLayer onRow a) (blockLayer onRow b)
    | .pair a b => .pair (ref onRow a) (ref onRow b)
    | .emptyRecord => .emptyRecord
    | .exactEmpty => .exactEmpty
    | .record label head tail => .record label (ref onRow head) (blockLayer onRow tail)
    | .recordDefault label source fallback => .recordDefault label (blockLayer onRow source) (ref onRow fallback)
    | .variant label payload => .variant label (ref onRow payload)
    | .arrow arg incoming result outgoing => .arrow (ref onRow arg) (onRow incoming) (ref onRow result) (onRow outgoing)
    | .mask hidden body => .mask hidden (blockLayer onRow body)

  def blockList (onRow : Row → Row) : List (Layer Row (Nat ⊕ State Row)) → List (Layer Row (Nat ⊕ State Row))
    | [] => []
    | head :: tail => blockLayer onRow head :: blockList onRow tail

  def ref (onRow : Row → Row) : Nat ⊕ State Row → Nat ⊕ State Row
    | .inl index => .inl index
    | .inr source => .inr (state onRow source)
end

mutual
  theorem oldState_inverse (first last : Row → Row) (inverse : ∀ row, last (first row) = row)
      (source : RegularInferenceModel.State Row) : oldState last (oldState first source) = source := by
    cases source
    all_goals simp only [oldState, oldType_inverse first last inverse, oldBlockList_inverse first last inverse]
  theorem oldType_inverse (first last : Row → Row) (inverse : ∀ row, last (first row) = row)
      (source : RegularValueTypes.Layer Row (RegularInferenceModel.State Row)) : oldType last (oldType first source) = source := by
    cases source
    all_goals simp only [oldType, oldType_inverse first last inverse, oldState_inverse first last inverse, inverse]
  theorem oldBlockLayer_inverse (first last : Row → Row) (inverse : ∀ row, last (first row) = row)
      (source : RegularValueTypes.Layer Row (Nat ⊕ RegularInferenceModel.State Row)) : oldBlockLayer last (oldBlockLayer first source) = source := by
    cases source
    all_goals simp only [oldBlockLayer, oldBlockLayer_inverse first last inverse, oldRef_inverse first last inverse, inverse]
  theorem oldBlockList_inverse (first last : Row → Row) (inverse : ∀ row, last (first row) = row)
      (source : List (RegularValueTypes.Layer Row (Nat ⊕ RegularInferenceModel.State Row))) : oldBlockList last (oldBlockList first source) = source := by
    cases source
    all_goals simp only [oldBlockList, oldBlockLayer_inverse first last inverse, oldBlockList_inverse first last inverse]
  theorem oldRef_inverse (first last : Row → Row) (inverse : ∀ row, last (first row) = row)
      (source : Nat ⊕ RegularInferenceModel.State Row) : oldRef last (oldRef first source) = source := by
    cases source
    all_goals simp only [oldRef, oldState_inverse first last inverse]
end

mutual
  theorem state_inverse (first last : Row → Row) (inverse : ∀ row, last (first row) = row)
      (source : State Row) : state last (state first source) = source := by
    cases source
    all_goals simp only [state, type_inverse first last inverse, blockList_inverse first last inverse, oldState_inverse first last inverse]
  theorem type_inverse (first last : Row → Row) (inverse : ∀ row, last (first row) = row)
      (source : Layer Row (State Row)) : type last (type first source) = source := by
    cases source
    all_goals simp only [type, type_inverse first last inverse, state_inverse first last inverse, inverse]
  theorem blockLayer_inverse (first last : Row → Row) (inverse : ∀ row, last (first row) = row)
      (source : Layer Row (Nat ⊕ State Row)) : blockLayer last (blockLayer first source) = source := by
    cases source
    all_goals simp only [blockLayer, blockLayer_inverse first last inverse, ref_inverse first last inverse, inverse]
  theorem blockList_inverse (first last : Row → Row) (inverse : ∀ row, last (first row) = row)
      (source : List (Layer Row (Nat ⊕ State Row))) : blockList last (blockList first source) = source := by
    cases source
    all_goals simp only [blockList, blockLayer_inverse first last inverse, blockList_inverse first last inverse]
  theorem ref_inverse (first last : Row → Row) (inverse : ∀ row, last (first row) = row)
      (source : Nat ⊕ State Row) : ref last (ref first source) = source := by
    cases source
    all_goals simp only [ref, state_inverse first last inverse]
end

def enterType (permission : CommonEffectRequestGeneration.Permission) (source : Ty) : Ty :=
  type (CommonEffectFreshRows.enterRow permission) source

def exitType (permission : CommonEffectRequestGeneration.Permission) (source : Ty) : Ty :=
  type (CommonEffectFreshRows.exitRow permission) source

theorem exit_enter_type (permission : CommonEffectRequestGeneration.Permission) (source : Ty) :
    exitType permission (enterType permission source) = source :=
  type_inverse _ _ (CommonEffectFreshRows.exit_enter permission) source

theorem release_protect_type (scope : Nat) (permission : CommonEffectRequestGeneration.Permission) (source : Ty) :
    type (CommonSignedRows.commonRelease scope permission.allows)
      (type (CommonSignedRows.commonProtect scope permission.allows) source) = source :=
  type_inverse _ _ (CommonSignedRows.commonRelease_protect scope permission.allows) source

theorem protect_release_type (scope : Nat) (permission : CommonEffectRequestGeneration.Permission) (source : Ty) :
    type (CommonSignedRows.commonProtect scope permission.allows)
      (type (CommonSignedRows.commonRelease scope permission.allows) source) = source :=
  type_inverse _ _ (CommonSignedRows.commonProtect_release scope permission.allows) source

end Yulang.CommonEffectTypeRowMap
