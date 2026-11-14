import Yulang.GeneralNominalOriginAlias181
import Yulang.GeneralNominalCenteredModelExtension

/-! Each origin path has one source root. Its equivalence alone suffices for
transport; paired recorded ordinary atoms can certify this local equivalence. -/
namespace Yulang.GeneralNominalOriginRootAlias181
open GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalOriginAlias181 (Similar mapSource)

 theorem root_similar (model : Assignment) (rename : Nat → Nat) (origin : Origin) :
    Equivalent (model (originSource origin)).1 (model (rename (originSource origin))).1 →
      Similar model origin (mapSource rename origin) := by
  induction origin with
  | source name =>
    intro alias
    constructor
    · intro value seen
      cases seen
      exact ⟨_,.source _,alias⟩
    · intro value seen
      cases seen
      exact ⟨_,.source _,⟨alias.2,alias.1⟩⟩
  | nominal parent name index ih =>
    intro alias
    have same := GeneralNominalOriginAlias181.nominal_congr model parent (mapSource rename parent)
      (ih alias) name index
    constructor
    · intro value seen
      exact ⟨value,(same value).mp seen,⟨subtype_refl _,subtype_refl _⟩⟩
    · intro value seen
      exact ⟨value,(same value).mpr seen,⟨subtype_refl _,subtype_refl _⟩⟩
  | structural parent shape index ih =>
    intro alias
    have same := GeneralNominalOriginAlias181.structural_congr model parent (mapSource rename parent)
      (ih alias) shape index
    constructor
    · intro value seen
      exact ⟨value,(same value).mp seen,⟨subtype_refl _,subtype_refl _⟩⟩
    · intro value seen
      exact ⟨value,(same value).mpr seen,⟨subtype_refl _,subtype_refl _⟩⟩

 theorem root_observes_iff (model : Assignment) (rename : Nat → Nat) (origin : Origin)
    (alias : Equivalent (model (originSource origin)).1 (model (rename (originSource origin))).1)
    (nonSource : ∀ name, origin ≠ .source name) (value : Ty) :
    Observes model origin value ↔ Observes model (mapSource rename origin) value := by
  cases origin with
  | source name => exact False.elim (nonSource name rfl)
  | nominal parent name index =>
    exact GeneralNominalOriginAlias181.nominal_congr model parent (mapSource rename parent)
      (root_similar model rename parent alias) name index value
  | structural parent shape index =>
    exact GeneralNominalOriginAlias181.structural_congr model parent (mapSource rename parent)
      (root_similar model rename parent alias) shape index value

 def AliasCertificate (state : GeneralNominalState.State) (first last : Nat) : Prop :=
  first = last ∨
    (.tyLe (.var first) (.var last) ∈ state.ordinary ∧
      .tyLe (.var last) (.var first) ∈ state.ordinary)

 theorem certificate_equivalent (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model)
    (certificate : AliasCertificate state first last) : Equivalent (model first).1 (model last).1 := by
  rcases certificate with same | ⟨forward,backward⟩
  · rw [same]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · exact ⟨valid.2.2 _ forward,valid.2.2 _ backward⟩

 def RootRecorded (state : GeneralNominalState.State) (rename : Nat → Nat) (origin : Origin) : Prop :=
  AliasCertificate state (originSource origin) (rename (originSource origin))

 theorem recorded_root_similar (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (rename : Nat → Nat) (origin : Origin)
    (certificate : RootRecorded state rename origin) :
    Similar model origin (mapSource rename origin) :=
  root_similar model rename origin (certificate_equivalent state model valid certificate)

 theorem recorded_observes_iff (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (rename : Nat → Nat) (origin : Origin)
    (certificate : RootRecorded state rename origin)
    (nonSource : ∀ name, origin ≠ .source name) (value : Ty) :
    Observes model origin value ↔ Observes model (mapSource rename origin) value :=
  root_observes_iff model rename origin (certificate_equivalent state model valid certificate) nonSource value

end Yulang.GeneralNominalOriginRootAlias181
