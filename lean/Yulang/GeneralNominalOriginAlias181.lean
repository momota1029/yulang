import Yulang.GeneralNominalBinderIdentity181

/-! Equivalent source aliases preserve nominal and structural projection paths.
Projection witnesses are transported unchanged; no uniqueness of structural
observations is required. Bare source observations are equivalent, not equal. -/
namespace Yulang.GeneralNominalOriginAlias181
open GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)

private theorem equivalent_trans (one : Equivalent a b) (two : Equivalent b c) : Equivalent a c :=
  ⟨subtype_trans one.1 two.1,subtype_trans two.2 one.2⟩

 def mapSource (rename : Nat → Nat) : Origin → Origin
  | .source name => .source (rename name)
  | .nominal parent name index => .nominal (mapSource rename parent) name index
  | .structural parent shape index => .structural (mapSource rename parent) shape index

 def Similar (model : Assignment) (first last : Origin) : Prop :=
  (∀ value, Observes model first value →
    ∃ other, Observes model last other ∧ Equivalent value other) ∧
  (∀ value, Observes model last value →
    ∃ other, Observes model first other ∧ Equivalent value other)

 theorem nominal_congr (model : Assignment) (first last : Origin)
    (same : Similar model first last) (name index : Nat) (actual : Ty) :
    Observes model (.nominal first name index) actual ↔
      Observes model (.nominal last name index) actual := by
  constructor
  · intro observed
    cases observed with
    | nominal parent equal found =>
      obtain ⟨other,seen,equivalent⟩ := same.1 _ parent
      exact .nominal seen (equivalent_trans ⟨equivalent.2,equivalent.1⟩ equal) found
  · intro observed
    cases observed with
    | nominal parent equal found =>
      obtain ⟨other,seen,equivalent⟩ := same.2 _ parent
      exact .nominal seen (equivalent_trans ⟨equivalent.2,equivalent.1⟩ equal) found

 theorem structural_congr (model : Assignment) (first last : Origin)
    (same : Similar model first last) (shape : GeneralNormalizedObservation.Shape)
    (index : Nat) (actual : Ty) :
    Observes model (.structural first shape index) actual ↔
      Observes model (.structural last shape index) actual := by
  constructor
  · intro observed
    cases observed with
    | structural parent length equal found =>
      obtain ⟨other,seen,equivalent⟩ := same.1 _ parent
      exact .structural seen length (equivalent_trans ⟨equivalent.2,equivalent.1⟩ equal) found
  · intro observed
    cases observed with
    | structural parent length equal found =>
      obtain ⟨other,seen,equivalent⟩ := same.2 _ parent
      exact .structural seen length (equivalent_trans ⟨equivalent.2,equivalent.1⟩ equal) found

 theorem mapSource_similar (model : Assignment) (rename : Nat → Nat)
    (aliases : ∀ name, Equivalent (model name).1 (model (rename name)).1)
    (origin : Origin) : Similar model origin (mapSource rename origin) := by
  induction origin with
  | source name =>
    constructor
    · intro value seen
      cases seen
      exact ⟨_,.source _,aliases name⟩
    · intro value seen
      cases seen
      exact ⟨_,.source _,⟨(aliases name).2,(aliases name).1⟩⟩
  | nominal parent name index ih =>
    have same := nominal_congr model parent (mapSource rename parent) ih name index
    constructor
    · intro value seen
      exact ⟨value,(same value).mp seen,⟨subtype_refl _,subtype_refl _⟩⟩
    · intro value seen
      exact ⟨value,(same value).mpr seen,⟨subtype_refl _,subtype_refl _⟩⟩
  | structural parent shape index ih =>
    have same := structural_congr model parent (mapSource rename parent) ih shape index
    constructor
    · intro value seen
      exact ⟨value,(same value).mp seen,⟨subtype_refl _,subtype_refl _⟩⟩
    · intro value seen
      exact ⟨value,(same value).mpr seen,⟨subtype_refl _,subtype_refl _⟩⟩

 theorem observes_mapSource (model : Assignment) (rename : Nat → Nat)
    (aliases : ∀ name, Equivalent (model name).1 (model (rename name)).1)
    (origin : Origin) (value : Ty) (seen : Observes model origin value) :
    ∃ other, Observes model (mapSource rename origin) other ∧ Equivalent value other :=
  (mapSource_similar model rename aliases origin).1 value seen

 theorem observes_mapSource_iff (model : Assignment) (rename : Nat → Nat)
    (aliases : ∀ name, Equivalent (model name).1 (model (rename name)).1)
    (origin : Origin) (nonSource : ∀ name, origin ≠ .source name) (value : Ty) :
    Observes model origin value ↔ Observes model (mapSource rename origin) value := by
  cases origin with
  | source name => exact False.elim (nonSource name rfl)
  | nominal parent name index =>
    exact nominal_congr model parent (mapSource rename parent)
      (mapSource_similar model rename aliases parent) name index value
  | structural parent shape index =>
    exact structural_congr model parent (mapSource rename parent)
      (mapSource_similar model rename aliases parent) shape index value

variable {roles : Roles.RoleDecls} {state : GeneralNominalCenteredSteps.State roles}
  {root : GeneralSourceDictionaries.Occurrence roles}

 theorem registered_alias_readback
    (path : B4Target.Steps (GeneralNominalCenteredSteps.Step registry root)
      (GeneralNominalCenteredSteps.initial context root) state)
    (old candidate : GeneralNominalCenters.Plan roles) (registered : old ∈ state.plans)
    (model : Assignment) (valid : GeneralNominalCenteredSteps.Models state model)
    (use : GeneralNominalMaterialization.Use) (present : use ∈ old.headSchema.variables)
    (actual : use.mode = .actual) (rename : Nat → Nat)
    (aliases : ∀ name, Equivalent (model name).1 (model (rename name)).1)
    (name : Nat) (sameCenter : candidate.binder name = old.binder use.name)
    (value : Ty) (seen : Observes model (mapSource rename use.origin) value) :
    Equivalent value (model (candidate.binder name)).1 := by
  obtain ⟨other,observed,equal⟩ := (mapSource_similar model rename aliases use.origin).2 value seen
  exact equivalent_trans equal
    (GeneralNominalBinderIdentity181.registered_readback path old candidate registered valid use
      present actual use.origin rfl name sameCenter other observed)

end Yulang.GeneralNominalOriginAlias181
