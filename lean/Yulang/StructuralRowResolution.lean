import Yulang.StructuralCut

/-!
# Transport of ground subtyping across row representations

Mapping rows preserves every constructor, including duplicate record labels
and both rows of arrows. Monotone row maps preserve the existing declarative
subtype relation. An injective row encoding which also reflects row inclusion
reflects subtyping: cut elimination removes intermediate types which need not
lie in the encoding's image.

Injectivity matters for the reference algebra's reflexivity on raw malformed
record spines. This module therefore states that requirement explicitly;
quotienting finite row codes by decoded equality supplies it without adding
a source-language well-formedness restriction.
-/

namespace Yulang.StructuralRowResolution

open StructuralBase StructuralDecisions

variable {A : Type u} {B : Type v}

def mapRows (f : A → B) : Ty A → Ty B
  | .base base => .base base
  | .bottom => .bottom
  | .top => .top
  | .union left right => .union (mapRows f left) (mapRows f right)
  | .inter left right => .inter (mapRows f left) (mapRows f right)
  | .pair left right => .pair (mapRows f left) (mapRows f right)
  | .emptyRecord => .emptyRecord
  | .record label value rest => .record label (mapRows f value) (mapRows f rest)
  | .variant label value => .variant label (mapRows f value)
  | .arrow input inputRow output outputRow =>
      .arrow (mapRows f input) (f inputRow) (mapRows f output) (f outputRow)

@[simp] theorem mapRows_id (type : Ty A) : mapRows id type = type := by
  induction type <;> simp_all [mapRows]

@[simp] theorem mapRows_comp {C : Type w} (f : A → B) (g : B → C) (type : Ty A) :
    mapRows g (mapRows f type) = mapRows (g ∘ f) type := by
  induction type <;> simp_all [mapRows]

@[simp] theorem mapRows_lookup (f : A → B) (type : Ty A) (label : Nat) :
    (mapRows f type).lookup label = (type.lookup label).map (mapRows f) := by
  induction type with
  | record name value rest _ ih =>
      by_cases same : label = name <;> simp [mapRows, Ty.lookup, same, ih]
  | _ => rfl

theorem mapRows_lookup_some (f : A → B) (type : Ty A) (label : Nat) (value : Ty B) :
    (mapRows f type).lookup label = some value ↔
      ∃ original, type.lookup label = some original ∧ mapRows f original = value := by
  rw [mapRows_lookup]
  cases found : type.lookup label <;> simp

@[simp] theorem mapRows_isRecord (f : A → B) (type : Ty A) :
    IsRecord (mapRows f type) ↔ IsRecord type := by
  induction type with
  | emptyRecord => exact ⟨fun _ => .empty, fun _ => .empty⟩
  | record label value rest _ ih =>
      constructor
      · intro shape
        cases shape with | field tail => exact .field (ih.mp tail)
      · intro shape
        cases shape with | field tail => exact .field (ih.mpr tail)
  | _ => constructor <;> intro impossible <;> cases impossible

theorem mapRows_injective (f : A → B) (injective : Function.Injective f) :
    Function.Injective (mapRows f) := by
  intro source
  induction source with
  | base base =>
      intro target same; cases target <;> simp [mapRows] at same
      cases same; rfl
  | bottom | top =>
      intro target same; cases target <;> simp [mapRows] at same
      rfl
  | union left right ihl ihr =>
      intro target same; cases target <;> simp [mapRows] at same
      cases ihl same.1; cases ihr same.2; rfl
  | inter left right ihl ihr =>
      intro target same; cases target <;> simp [mapRows] at same
      cases ihl same.1; cases ihr same.2; rfl
  | pair left right ihl ihr =>
      intro target same; cases target <;> simp [mapRows] at same
      cases ihl same.1; cases ihr same.2; rfl
  | emptyRecord =>
      intro target same; cases target <;> simp [mapRows] at same
      rfl
  | record label value rest ihv ihr =>
      intro target same; cases target <;> simp [mapRows] at same
      cases same.1; cases ihv same.2.1; cases ihr same.2.2; rfl
  | variant label value ih =>
      intro target same; cases target <;> simp [mapRows] at same
      cases same.1; cases ih same.2; rfl
  | arrow input inputRow output outputRow ihi iho =>
      intro target same
      cases target <;> simp [mapRows] at same
      cases ihi same.1; cases injective same.2.1
      cases iho same.2.2.1; cases injective same.2.2.2; rfl

theorem subtype_map (f : A → B) {leA : A → A → Prop} {leB : B → B → Prop}
    (monotone : ∀ {left right}, leA left right → leB (f left) (f right))
    {source target : Ty A} (subtype : Subtype leA source target) :
    Subtype leB (mapRows f source) (mapRows f target) := by
  induction subtype with
  | refl => exact .refl _
  | trans _ _ ihl ihr => exact .trans ihl ihr
  | bottom => exact .bottom _
  | top => exact .top _
  | unionLeft => exact .unionLeft _ _
  | unionRight => exact .unionRight _ _
  | unionElim _ _ ihl ihr => exact .unionElim ihl ihr
  | interLeft => exact .interLeft _ _
  | interRight => exact .interRight _ _
  | interIntro _ _ ihl ihr => exact .interIntro ihl ihr
  | pair _ _ ihl ihr => exact .pair ihl ihr
  | variant _ ih => exact .variant ih
  | arrow _ rowIn _ rowOut ihi iho =>
      exact .arrow ihi (monotone rowIn) iho (monotone rowOut)
  | @record source target sourceShape targetShape fields comparisons ih =>
      apply Subtype.record ((mapRows_isRecord f source).mpr sourceShape)
        ((mapRows_isRecord f target).mpr targetShape)
      · intro label expected expectedFound
        obtain ⟨original, found, _⟩ := (mapRows_lookup_some f target label expected).mp expectedFound
        obtain ⟨actual, actualFound⟩ := fields label original found
        exact ⟨mapRows f actual, by simp [mapRows_lookup, actualFound]⟩
      · intro label actual expected actualFound expectedFound
        obtain ⟨a, ha, rfl⟩ := (mapRows_lookup_some f source label actual).mp actualFound
        obtain ⟨b, hb, rfl⟩ := (mapRows_lookup_some f target label expected).mp expectedFound
        exact ih label a b ha hb

theorem comparison_unmap (f : A → B) (injective : Function.Injective f)
    {leA : A → A → Prop} {leB : B → B → Prop}
    (reflects : ∀ {left right}, leB (f left) (f right) → leA left right)
    {mappedSource mappedTarget : Ty B} (comparison : Comparison leB mappedSource mappedTarget) :
    ∀ source target : Ty A, mapRows f source = mappedSource → mapRows f target = mappedTarget →
      Comparison leA source target := by
  induction comparison with
  | refl =>
      intro source target first second
      have same := mapRows_injective f injective (first.trans second.symm)
      cases same
      exact .refl _
  | bottom =>
      intro source target first second
      cases source <;> simp only [mapRows] at first <;> cases first
      exact .bottom _
  | top =>
      intro source target first second
      cases target <;> simp only [mapRows] at second <;> cases second
      exact .top _
  | unionElim _ _ ihl ihr =>
      intro source target first second
      cases source <;> simp only [mapRows] at first <;> cases first
      exact .unionElim (ihl _ target rfl second) (ihr _ target rfl second)
  | interIntro _ _ ihl ihr =>
      intro source target first second
      cases target <;> simp only [mapRows] at second <;> cases second
      exact .interIntro (ihl source _ first rfl) (ihr source _ first rfl)
  | unionLeft _ ih =>
      intro source target first second
      cases target <;> simp only [mapRows] at second <;> cases second
      exact .unionLeft (ih source _ first rfl)
  | unionRight _ ih =>
      intro source target first second
      cases target <;> simp only [mapRows] at second <;> cases second
      exact .unionRight (ih source _ first rfl)
  | interLeft _ ih =>
      intro source target first second
      cases source <;> simp only [mapRows] at first <;> cases first
      exact .interLeft (ih _ target rfl second)
  | interRight _ ih =>
      intro source target first second
      cases source <;> simp only [mapRows] at first <;> cases first
      exact .interRight (ih _ target rfl second)
  | pair _ _ ihl ihr =>
      intro source target first second
      cases source <;> simp only [mapRows] at first <;> cases first
      cases target <;> simp only [mapRows] at second <;> cases second
      exact .pair (ihl _ _ rfl rfl) (ihr _ _ rfl rfl)
  | variant _ ih =>
      intro source target first second
      cases source <;> simp only [mapRows] at first <;> cases first
      cases target <;> simp only [mapRows] at second <;> cases second
      exact .variant (ih _ _ rfl rfl)
  | arrow _ rowIn _ rowOut ihi iho =>
      intro source target first second
      cases source <;> simp only [mapRows] at first <;> cases first
      cases target <;> simp only [mapRows] at second <;> cases second
      exact .arrow (ihi _ _ rfl rfl) (reflects rowIn) (iho _ _ rfl rfl) (reflects rowOut)
  | @record left right sourceShape targetShape fields _ ih =>
      intro source target first second
      subst left right
      apply Comparison.record ((mapRows_isRecord f source).mp sourceShape)
        ((mapRows_isRecord f target).mp targetShape)
      · intro label expected expectedFound
        have mappedFound : (mapRows f target).lookup label = some (mapRows f expected) := by
          simp [mapRows_lookup, expectedFound]
        obtain ⟨actual, actualFound⟩ := fields label _ mappedFound
        obtain ⟨original, found, _⟩ := (mapRows_lookup_some f source label actual).mp actualFound
        exact ⟨original, found⟩
      · intro label actual expected actualFound expectedFound
        apply ih label (mapRows f actual) (mapRows f expected) _ _ actual expected rfl rfl
        · simp [mapRows_lookup, actualFound]
        · simp [mapRows_lookup, expectedFound]

theorem subtype_map_iff (f : A → B) (injective : Function.Injective f)
    {leA : A → A → Prop} {leB : B → B → Prop}
    (rowExact : ∀ left right, leA left right ↔ leB (f left) (f right))
    (rowTrans : ∀ {a b c}, leB a b → leB b c → leB a c)
    (source target : Ty A) :
    Subtype leA source target ↔ Subtype leB (mapRows f source) (mapRows f target) := by
  constructor
  · exact subtype_map f (fun h => (rowExact _ _).mp h)
  · intro subtype
    exact (comparison_unmap f injective (fun h => (rowExact _ _).mpr h)
      (Comparison.complete (leRow := leB) rowTrans subtype) source target rfl rfl).sound

end Yulang.StructuralRowResolution
