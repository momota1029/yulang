import Yulang.GeneralDeclarativeI65AuthoredPrefix368
import Yulang.GeneralDeclarativeWitnessOrigins350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeOrigins321 (Backed)
open GeneralDeclarativeWitnessOrigins350 (Table Attached support)
open GeneralDeclarativeK2Graph321 (View Shape)
open GeneralDeclarativeGraphRows321 (shapeOf structural)
open GeneralDeclarativeHead320 (Equation)
abbrev SourceLabel := GeneralDeclarativeOrigins321.Origin

/-- Independent lineage of actual normalized edges, not the solver's
whole unfiltered normal form. This does not construct the source
lineage table from arbitrary ordinary rows. -/
structure TaggedNormal where
  atoms : List (PresenceNormalForm.Atom Nat × SourceLabel)
  intervals : List ((Nat × Nat) × SourceLabel)

structure NormalAttached (s : GeneralDeclarativeWhere319.State) (n : TaggedNormal) : Prop where
  atoms : ∀ row ∈ n.atoms, row.1 ∈ s.ordinary
  intervals : ∀ row ∈ n.intervals, row.1 ∈ s.intervals

def releasedSource (released : List Nat) : SourceLabel → Bool
  | .source => true
  | .output owner => released.contains owner

def supportedEntries {α : Type} (released : List Nat) (xs : List (α × SourceLabel)) : List α :=
  (xs.filter fun row => releasedSource released row.2).map Prod.fst

def supportedNormal (n : TaggedNormal) (released : List Nat) : GeneralDeclarativeWhere319.State :=
  ⟨supportedEntries released n.atoms,supportedEntries released n.intervals⟩

theorem supported_entry_origin {α : Type} {released : List Nat} {rows : List (α × SourceLabel)} {a : α} :
    a ∈ supportedEntries released rows ↔
      ∃ o, (a,o) ∈ rows ∧ GeneralDeclarativeOrigins321.Available (· ∈ released) o := by
  constructor
  · intro present
    obtain ⟨⟨b,o⟩,listed,equal⟩ := List.mem_map.mp present
    change b = a at equal
    subst b
    obtain ⟨row,ready⟩ := List.mem_filter.mp listed
    refine ⟨o,row,?_⟩
    cases o with
    | source => exact .source
    | output owner => exact .completed (by simpa [releasedSource] using ready)
  · rintro ⟨o,listed,ready⟩
    refine List.mem_map.mpr ⟨(a,o),List.mem_filter.mpr ⟨listed,?_⟩,rfl⟩
    cases ready with
    | source => rfl
    | completed h => simpa [releasedSource] using h

theorem backed_bound_is_ordinary {s : GeneralDeclarativeWhere319.State} {n : TaggedNormal}
    (attached : NormalAttached s n) {released : List Nat} {a b : Nat}
    (reads : Bound (supportedNormal n released) a b) : Bound s a b := by
  induction reads with
  | interval h =>
    obtain ⟨o,listed,ready⟩ := (supported_entry_origin (released := released) (rows := n.intervals)).mp h
    exact .interval (attached.intervals (_,o) listed)
  | constraint h =>
    obtain ⟨o,listed,ready⟩ := (supported_entry_origin (released := released) (rows := n.atoms)).mp h
    exact .constraint (attached.atoms (_,o) listed)
  | refl x => exact .refl x
  | trans _ _ first last => exact .trans first last

inductive AuthorizedAlias {s : GeneralDeclarativeHead320.State} {t : Table}
    (a : Attached s t) (n : TaggedNormal) : Nat → Nat → Prop where
  | written : BackAlias (support a) left right → AuthorizedAlias a n left right
  | normalized : Bound (supportedNormal n t.released) left right →
      Bound (supportedNormal n t.released) right left → AuthorizedAlias a n left right
  | next : AuthorizedAlias a n x y → AuthorizedAlias a n y z → AuthorizedAlias a n x z

theorem authorized_alias_to_ordinary {s : GeneralDeclarativeHead320.State} {t : Table}
    {a : Attached s t} {n : TaggedNormal} (verified : NormalAttached s.normal n)
    {left right : Nat} (link : AuthorizedAlias a n left right) :
    GeneralDeclarativeLowerKnown321.Alias s left right := by
  induction link with
  | written read => exact backed_alias_is_ordinary read
  | normalized there back =>
    exact .bounds (backed_bound_is_ordinary verified there) (backed_bound_is_ordinary verified back)
  | next _ _ x y => exact .trans x y

def verifiedSourceView {s : GeneralDeclarativeHead320.State} {t : Table}
    (a : Attached s t) (n : TaggedNormal) : View :=
  fun root shape => ∃ source expr, AuthorizedAlias a n root source ∧
    Backed (support a) (⟨source,expr⟩ : Equation) ∧ shapeOf expr = some shape

theorem verified_source_view_to_ordinary {s : GeneralDeclarativeHead320.State} {t : Table}
    {a : Attached s t} {n : TaggedNormal} (verified : NormalAttached s.normal n)
    {root : Nat} {shape : Shape} (read : verifiedSourceView a n root shape) :
    structural s root shape := by
  obtain ⟨source,expr,alias,⟨_,routed,_⟩,plain⟩ := read
  exact ⟨source,authorized_alias_to_ordinary verified alias,expr,(support a).ordinary routed,plain⟩

end Yulang.GeneralDeclarativeI65
