import Yulang.CommonCaseShapeChecks

/-! Complete finite cells for records with specified required fields and
arbitrary extra fields. Repeated specification labels are retained: the
finite product is filtered by every requirement, using first-match lookup.
Actual records need not have unique labels or follow specification order. -/

namespace Yulang.CommonCaseRecordCells

open CaseValues (Value Bindings lookup)
open CommonCaseBaseCells (Shape InShape ValueEquivalent)

abbrev Specification := List (Nat × Shape)

def Domain (specification : Specification) (actual : Bindings Empty) : Prop :=
  ∀ entry ∈ specification, ∃ value, lookup entry.1 actual = some value ∧ InShape entry.2 value

def checkDomain (specification : Specification) (actual : Bindings Empty) : Bool :=
  specification.all fun entry => match lookup entry.1 actual with
    | none => false
    | some value => CommonCaseShapeChecks.check entry.2 value

theorem checkDomain_exact (specification : Specification) (actual : Bindings Empty) :
    checkDomain specification actual = true ↔ Domain specification actual := by
  constructor
  · intro checked entry member
    have tested := List.all_eq_true.mp checked entry member
    cases found : lookup entry.1 actual with
    | none => simp only [found, Bool.false_eq_true] at tested
    | some value =>
        exact ⟨value, rfl, (CommonCaseShapeChecks.check_exact _ _).mp (by simpa only [found] using tested)⟩
  · intro valid
    apply List.all_eq_true.mpr
    intro entry member
    obtain ⟨value, found, typed⟩ := valid entry member
    simpa only [found] using (CommonCaseShapeChecks.check_exact _ _).mpr typed

inductive EntriesRelated (bounds : List Int) (texts : List String) (actual : Bindings Empty) :
    Specification → Bindings Empty → Prop where
  | nil : EntriesRelated bounds texts actual [] []
  | cons : lookup name actual = some original → ValueEquivalent bounds texts sample original →
      EntriesRelated bounds texts actual specification samples →
      EntriesRelated bounds texts actual ((name, shape) :: specification) ((name, sample) :: samples)

theorem EntriesRelated.lookup_related (related : EntriesRelated bounds texts actual specification samples)
    (name : Nat) (member : name ∈ specification.map Prod.fst) :
    ∃ sample original, lookup name samples = some sample ∧ lookup name actual = some original ∧
      ValueEquivalent bounds texts sample original := by
  induction related with
  | nil => cases member
  | @cons label original sample rest generated shape found same tail ih =>
      by_cases atHead : name = label
      · subst name
        exact ⟨sample, original, by simp only [lookup, ↓reduceIte], found, same⟩
      · have later : name ∈ rest.map Prod.fst := by
          simp only [List.map_cons, List.mem_cons] at member
          exact member.resolve_left atHead
        obtain ⟨item, initial, inSamples, inActual, equivalent⟩ := ih later
        exact ⟨item, initial, by simpa only [lookup, atHead, ↓reduceIte] using inSamples, inActual, equivalent⟩

theorem EntriesRelated.domain (related : EntriesRelated bounds texts actual specification samples)
    (valid : Domain specification actual) : Domain specification samples := by
  intro entry member
  obtain ⟨original, found, typed⟩ := valid entry member
  obtain ⟨sample, initial, sampleFound, initialFound, same⟩ := related.lookup_related entry.1 (List.mem_map_of_mem member)
  have equal : initial = original := Option.some.inj (initialFound.symm.trans found)
  subst initial
  exact ⟨sample, sampleFound, (CommonCaseShapeChecks.shape_iff same).mpr typed⟩

def rawRepresentatives (bounds : List Int) (texts : List String) : Specification → List (Bindings Empty)
  | [] => [[]]
  | (name, shape) :: rest => (CommonCaseBaseCells.representatives bounds texts shape).flatMap fun value =>
      (rawRepresentatives bounds texts rest).map fun tail => (name, value) :: tail

theorem raw_complete (bounds : List Int) (texts : List String) (specification : Specification)
    (actual : Bindings Empty) (valid : Domain specification actual) :
    ∃ samples ∈ rawRepresentatives bounds texts specification, EntriesRelated bounds texts actual specification samples := by
  induction specification with
  | nil => exact ⟨[], List.mem_cons_self, .nil⟩
  | cons entry rest ih =>
      rcases entry with ⟨name, shape⟩
      obtain ⟨original, found, typed⟩ := valid (name, shape) List.mem_cons_self
      obtain ⟨sample, member, same⟩ := CommonCaseBaseCells.representative_complete bounds texts typed
      obtain ⟨samples, samplesMember, tail⟩ := ih (fun entry member => valid entry (List.mem_cons_of_mem _ member))
      exact ⟨(name, sample) :: samples,
        List.mem_flatMap.mpr ⟨sample, member, List.mem_map.mpr ⟨samples, samplesMember, rfl⟩⟩,
        .cons found same tail⟩

def representatives (bounds : List Int) (texts : List String) (specification : Specification) : List (Bindings Empty) :=
  (rawRepresentatives bounds texts specification).filter (checkDomain specification)

theorem representatives_sound (bounds : List Int) (texts : List String) (specification : Specification)
    (samples : Bindings Empty) (member : samples ∈ representatives bounds texts specification) : Domain specification samples :=
  (checkDomain_exact specification samples).mp (List.mem_filter.mp member).2

/-- Every real record in the domain, with arbitrary extra/duplicate fields,
has a finite representative preserving every declared first lookup. The
relation describes declared lookups up to cell equivalence. Full raw-record
or returned-payload identity is a separate matching interface. -/
theorem representative_complete (bounds : List Int) (texts : List String) (specification : Specification)
    (actual : Bindings Empty) (valid : Domain specification actual) :
    ∃ samples ∈ representatives bounds texts specification, EntriesRelated bounds texts actual specification samples := by
  obtain ⟨samples, member, related⟩ := raw_complete bounds texts specification actual valid
  exact ⟨samples, List.mem_filter.mpr ⟨member, (checkDomain_exact specification samples).mpr (related.domain valid)⟩, related⟩

end Yulang.CommonCaseRecordCells
