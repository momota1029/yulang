import Yulang.GeneralFiniteWitnessSupport244
namespace Yulang.GeneralFiniteWitnessReadback244
open GeneralFiniteWitnessSupport244
variable {Name Value : Type}

def Reads (readback : Assignment Name Value → Assignment Name Value) (sources : Name → List Name) : Prop :=
 ∀ name first last, Agree (sources name) first last → readback first name = readback last name

theorem readback_agree (reads : Reads readback sources)
 (same : Agree (names.flatMap sources) first last) : Agree names (readback first) (readback last) := by
 intro name member
 apply reads name
 intro source present
 exact same source (List.mem_flatMap.mpr ⟨name,member,present⟩)

theorem supports_readback (reads : Reads readback sources) (support : Supports names predicate) :
 Supports (names.flatMap sources) (fun model => predicate (readback model)) := by
 intro first last same
 exact support _ _ (readback_agree reads same)

theorem supportedAt_readback (reads : Reads readback sources)
 (supported : SupportedAt predicate (readback model)) :
 SupportedAt (fun next => predicate (readback next)) model := by
 obtain ⟨names,kept⟩ := supported
 exact ⟨names.flatMap sources,fun next same => kept _ (readback_agree reads same)⟩

theorem reads_compose (outerReads : Reads outer outerSources) (innerReads : Reads inner innerSources) :
 Reads (fun model => outer (inner model)) (fun name => (outerSources name).flatMap innerSources) := by
 intro name first last same
 exact outerReads name _ _ (readback_agree innerReads same)

theorem supports_bounded_exists (items : List α) (predicate : α → Assignment Name Value → Prop)
 (sources : α → List Name) (supports : ∀ item ∈ items, Supports (sources item) (predicate item)) :
 Supports (items.flatMap sources) (fun model => ∃ item ∈ items, predicate item model) := by
 intro first last same
 have kept (item) (member : item ∈ items) := supports item member first last
   (fun name present => same name (List.mem_flatMap.mpr ⟨item,member,present⟩))
 constructor
 · rintro ⟨item,member,valid⟩; exact ⟨item,member,(kept item member).mp valid⟩
 · rintro ⟨item,member,valid⟩; exact ⟨item,member,(kept item member).mpr valid⟩

theorem supports_bounded_forall (items : List α) (predicate : α → Assignment Name Value → Prop)
 (sources : α → List Name) (supports : ∀ item ∈ items, Supports (sources item) (predicate item)) :
 Supports (items.flatMap sources) (fun model => ∀ item ∈ items, predicate item model) := by
 intro first last same
 apply forall_congr'; intro item
 apply forall_congr'; intro member
 exact supports item member first last
   (fun name present => same name (List.mem_flatMap.mpr ⟨item,member,present⟩))

def write [DecidableEq Name] (names : List Name) (values model : Assignment Name Value) : Assignment Name Value :=
 fun name => if name ∈ names then values name else model name

theorem write_preserves [DecidableEq Name] (names : List Name) (values model : Assignment Name Value) :
 Preserves names (write names values model) model := by
 intro name outside
 simp [write,outside]

theorem write_keeps_supported [DecidableEq Name] (support : Supports reads predicate)
 (checked : check writes reads = true) (values model : Assignment Name Value) :
 predicate (write writes values model) ↔ predicate model :=
 checked_preserves support ((check_iff writes reads).mp checked) (write_preserves writes values model)

theorem witness_write [DecidableEq Name] {predicate : Assignment Name Value → Prop} {model : Assignment Name Value} (given : SupportedAt predicate model) :
 ∃ reads, ∀ writes values, check writes reads = true → predicate (write writes values model) := by
 obtain ⟨reads,kept⟩ := given
 exact ⟨reads,fun writes values checked => kept _
   (checked_agree ((check_iff writes reads).mp checked) (write_preserves writes values model))⟩

/-- A finite certificate family supplies a uniform set. The bound on candidates
is a genuine separate premise, unlike support for one existing witness. -/
theorem bounded_family_write [DecidableEq Name] (items : List α)
 (predicate : α → Assignment Name Value → Prop) (sources : α → List Name)
 (supports : ∀ item ∈ items, Supports (sources item) (predicate item))
 (checked : check writes (items.flatMap sources) = true) (values model : Assignment Name Value) :
 (∃ item ∈ items, predicate item (write writes values model)) ↔ ∃ item ∈ items, predicate item model :=
 write_keeps_supported (supports_bounded_exists items predicate sources supports) checked values model
end Yulang.GeneralFiniteWitnessReadback244
