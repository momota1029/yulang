import Yulang.GeneralDeclarativeWitnessRecordNodes350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTies350
open GeneralDeclarations (Checked)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeTaggedSelected340 (Selected reconstruct)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeStableCanonical329 (EqualUses exact uses_existing)
open GeneralDeclarativeStableAssemble329 (tieState firsts)
open GeneralDeclarativeGrowth327 (Extends restrict)
open GeneralDeclarativeCurrentReceipt330 (relays_models)
open GeneralDeclarativeStableTies329 (rows pairOf)
open GeneralDeclarativeEntailment320 (Holds model_append)
open GeneralNominalCommonBridge (Assignment)

/-- The compiler-derived ordinary prefix, not endpoint observations,
is the source of the actual selected I-58 equalities. The proof is
model-uniform and never treats missing ties as language pending. -/
theorem tied_prefix {s : State} {p : Supported s done}
    (choice : Selected p sidecar r i wait d impl kids)
    (checked : Checked r) (covered : Coverage r i) (declared : Declared r d)
    (m : Assignment) (fit : Models s m) :
    Models (tieState choice.named choice.spans choice.fallback) m := by
  obtain ⟨_,_,_,grows⟩ := reconstruct choice checked covered declared
  exact restrict grows m (relays_models choice.receipt m fit)

theorem repeats {s : State} {p : Supported s done}
    (choice : Selected p sidecar r i wait d impl kids)
    (checked : Checked r) (covered : Coverage r i) (declared : Declared r d)
    (m : Assignment) (fit : Models s m) : EqualUses m choice.spans :=
  ((exact choice.named (firsts choice.spans choice.fallback) choice.spans (uses_existing _ _) m).mp
    (tied_prefix choice checked covered declared m fit)).2

theorem literal_rows {s : State} {p : Supported s done}
    (choice : Selected p sidecar r i wait d impl kids)
    (checked : Checked r) (covered : Coverage r i) (declared : Declared r d)
    (m : Assignment) (fit : Models s m) :
    ∀ pair ∈ rows (firsts choice.spans choice.fallback) (choice.spans.map pairOf), Holds m pair :=
  ((model_append m).mp (tied_prefix choice checked covered declared m fit)).2

end Yulang.GeneralDeclarativeWitnessTies350
