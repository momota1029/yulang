import Yulang.GeneralDeclarativeAlternativeReadComplete333
import Yulang.GeneralDeclarativeInlineOrigins331
import Yulang.GeneralDeclarativeNestedOpaque332

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 10000000
namespace C333PhaseReuse
open Yulang
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeInlineOrigins331 (Requirement fromOrigins complete exact_uses)
open GeneralDeclarativeAlternativeView333 (ofTable Index)
open GeneralDeclarativeAlternativeNeeds333 (Need Eventually finiteIndex)
open GeneralDeclarativeAlternativeRead333 (normalized)
open GeneralDeclarativeAlternativeReadComplete333 (normalized_finite)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralDeclarationPatterns (normalize)

/-- The new finite packet is reconstructed under exactly the old
authorized origin requirements. Models and alternative spellings
cannot fill an incomplete owner, and this makes no claim about
which candidate the later state elects. -/
theorem across_support_phase {s : State} {p : Supported s done}
    (printed : translate c i (normalize pat) = some code)
    (witness : Read (restriction p) mode raw code seen) :
    ∃ uses : List Requirement, fromOrigins p uses ∧ complete done uses ∧
      ∀ (t : State) {later : Nat → Prop} (q : Supported t later), s.normal = t.normal →
      fromOrigins q uses → complete later uses →
        ∃ packet : List (Need (restriction q)), Eventually (fun depth =>
          seen ∈ normalized (finiteIndex packet) depth c i mode raw pat) := by
  obtain ⟨authority,original,active,rebuild⟩ := exact_uses witness
  exact ⟨authority,original,active,fun t {later} (q : Supported t later) normals valid completed =>
    normalized_finite printed (rebuild t q normals valid completed)⟩

open GeneralDeclarativeNestedOpaque332 (state support visible backed exactStop model ordinary_unchanged)
open GeneralDeclarativeAlternativeSpine333 (spines)

noncomputable def exampleIndex (first last : Bool) : Index (restriction (support first last)) :=
  ofTable (visible first last) (backed first last) []

/-- Both independently recorded owners must be complete for the
actual named residual. This checks the new *alternative* spine table,
not a deterministic supplied path and not a diagnostic rule. -/
theorem exactly_available (first last : Bool) :
    (spines (exampleIndex first last) 20 2).map Subtype.val =
      if first && last then [([(8,.variable 12)],exactStop)] else [] := by
  cases first <;> cases last <;> rfl

theorem unchanged_ordinary_state : Models state model := ordinary_unchanged

#print axioms across_support_phase
#print axioms exactly_available
#print axioms unchanged_ordinary_state
end C333PhaseReuse
