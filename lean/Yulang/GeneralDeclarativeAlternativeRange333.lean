import Yulang.GeneralDeclarativeAlternativeCapture333
import Yulang.GeneralDeclarativeInlineIntervals331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAlternativeRange333
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeGrowth327 (Extends fits)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeInlineIntervals331 (Existing captureWith fixed_centers kept_ranges)
open GeneralDeclarativeInlineMaterial331 (seed)
open GeneralDeclarativeInlineAllocation331 (captures renamed)
open GeneralDeclarativeNestedRebuild332 (rebuild)
open GeneralDeclarativeNestedMaterial332 (assemble assemble_exact computed_frame)
open GeneralDeclarativeStableReads329 (One)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeOpaqueConserve328 (Retains)

abbrev KnownAt (s : State) (n : Nat) :=
  { cap : Capture // cap.center = n ∧ Bounds s cap }

abbrev Known (s : State) := ∀ n, Option (KnownAt s n)

/-- No endpoint is substituted for the actual name. Known triples carry
current ordinary bound witnesses; otherwise the read supplies just
the original point name. The range view does not read a model. -/
def located (view : Known s) (n : Nat) : Capture :=
  match view n with
  | some saved => saved.val
  | none => point n

theorem located_ok {view : Known s} (n : Nat) :
    (located view n).center = n ∧ Bounds s (located view n) := by
  cases found : view n with
  | none =>
    simp only [located,found]
    exact ⟨rfl,point_bounded s n⟩
  | some info => simpa only [located,found] using info.property

theorem existing {s t : State} (view : Known s) (grows : Extends s t) (uses : List Occurrence) :
    Existing t (located view) uses := by
  intro spot listed n eq
  have located := located_ok (view := view) n
  exact ⟨located.1,fits grows located.2⟩

theorem original_spans {s : State} {used : List Occurrence}
    (checked : assemble s a keep code used = some (out,spans)) :
    spans = captures (seed s a keep used) used := by
  unfold assemble at checked
  cases was : rebuild code (renamed (seed s a keep used) used) with
  | none => simp [was] at checked
  | some got =>
    rcases got with ⟨raw,rest⟩
    cases rest with
    | nil =>
      simp [was] at checked
      exact checked.2.symm
    | cons => simp [was] at checked

theorem reframe {s t : State} {view : Known s}
    (witness : One out c i a pat (captures (seed t a keep used) used))
    (grows : Extends s t) :
    One out c i a pat (captureWith (located view) (seed t a keep used) used) := by
  obtain ⟨fit,head,stored,writes,derives,walk⟩ := witness
  rw [← fixed_centers (existing view grows used)] at walk
  exact ⟨fit,head,stored,writes,derives,walk⟩

def materialize (view : Known s) (current : State) (a : Capture) (keep : List Nat) (code : Expr)
    (used : List Occurrence) : Option (State × List (Nat × Capture)) :=
  (assemble current a keep code used).map fun (out,_) =>
    (out,captureWith (located view) (seed current a keep used) used)

theorem materialize_exact {s t : State} {p : Supported t done} (view : Known s)
    (grows : Extends s t) (bounds : Bounds t a)
    (printed : translate c i (normalize pat) = some code)
    (known : Read (restriction p) .actual (.variable a.center) code used)
    (checked : materialize view t a keep code used = some (out,spans)) :
    Retains t out keep ∧ One out c i a pat spans ∧
      (∀ slot ∈ spans, Bounds out slot.2) := by
  cases raw : assemble t a keep code used with
  | none => simp [materialize,raw] at checked
  | some old =>
    obtain ⟨middle,original⟩ := old
    have ends : (middle,captureWith (located view) (seed t a keep used) used) = (out,spans) := by
      simpa [materialize,raw] using checked
    cases ends
    obtain ⟨retained,src,_,_,_⟩ := computed_frame bounds printed known raw
    rw [original_spans raw] at src
    exact ⟨retained,reframe src grows,kept_ranges retained.grows (existing view grows used) _⟩

theorem materialize_exists {s t : State} {p : Supported t done} (view : Known s)
    (bounds : Bounds t a) (printed : translate c i (normalize pat) = some code)
    (known : Read (restriction p) .actual (.variable a.center) code used) :
    ∃ out spans, materialize view t a keep code used = some (out,spans) := by
  obtain ⟨out,old,ready,_,_,_,_,_⟩ := assemble_exact bounds printed known keep
  exact ⟨out,captureWith (located view) (seed t a keep used) used,by simp [materialize,ready]⟩

end Yulang.GeneralDeclarativeAlternativeRange333
