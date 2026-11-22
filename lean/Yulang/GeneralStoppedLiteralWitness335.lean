import Yulang.GeneralStoppedLiteralCompiler335

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralStoppedLiteralWitness335
open GeneralDeclarations (Registry Declaration Clause Checked)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeWitnessHead334 (Slice Actuals actuals_sound)
open GeneralStoppedLiteralCompiler335 (compile exact_frame)
open GeneralDeclarativeCurrentReceipt330 (Receipt complete)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarativeEvidenceFold325 (LocalWitness same_model)
open GeneralDeclarativeEvidence320 (Evidence)
open CommonRoleOutermostResolver (Frontier Classify)

/-- An isolated positive relation for the diagnostic transport test;
not the replacement of C334's Rule. Captures and approved source
support are still required. The only changed component being tested
is preservation of each already available, uniquely bound span. -/
structure Witness {s : State} (p : Supported s done) (r : Registry) (i : Interpretation)
    (waiting : Demand → Declaration → Prop) (d : Demand) (impl : Declaration) (kids : List Demand) where
  chosen : Elected s r i p (candidates p r i waiting) d impl
  slice : Slice p
  keep : List Nat
  fallback : Nat → Capture
  targets : Clause → Nat → Nat
  named : State
  spans : List (Nat × Capture)
  supported : Actuals slice.support r.constructors i keep slice.base d.arguments impl.head named spans
  linear : (spans.map Prod.fst).Nodup
  computed : State
  emitted : compile r i d impl named spans keep fallback targets = some (computed,kids)
  receipt : Receipt computed s

inductive Rule {s : State} (p : Supported s done) (r : Registry) (i : Interpretation)
    (waiting : Demand → Declaration → Prop) : Demand → Frontier Demand → Prop
  | selected : Witness p r i waiting d impl kids → Rule p r i waiting d (.selected impl.id kids)

theorem frame {s : State} {p : Supported s done} (checked : Checked r) (cover : Coverage r i)
    (wanted : Declared r d) (w : Witness p r i waiting d impl kids) :
    Nonempty (Frame w.computed r i d impl kids) := by
  obtain ⟨_,seen,known⟩ := actuals_sound w.supported (GeneralDeclarativeClauseBatch327.reflexive _)
  obtain ⟨out,children,checkedFrame,emitted⟩ :=
    exact_frame checked cover w.chosen.viable.1.1 w.chosen.viable.1.2 wanted
      seen known w.linear w.keep w.fallback w.targets
  cases Option.some.inj (emitted.symm.trans w.emitted)
  exact checkedFrame

theorem local_meaning {s : State} {p : Supported s done} (checked : Checked r) (cover : Coverage r i) :
    LocalWitness r i s (Rule p r i waiting) := by
  intro m fit d declared k cs classified
  cases classified with
  | selected known =>
    obtain ⟨frame⟩ := frame checked cover declared known
    have t := complete checked cover known.chosen.viable.1.1 known.chosen.viable.1.2 declared frame known.receipt
    exact ⟨⟨_,frame.capture,rfl,t.2.1 m fit⟩,t.2.2⟩

theorem sound {s : State} {p : Supported s done} (checked : Checked r) (cover : Coverage r i)
    (wanted : Declared r d) (tree : Classify (Rule p r i waiting) d (.selected dictionary)) :
    ∀ m, Models s m → Evidence r i m d dictionary :=
  fun _m fit => same_model (local_meaning checked cover) fit wanted tree

end Yulang.GeneralStoppedLiteralWitness335
