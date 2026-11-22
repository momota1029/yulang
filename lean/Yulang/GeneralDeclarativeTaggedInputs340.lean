import Yulang.GeneralDeclarativeTaggedWhole340
import Yulang.GeneralDeclarativeExactDictionary337

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTaggedInputs340
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeTaggedSources340 (BoundsRead prefers_no_split)
open GeneralDeclarativeTaggedPatch340 (captured)
open GeneralDeclarativeTaggedWhole340 (fullState copied existing_head)
open GeneralDeclarativeStableReads329 (names_one)
open GeneralDeclarativeObserverGrowth330 (preserve sources_grow)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeExactOverlay337 (Holds)
open GeneralDeclarativeEndpointInput336 (LocalShape shape_grows)
open GeneralDeclarativeExactDictionary337 (Observed)
open GeneralDeclarativeGrowth327 (Extends trans fits)
open GeneralDeclarativeEqualities322 (semantic)
open GeneralCandidateInspection (plainNames)
open GeneralDeclarationPatterns (Pattern Constructors normalize normalizeArgs variablesArgs)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (translate)
open CommonRoleOutermostResolver (All₂)

/-- Extend the existing ordered input producer without replacing its
named/inline/approved-record branches or its ordinary output compiler. -/
inductive Input {s : State} (p : Supported s done) (c : Constructors) (i : Interpretation)
    (keep : List Nat) : State → Capture → Pattern → State → List (Nat × Capture) → List Entry → Prop where
  | prior : GeneralDeclarativeEndpointInput336.Input p c i keep before a pat after used reads →
      Input p c i keep before a pat after used reads
  | whole : BoundsRead p a tag low high →
      normalize pat = .variant tag payload →
      plainNames payload = some names →
      translate c i payload = some code →
      Input p c i keep before a pat (fullState before a tag low high keep code)
        (copied (captured before a tag low high keep) names) []

inductive Inputs {s : State} (p : Supported s done) (c : Constructors) (i : Interpretation)
    (keep : List Nat) : State → List Capture → List Pattern → State → List (Nat × Capture) → List Entry → Prop where
  | nil : Inputs p c i keep before [] [] before [] []
  | cons : Input p c i keep before a pat step first own →
      Inputs p c i keep step as pats after more history →
      Inputs p c i keep before (a::as) (pat::pats) after (first++more) (own++history)

theorem pull {s : State} {p : Supported s done} (seen : BoundsRead p a tag low high)
    (prior : Extends s before) : BoundsRead (preserve p prior) a tag low high :=
  ⟨fits prior seen.interval,prefers_no_split seen.lower (sources_grow p prior),
    prefers_no_split seen.upper (sources_grow p prior)⟩

theorem one {s : State} {p : Supported s done} (observed : Input p c i keep before a pat after used reads)
    (old : Extends s before) :
    Extends before after ∧ LocalShape (s := after) c i a pat used reads ∧
      (∀ slot ∈ used, Bounds after slot.2) ∧ used.map Prod.fst = (normalize pat).variables := by
  cases observed with
  | prior former => exact GeneralDeclarativeEndpointInput336.input former old
  | whole seen normalized plain translated =>
    obtain ⟨step,head,ranges⟩ := existing_head (pull seen old) keep normalized plain translated
    obtain ⟨code,form,printed,actual,walk⟩ := head.actual
    exact ⟨step.grows,⟨head.fits,.inl ⟨form,code,printed,actual,walk,rfl⟩⟩,ranges,names_one head⟩

theorem complete {s : State} {p : Supported s done}
    (observed : Inputs p c i keep before as pats after used reads) (old : Extends s before) :
    Extends before after ∧ (∀ slot ∈ used, Bounds after slot.2) ∧
      used.map Prod.fst = variablesArgs (normalizeArgs pats) := by
  induction observed with
  | nil => exact ⟨GeneralDeclarativeClauseBatch327.reflexive _,fun _ h => False.elim (List.not_mem_nil h),rfl⟩
  | cons first _ ih =>
    obtain ⟨step,_,here,ordered⟩ := one first old
    obtain ⟨last,more,rest⟩ := ih (trans old step)
    exact ⟨trans step last,fun _ h => (List.mem_append.mp h).elim (fun u => fits last (here _ u)) (more _),
      by simp only [List.map_append,ordered,rest,normalizeArgs,variablesArgs]⟩

theorem observed {s : State} {p : Supported s done} (inputs : Inputs p c i keep before as pats after used reads)
    (old : Extends s before) (current : Extends after t) (m) (fit : Models t m)
    (exactRows : ∀ e ∈ reads, Holds m e) : All₂ (Observed c i m) as pats := by
  induction inputs with
  | nil => exact .nil
  | cons first later ih =>
    obtain ⟨step,formed,_,_⟩ := one first old
    have remaining := (complete later (trans old step)).1
    have active := shape_grows (trans remaining current) formed
    refine .cons ?_ (ih (trans old step) current (fun e present => exactRows e (List.mem_append_right _ present)))
    rcases active.form with ⟨target,code,printed,currentShape,walk,_⟩|record
    · exact .literal (bounds_sound active.range m fit) printed (semantic currentShape m fit) walk
    · exact .record (bounds_sound active.range m fit) record
        (fun e present => exactRows e (List.mem_append_left _ present))

end Yulang.GeneralDeclarativeTaggedInputs340
