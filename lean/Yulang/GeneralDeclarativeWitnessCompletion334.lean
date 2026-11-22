import Yulang.GeneralDeclarativeWitnessCut334
import Yulang.GeneralDeclarativeWitnessStopped334

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeWitnessCompletion334
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessCutDecl334
open GeneralDeclarativeWitnessCutBody334
open GeneralDeclarativeWitnessCutRank334 (safe)
open GeneralDeclarativeWitnessCut334 (waiting unchanged_bounds no_arguments)
open GeneralDeclarativeOrigins321 (Supported Origin restriction backed_iff)
open GeneralDeclarativeHead320 (Equation Models)
open GeneralDeclarativeLowerKnown321 (Ready alias_refl)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativeGrowth327 (Extends fits trans)
open GeneralDeclarativeObserverGrowth330 (sources_grow trace)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeInlineGrowth331 (extend)
open GeneralDeclarativeArityPlan330 (grow)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeWitnessHead334 (Slice CurrentArgument)
open GeneralDeclarativeWitnessNode334 (Witness)
open GeneralDeclarativeWitnessClassify334 (Rule dictionary_sound)
open GeneralDeclarativeCurrentReceipt330 (literal)
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarationExamples (constructors)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeEvidence320 (Evidence)
open CommonRoleOutermostResolver (All₂ Classify Dictionary)

/-- Change completion only, not the equations, intervals or origin map. -/
def view (done : Nat → Prop) : Supported final done where
  derivesFrom := support.derivesFrom
  ordinary := support.ordinary

def earlier (done : Nat → Prop) : Supported initial done where
  derivesFrom := support.derivesFrom
  ordinary := by
    rintro e o (plain|output)
    · exact List.mem_append_left _ plain.1
    · cases output.1
      exact List.mem_append_right _ List.mem_cons_self

theorem grown : Extends initial final :=
  trans (GeneralDeclarativeGrowth327.facts _ _)
    (trans folded.preserve.grows (GeneralDeclarativeGrowth327.facts _ _))

def slice (done : Nat → Prop) : Slice (view done) :=
  ⟨initial,earlier done,grown,sources_grow _ grown⟩

theorem allowed {done : Nat → Prop} {e : Equation} (member : e ∈ knownRows) :
    e ∈ (restriction (view done)).equations :=
  (backed_iff _ _).mpr ⟨.source,.inl ⟨member,rfl⟩,.source⟩

theorem source_head {done : Nat → Prop} :
    HeadMatches (restriction (view done)) constructors interpretation root impl := by
  refine .cons ⟨unchanged_bounds,wanted,[⟨0,.lower,3⟩,⟨1,.lower,4⟩],[⟨0,.upper,3⟩,⟨1,.upper,4⟩],normal,?_,?_⟩ .nil
  · exact .record (alias_refl _) (allowed List.mem_cons_self) .capture .capture
  · exact .record (alias_refl _) (allowed (List.mem_cons_of_mem _ List.mem_cons_self)) .capture .capture

theorem choice {done : Nat → Prop} :
    Elected final registry interpretation (view done) (candidates (view done) registry interpretation waiting) root impl := by
  have read : Ready (view done) root := by
    intro cap there; cases List.mem_singleton.mp there
    exact ⟨_,lo,allowed List.mem_cons_self,alias_refl _,rfl⟩
  refine ⟨read,safe _,fun ⟨_,_,no⟩ => no,⟨⟨List.mem_cons_self,rfl⟩,.inl source_head⟩,?_⟩
  intro other meets
  cases List.mem_singleton.mp meets.1.1
  rfl

def backedAfter {done : Nat → Prop} (completed : done 100) :
    Witness (view done) registry interpretation waiting root impl [] where
  chosen := choice
  slice := slice done
  protect := keep
  fallback := fallback
  targets := targets
  named := initial
  spans := spans
  source := .cons (.named ⟨bounds,wanted,[⟨0,.actual,3⟩,⟨1,.actual,4⟩],normal,
    .record (alias_refl _) ((backed_iff (earlier done) opaqueCenter).mpr ⟨.output 100,Or.inr ⟨rfl,rfl⟩,.completed completed⟩)
      .capture .capture,.cons ⟨rfl,rfl,point_bounded initial 3⟩
        (.cons ⟨rfl,rfl,point_bounded initial 4⟩ .nil)⟩) .nil
  ordinary := final
  compiled := literal_write
  receipt := literal (GeneralDeclarativeClauseBatch327.reflexive _)

theorem before_back {done : Nat → Prop} (before : ¬done 100) :
    Extends (restriction (view done)) (restriction support) := by
  refine ⟨fun _ h => h,fun _ h => h,?_⟩
  intro e seen
  obtain ⟨o,why,now⟩ := (backed_iff _ _).mp seen
  rcases why with original|delayed
  · exact exact_supported.mpr original.1
  · rw [delayed.2] at now
    cases now with
    | completed h => exact (before h).elim

theorem transport_head {done : Nat → Prop} (before : ¬done 100)
    (k : CurrentArgument (view done) constructors interpretation cap pat) :
    CurrentArgument support constructors interpretation cap pat := by
  obtain ⟨fit,shape⟩ := k
  refine ⟨fit,?_⟩
  rcases shape with ⟨code,uses,translated,h⟩|⟨code,uses,translated,h⟩|⟨plan,translated,h⟩
  · exact .inl ⟨code,uses,translated,trace (before_back before) h⟩
  · exact .inr (.inl ⟨code,uses,translated,extend (before_back before) h⟩)
  · exact .inr (.inr ⟨plan,translated,grow (before_back before) h⟩)

theorem actual_selected_before {done : Nat → Prop} (before : ¬done 100) :
    ¬Rule (view done) registry interpretation waiting root (.selected key kids) := by
  intro h
  obtain ⟨actual,_,⟨w⟩⟩ := GeneralDeclarativeWitnessClassify334.selected_witness h
  cases List.mem_singleton.mp w.chosen.viable.1.1
  have found := GeneralDeclarativeWitnessHead334.current_heads w.slice w.source
  cases found with
  | cons here _ => exact GeneralDeclarativeWitnessCut334.no_current (transport_head before here)

/-- The old selector's one-sided mismatch is caused by exactly the
support gate in this fixture: completion of the recorded owner allows
the same ordinary row and exact compiler output, with no state change. -/
theorem exactly_completed (done : Nat → Prop) :
    Rule (view done) registry interpretation waiting root (.selected impl.id []) ↔ done 100 := by
  constructor
  · intro picked
    apply Classical.byContradiction
    intro no
    exact actual_selected_before no picked
  · intro ok
    exact .selected (backedAfter ok)

theorem actually_pending_before {done : Nat → Prop} (before : ¬done 100) :
    Rule (view done) registry interpretation waiting root .pending := by
  apply Rule.unread choice
  intro seen
  cases seen with
  | cons named _ => exact GeneralDeclarativeWitnessCut334.no_current (transport_head before named)

theorem never_pending_after {done : Nat → Prop} (completed : done 100) :
    ¬Rule (view done) registry interpretation waiting root .pending := by
  intro h
  have chosen := choice (done := done)
  cases h with
  | existing prior =>
    cases prior with
    | unsupported delayed _ => exact ((GeneralDeclarativeLowerKnown321.ready_iff_not_delayed _ _).mp chosen.ready) delayed
    | unresolved _ _ blocked => exact chosen.clear blocked
  | unread candidate absent =>
    have visible := candidate.viable.1.1
    cases List.mem_singleton.mp visible
    exact absent (GeneralDeclarativeWitnessHead334.current_heads
      (backedAfter completed).slice (backedAfter completed).source)

theorem pending_iff_incomplete (done : Nat → Prop) :
    Rule (view done) registry interpretation waiting root .pending ↔ ¬done 100 :=
  ⟨fun prior complete => never_pending_after complete prior,actually_pending_before⟩

theorem actual_dictionary_after {done : Nat → Prop} (completed : done 100) :
    Classify (Rule (view done) registry interpretation waiting) root (.selected (.node impl.id [])) ∧
      ∃ m, Models final m ∧ Evidence registry interpretation m root (.node impl.id []) := by
  have picked := (exactly_completed done).mpr completed
  have tree := (show Classify (Rule (view done) registry interpretation waiting) root (.selected (.node impl.id [])) from
    ⟨.selected impl.id [],.selected picked .nil,.selected .nil (.selected rfl)⟩)
  obtain ⟨m,valid⟩ := has_model
  exact ⟨tree,m,valid,dictionary_sound checked covered declared tree m valid⟩

end Yulang.GeneralDeclarativeWitnessCompletion334
