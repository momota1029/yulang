import Yulang.GeneralDeclarativeWitnessCompletion334

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralStoppedI61Endpoint335
open GeneralDeclarativeHead320 (State Equation Models environment)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeOrigins321 (Supported restriction restrict_models from_source)
open GeneralDeclarativeEntailment320 (appendFacts Holds model_append)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open CommonNominalFullCarrier (Equivalent subtype_trans)

/-- I-61 point-record subcase: the two approved endpoint observations
have exactly the same record RHS, including the residual, and contain
the actual center in the ordinary interval. The center itself is not
looked up. This does not cover distinct endpoint field/tail names or
nonpoint field intervals. -/
structure EqualRecord {s : State} (p : Supported s done) (arg : Capture)
    (label : Nat) (field tail : Expr) : Prop where
  valid : Bounds s arg
  lo : (⟨arg.lower,.record label field tail⟩ : Equation) ∈ (restriction p).equations
  hi : (⟨arg.upper,.record label field tail⟩ : Equation) ∈ (restriction p).equations

theorem center_is_record {s : State} {p : Supported s done}
    (read : EqualRecord p a label field tail) (m) (fit : Models s m) :
    Holds m ⟨a.center,.record label field tail⟩ := by
  have supported := restrict_models p m fit
  have below := supported.2 _ read.lo
  have above := supported.2 _ read.hi
  have interval := bounds_sound read.valid m fit
  exact ⟨subtype_trans interval.2 above.1,subtype_trans below.2 interval.1⟩

theorem present_iff {s : State} {p : Supported s done}
    (read : EqualRecord p a label field tail) (m) :
    Models (appendFacts s [⟨a.center,.record label field tail⟩]) m ↔ Models s m := by
  rw [model_append]
  constructor
  · exact And.left
  · intro fit
    refine ⟨fit,?_⟩
    intro row found
    cases List.mem_singleton.mp found
    exact center_is_record read m fit

/-- An isolated adaptor into the existing witness kernel. The added
row is supported *by the explicit endpoint certificate*, not merely
because it is an ordinary consequence or a previously recorded
unfinished output. Origin.source in the adapter means this verified
projection; it does not claim the parser authored a literal center
row. This is not a replacement for I-61's eventual general Read. -/
def normalize {s : State} {p : Supported s done}
    (_read : EqualRecord p a label field tail) :
    Supported (appendFacts s [⟨a.center,.record label field tail⟩]) done where
  derivesFrom := fun row origin => p.derivesFrom row origin ∨
    (row = ⟨a.center,.record label field tail⟩ ∧ origin = .source)
  ordinary := by
    rintro row _ (earlier|⟨rfl,_⟩)
    · exact List.mem_append_left _ (p.ordinary earlier)
    · exact List.mem_append_right _ List.mem_cons_self

namespace Cut
open GeneralDeclarativeWitnessCutDecl334
open GeneralDeclarativeWitnessCutBody334
open GeneralDeclarativeWitnessCut334 (waiting unchanged_bounds)
open GeneralDeclarativeWitnessCutRank334 (safe)
open GeneralDeclarativeWitnessCompletion334 (grown)
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarationExamples (constructors)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeObserverGrowth330 (preserve sources_grow)
open GeneralDeclarativeLowerKnown321 (Ready knows_row alias_refl)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeWitnessHead334 (Slice)
open GeneralDeclarativeWitnessNode334 (Witness)
open GeneralDeclarativeWitnessClassify334 (Rule dictionary_sound)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralDeclarativeCurrentReceipt330 (literal)
open GeneralDeclarativeClauseBatch327 (reflexive)
open GeneralDeclarativeEvidence320 (Evidence)
open CommonRoleOutermostResolver (Classify)

abbrev noCenter : State := ⟨initial.normal,knownRows⟩

def authored : Supported noCenter (fun _ => False) :=
  ⟨fun e o => e ∈ knownRows ∧ o = .source,fun h => h.1⟩

theorem no_center_present : opaqueCenter ∉ noCenter.equations := by
  intro present
  simp only [knownRows,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with h|h|h|h <;> cases h

theorem endpoints : EqualRecord authored arg 7 (.variable 3) (.variable 4) :=
  ⟨bounds,from_source authored ⟨List.mem_cons_self,rfl⟩,
    from_source authored ⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩⟩

def prepared : Supported initial (fun _ => False) := normalize endpoints

def authorized : Supported final (fun _ => False) := preserve prepared grown

theorem projection_is_conservative (m) : Models initial m ↔ Models noCenter m :=
  present_iff endpoints m

theorem old_lo : lo ∈ (restriction authorized).equations :=
  from_source authorized (.inl ⟨List.mem_cons_self,rfl⟩)

theorem old_hi : hi ∈ (restriction authorized).equations :=
  from_source authorized (.inl ⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩)

theorem supported_center : opaqueCenter ∈ (restriction prepared).equations :=
  from_source prepared (.inr ⟨rfl,rfl⟩)

theorem actual_choice :
    Elected final registry interpretation authorized (candidates authorized registry interpretation waiting) root impl := by
  have ready : Ready authorized root := by
    intro x here; cases List.mem_singleton.mp here
    exact ⟨_,knows_row old_lo rfl⟩
  have headMatches : HeadMatches (restriction authorized) constructors interpretation root impl := by
    refine .cons ⟨unchanged_bounds,wanted,[⟨0,.lower,3⟩,⟨1,.lower,4⟩],[⟨0,.upper,3⟩,⟨1,.upper,4⟩],
      normal,.record (alias_refl _) old_lo .capture .capture,.record (alias_refl _) old_hi .capture .capture⟩ .nil
  refine ⟨ready,safe _,fun ⟨_,_,n⟩ => n,⟨⟨List.mem_cons_self,rfl⟩,.inl headMatches⟩,?_⟩
  intro other viable
  cases List.mem_singleton.mp viable.1.1
  rfl

def selected : Witness authorized registry interpretation waiting root impl [] where
  chosen := actual_choice
  slice := ⟨initial,prepared,grown,sources_grow prepared grown⟩
  protect := keep
  fallback := fallback
  targets := targets
  named := initial
  spans := spans
  source := .cons (.named ⟨bounds,wanted,[⟨0,.actual,3⟩,⟨1,.actual,4⟩],normal,
    .record (alias_refl _) supported_center .capture .capture,
    .cons ⟨rfl,rfl,point_bounded initial 3⟩ (.cons ⟨rfl,rfl,point_bounded initial 4⟩ .nil)⟩) .nil
  ordinary := final
  compiled := literal_write
  receipt := literal (reflexive _)

theorem actual_selected :
    Classify (Rule authorized registry interpretation waiting) root (.selected (.node impl.id [])) :=
  ⟨.selected impl.id [],.selected (.selected selected) .nil,.selected .nil (.selected rfl)⟩

theorem actual_repaired :
    ∃ m, Models final m ∧ Evidence registry interpretation m root (.node impl.id []) := by
  obtain ⟨m,fit⟩ := has_model
  exact ⟨m,fit,dictionary_sound checked covered declared actual_selected m fit⟩

end Cut
end Yulang.GeneralStoppedI61Endpoint335
