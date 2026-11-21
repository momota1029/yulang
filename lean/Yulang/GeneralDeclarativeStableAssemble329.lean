import Yulang.GeneralDeclarativeStableInputs329
import Yulang.GeneralDeclarativeStableAttempt329
import Yulang.GeneralDeclarativeStableCompiler329

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableAssemble329
open GeneralDeclarations (Registry Declaration Clause Checked)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeStableTies329 (Consequence pairOf rows used_after present_entails repeated_shares)
open GeneralDeclarativeStableReads329 (Heads weakened names_all)
open GeneralDeclarativeStableCanonical329 (EqualUses exact uses_existing)
open GeneralDeclarativeOpaqueCapture328 (choose)
open GeneralDeclarativeOpaqueShared328 (Chosen build built)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralDeclarativeGrowth327 (Extends facts trans fits derives)
open GeneralDeclarativeStableCompiler329 (Frame read)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeAppliedClause327 (prepared_exists targetsOnly compiler_projection compiled_frames)
open GeneralDeclarativeClauseBatch327 (Port prepare)
open GeneralDeclarativeClausePlacement327 (placement)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeWhereOutputBatch327 (whole)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeEmissionForest322 (children)

abbrev Span := Nat × Capture

def firsts (spans : List Span) (fallback : Nat → Capture) : Nat → Capture :=
  fun n => choose fallback n spans

def tieState (s : State) (spans : List Span) (fallback : Nat → Capture) : State :=
  appendFacts s (rows (firsts spans fallback) (spans.map pairOf))

def merged (s : State) (keep : List Nat) (spans : List Span) (fallback : Nat → Capture) : Chosen :=
  build keep spans fallback (tieState s spans fallback) (spans.map Prod.fst)

structure MergeFacts (s : State) (keep : List Nat) (spans : List Span) (fallback : Nat → Capture) : Prop where
  preserve : Retains (tieState s spans fallback) (merged s keep spans fallback).state keep
  ranges : ∀ x ∈ spans, Bounds (merged s keep spans fallback).state ((merged s keep spans fallback).captures x.1)
  written : Consequence (merged s keep spans fallback).state (merged s keep spans fallback).captures (spans.map pairOf)

theorem assemble {s : State} (keep : List Nat) (spans : List Span) (fallback : Nat → Capture)
    (fit : ∀ a ∈ spans, Bounds s a.2) : MergeFacts s keep spans fallback := by
  let selected := firsts spans fallback
  let t := tieState s spans fallback
  have ls : Extends s t := facts _ _
  have written : Consequence t selected (spans.map pairOf) :=
    present_entails (used_after selected (spans.map pairOf))
  obtain ⟨all,read⟩ := built keep fallback (spans.map Prod.fst)
    (fun a seen => fits ls (fit a seen)) (repeated_shares written)
  refine ⟨all,?_,?_⟩
  · intro entry seen
    exact (read entry.1 (List.mem_map.mpr ⟨entry,seen,rfl⟩) entry.2 seen).1
  · intro e stored
    obtain ⟨u,comp,rfl⟩ := List.mem_map.mp stored
    obtain ⟨entry,seen,rfl⟩ := List.mem_map.mp (List.mem_filter.mp comp).1
    exact GeneralDeclarativeEqualities322.entails
      (.symm (read entry.1 (List.mem_map.mpr ⟨entry,seen,rfl⟩) entry.2 seen).2)

theorem witness_projection {s : State} {spans : List Span}
    (checked : MergeFacts s keep spans fallback) (m) :
    (Models s m ∧ EqualUses m spans) ↔
      ∃ n, Models (merged s keep spans fallback).state n ∧
        ∀ v ∈ GeneralDeclarativeFootprint321.stateNames (tieState s spans fallback) ++ keep, n v = m v := by
  exact (exact s (firsts spans fallback) spans (uses_existing spans fallback) m).symm.trans
    (GeneralDeclarativeOpaqueConserve328.exact checked.preserve m)

theorem prepare_grows {s t : State} (ran : prepare c i keep cap s clauses = some (t,ports)) : Extends s t := by
  induction clauses generalizing s t ports with
  | nil =>
    have same : s = t := congrArg Prod.fst (Option.some.inj ran)
    cases same
    exact GeneralDeclarativeClauseBatch327.reflexive s
  | cons cl rest ih =>
    cases decoded : GeneralNominalCenteredHeadMatExpressions.translateMany c i
        (cl.arguments.map GeneralDeclarationPatterns.normalize) with
    | none => simp [prepare,decoded] at ran
    | some codes =>
      let jobs := GeneralDeclarativeSparseWhere325.plan cl.arguments codes
      let next := GeneralDeclarativeFreshInputs325.prepared s keep cap jobs
      cases tail : prepare c i keep cap next rest with
      | none => simp [prepare,decoded,next,jobs,tail] at ran
      | some out =>
        have same : out.1 = t := by
          dsimp only [next,jobs] at tail
          have h : some (out.1,GeneralDeclarativeClauseBatch327.make s keep cap cl codes :: out.2) =
              some (t,ports) := by
            simpa [prepare,decoded,tail] using ran
          exact congrArg Prod.fst (Option.some.inj h)
        rw [← same]
        exact trans (GeneralDeclarativeClauseBatch327.make_grows s keep cap jobs) (ih tail)

/-- Compile and replay the exact approved ordinary selection writes.
Naming the repeated captures comes *after* the equality, so only the
post-equality part is conservative. The exact association rows may
narrow the state again. A resulting frame is a source compilation
fact; by itself it is not an election or a proof of model existence. -/
theorem frame_after {s : State} {d : Demand} (checked : Checked r) (covered : Coverage r i)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (demand : Declared r d)
    (keep : List Nat) (fallback : Nat → Capture) (targets : Clause → Nat → Nat)
    (walks : Heads s r.constructors i d.arguments impl.head spans)
    (fit : ∀ a ∈ spans, Bounds s a.2) :
    ∃ (current : State) (kids : List Demand) (frame : Frame current r i d impl kids),
      let input := merged s keep spans fallback
      frame.base = input.captures ∧ frame.spans = spans ∧
      Extends (tieState s spans fallback) current ∧
      (∀ m, Models current m ↔ Models frame.prepared m ∧
        ∀ e ∈ frame.whereRows ++ frame.rootRows, GeneralDeclarativeEntailment320.Holds m e) := by
  let input := merged s keep spans fallback
  have built := assemble keep spans fallback fit
  obtain ⟨prep,ports,ready⟩ := prepared_exists (s := input.state) covered visible targets input.captures keep
  let place := placement impl.requirements ports targets
  let named := sourceNames impl place input.captures
  obtain ⟨ws,rs,atWhere,atRoot,_,_,_,_,models⟩ :=
    compiled_frames checked covered visible role demand targets input.captures keep ready
  let afterWhere := appendFacts prep ws
  let current := appendFacts afterWhere rs
  let kids := children impl named place
  have appended : Extends prep current := trans (facts _ _) (facts _ _)
  have prepGrows : Extends input.state prep :=
    prepare_grows ready
  have headGrows : Extends s current :=
    trans (facts _ _) (trans built.preserve.grows (trans prepGrows appended))
  have has : ∀ v ∈ impl.inputNames, Bounds current (input.captures v) := by
    intro v listed
    change v ∈ _ at listed
    rw [GeneralDeclarations.Declaration.inputNames,← names_all walks] at listed
    obtain ⟨span,found,same⟩ := List.mem_map.mp listed
    rw [← same]
    exact fits (trans prepGrows appended) (built.ranges span found)
  have ties : Consequence current input.captures (spans.map pairOf) := by
    intro e member m fit
    exact built.written e member m (GeneralDeclarativeGrowth327.restrict (trans prepGrows appended) m fit)
  let frame : Frame current r i d impl kids :=
    ⟨input.captures,spans,weakened headGrows walks,ties,has,targets,
      GeneralDeclarativeFootprint321.stateNames input.state ++ keep,input.state,prep,ports,
      ready,appended,ws,atWhere,fun _ h => List.mem_append_left _ (List.mem_append_right _ h),
      rs,atRoot,fun _ h => List.mem_append_right _ h,GeneralDeclarativeOpaqueBatch328.check_exact.mpr rfl⟩
  exact ⟨current,kids,frame,rfl,rfl,trans built.preserve.grows (trans prepGrows appended),models⟩

end Yulang.GeneralDeclarativeStableAssemble329
