import Yulang.GeneralDeclarativeExactDictionary337
import Yulang.GeneralDeclarativeEndpointSupport336
import Yulang.GeneralDeclarativeEndpointConserve336

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeExactSupport337
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeEndpointOverlay336 (Entry inputs)
open GeneralDeclarativeExactOverlay337 (ModelsExact Holds eval eval_eq)
open GeneralDeclarativeEndpointSupport336 (Certified)
open GeneralDeclarativeEndpointConserve336 (refs names slots_same)
open GeneralDeclarativeEndpointRecord336 (interp)
open GeneralDeclarativeEndpointProgram336 (Projection)
open GeneralDeclarativeRecordChannel330 (project)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeStableAssemble329 (tieState merged assemble)
open GeneralDeclarativeStableCanonical329 (EqualUses)
open GeneralNominalCommonBridge (Assignment)

def endpointRows (e : Entry) : List Equation :=
  match e.1 with
  | .field _ _ a b | .rest _ _ a b => [⟨e.2.lower,a⟩,⟨e.2.upper,b⟩]

theorem endpoints_sound {e : Entry} {m : Assignment} (h : Holds m e) :
    ∀ row ∈ endpointRows e, GeneralDeclarativeEntailment320.Holds m row := by
  obtain ⟨step,cap⟩ := e
  obtain ⟨ideal,run,observed⟩ := h
  cases step with
  | field a k lo hi =>
    cases seen : project k false [] (m a.center).1 with
    | none => simp [eval,Projection.eval,seen] at run
    | some payload =>
      have written : (interp m lo,payload,interp m hi) = ideal :=
        Option.some.inj (by simpa [eval,Projection.eval,seen] using run)
      subst ideal
      intro row shown
      change row ∈ [⟨cap.lower,lo⟩,⟨cap.upper,hi⟩] at shown
      rcases List.mem_cons.mp shown with rfl|after
      · exact observed.1
      · cases List.mem_singleton.mp after
        exact observed.2.2
  | rest a ks lo hi =>
    have written : (interp m lo,GeneralDeclarativeExactDelete337.subtract ks (m a.center).1,
        interp m hi) = ideal := Option.some.inj run
    subst ideal
    intro row shown
    change row ∈ [⟨cap.lower,lo⟩,⟨cap.upper,hi⟩] at shown
    rcases List.mem_cons.mp shown with rfl|after
    · exact observed.1
    · cases List.mem_singleton.mp after
      exact observed.2.2

def rows (rs : List Entry) : List Equation := rs.flatMap endpointRows

theorem model_exact (s : State) (rs : List Entry) (m : Assignment) :
    ModelsExact (appendFacts s (rows rs)) rs m ↔ ModelsExact s rs m := by
  rw [ModelsExact,ModelsExact,model_append]
  exact ⟨fun fit => ⟨fit.1.1,fit.2⟩,fun fit => ⟨⟨fit.1,fun row used => by
    obtain ⟨e,present,chosen⟩ := List.mem_flatMap.mp used
    exact endpoints_sound (fit.2 e present) _ chosen⟩,fit.2⟩⟩

/-- Standalone residual endpoints are backed by the actual source
read and computed deletion; the center still has no forged syntax.
The old origin algebra has no projection constructor. The adapter
uses source only when the new certificate is provided. -/
def authorize {s : State} (p : Supported s done) (rs : List Entry) : Supported (appendFacts s (rows rs)) done where
  derivesFrom row o := p.derivesFrom row o ∨
    (∃ e ∈ rs, Certified p e ∧ row ∈ endpointRows e) ∧ o = .source
  ordinary := by
    intro row o heard
    rcases heard with old|⟨⟨e,present,cert,written⟩,source⟩
    · exact List.mem_append_left _ (p.ordinary old)
    · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨e,present,written⟩)

theorem from_projection {s : State} {p : Supported s done} {rs : List Entry} {e : Entry}
    (listed : e ∈ rs) (authored : Certified p e) (exactRow : row ∈ endpointRows e) :
    row ∈ (restriction (authorize p rs)).equations :=
  from_source _ (.inr ⟨⟨e,listed,authored,exactRow⟩,rfl⟩)

theorem holds_same {e : Entry} {m n : Assignment} (kept : ∀ v ∈ refs e, n v = m v) :
    Holds n e ↔ Holds m e := by
  have source := eval_eq (p := e.1) (m := m) (n := n)
    (fun v there => kept v (List.mem_append_left _ there))
  unfold Holds
  rw [source,slots_same kept]

theorem receipts_same {rs : List Entry} {m n : Assignment} (kept : ∀ v ∈ names rs, n v = m v) :
    (∀ e ∈ rs, Holds n e) ↔ ∀ e ∈ rs, Holds m e := by
  have exactScope : ∀ e ∈ rs, Holds n e ↔ Holds m e := by
    intro e used
    exact holds_same (fun v h => kept v (List.mem_flatMap.mpr ⟨e,used,h⟩))
  exact ⟨fun f e info => (exactScope e info).mp (f e info),
    fun f e info => (exactScope e info).mpr (f e info)⟩

theorem conserve {s t : State} (grow : Retains s t keep)
    (footprint : names rs ⊆ stateNames s ++ keep) (m : Assignment) :
    ModelsExact s rs m ↔ ∃ n, ModelsExact t rs n ∧ ∀ v ∈ stateNames s ++ keep, n v = m v := by
  constructor
  · intro valid
    obtain ⟨n,known,kept⟩ := grow.lifts m valid.1
    exact ⟨n,⟨known,(receipts_same (fun v h => kept v (footprint h))).mpr valid.2⟩,kept⟩
  · intro ⟨n,valid,kept⟩
    exact ⟨(GeneralDeclarativeOpaqueConserve328.exact grow m).mpr ⟨n,valid.1,kept⟩,
      (receipts_same (fun v h => kept v (footprint h))).mp valid.2⟩

theorem ready_after_ties {s : State} (valid : ModelsExact s rs m) (shared : EqualUses m uses)
    (fit : ∀ slot ∈ uses, Bounds s slot.2)
    (footprint : names rs ⊆ stateNames (tieState s uses fallback) ++ keep) :
    ∃ n, ModelsExact (merged s keep uses fallback).state rs n ∧
      ∀ v ∈ stateNames (tieState s uses fallback) ++ keep, n v = m v := by
  exact (conserve (assemble keep uses fallback fit).preserve footprint m).mp
    ((GeneralDeclarativeExactDictionary337.ties_exact s rs uses fallback m).mpr ⟨valid,shared⟩)

open GeneralDeclarativeEndpointRecord336 (Read)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeRecordSpine330 (Terminal)
open GeneralDeclarativeOrderedRecord326 (order)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open CommonRoleCanonicalRows (Row normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr)

/-- Re-enter the same supported reader on a projected compound field
or standalone residual. Both child endpoint spines come from its
already certified literal endpoints, not from the projected center. -/
theorem nested_read {s : State} {p : Supported s done} {rs : List Entry} {e : Entry}
    (listed : e ∈ rs) (backed : Certified p e) (bounded : Bounds s e.2)
    (left : (⟨e.2.lower,withTail ls le⟩ : Equation) ∈ endpointRows e)
    (right : (⟨e.2.upper,withTail us ue⟩ : Equation) ∈ endpointRows e)
    (leftEnd : Terminal le) (rightEnd : Terminal ue) (different : keys.Nodup)
    (lowOrder : order (normalize ls) keys = some first)
    (highOrder : order (normalize us) keys = some last) :
    Read (authorize p rs) e.2 keys ls us first last le ue :=
  ⟨GeneralDeclarativeGrowth327.fits (GeneralDeclarativeGrowth327.facts _ _) bounded,different,
    .inline (alias_refl _) leftEnd (from_projection listed backed left),
    .inline (alias_refl _) rightEnd (from_projection listed backed right),lowOrder,highOrder⟩


end Yulang.GeneralDeclarativeExactSupport337
