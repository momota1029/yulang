import Yulang.GeneralDeclarativeCompoundSources338
import Yulang.GeneralDeclarativeWitnessHead334

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCompoundInputs338
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeGrowth327 (Extends restrict fits)
open GeneralDeclarativeObserverGrowth330 (preserve sources_grow)
open GeneralDeclarativeClauseBatch327 (reflexive)
open GeneralDeclarativeCompoundTree338
open GeneralDeclarativeCompoundSources338 (Source Anchors exact)
open GeneralDeclarativeEndpointConserve336 (names)
open GeneralDeclarativeExactSupport337 (receipts_same)
open GeneralDeclarativeWitnessHead334 (Argument argument_sound)
open GeneralDeclarativeStableReads329 (names_one)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarationPatterns (Constructors Pattern normalize normalizeArgs variablesArgs)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂)

def oldAfter {w : World done} (a : Argument w.source c i (names w.reads ++ keep) w.state arg pat s used)
    : World done :=
  ⟨s,preserve w.source ((argument_sound a (reflexive _)).1.grows),w.reads⟩

theorem old_sound {w : World done} (seen : Argument w.source c i (names w.reads ++ keep) w.state arg pat s used) :
    Sound keep w (oldAfter seen) := by
  obtain ⟨writes,_,_⟩ := argument_sound seen (reflexive _)
  refine ⟨⟨writes.grows,fun _ found => found,sources_grow w.source writes.grows⟩,?_⟩
  intro m fit
  obtain ⟨n,model,stayed⟩ := writes.lifts m fit.1
  exact ⟨n,⟨model,(receipts_same (fun x h => stayed x
    (List.mem_append_right _ (List.mem_append_left _ h)))).mpr fit.2⟩,stayed⟩

/-- Append actual compound and earlier approved ordinary inputs in one
ordered pass. There is no I-58 or where/output writing in this pass. -/
inductive Inputs {done : Nat → Prop} (c : Constructors) (i : Interpretation)
    (keep : List Nat) : World done → List Capture → List Pattern → World done → List Span → Prop where
  | nil : Inputs c i keep w [] [] w []
  | compound : Tree keep w a (normalize p) mid now → Inputs c i keep mid args ps final later →
      Inputs c i keep w (a::args) (p::ps) final (now++later)
  | ordinary (old : Argument w.source c i (names w.reads ++ keep) w.state a p s now) :
      Inputs c i keep (oldAfter old) args ps final later →
      Inputs c i keep w (a::args) (p::ps) final (now++later)

theorem input_exact {w v : World done} (inputs : Inputs c i keep w args pats v spans) :
    Sound keep w v ∧ spans.map Prod.fst = variablesArgs (normalizeArgs pats) ∧
      ∀ u ∈ spans, Bounds v.state u.2 := by
  induction inputs with
  | nil => exact ⟨identity _ _,rfl,fun _ m => False.elim (List.not_mem_nil m)⟩
  | compound one _ ih =>
    obtain ⟨first,order,bounds⟩ := tree_exact one
    obtain ⟨last,rest,others⟩ := ih
    refine ⟨chain first last,by simp only [List.map_append,order,rest,normalizeArgs,variablesArgs],?_⟩
    intro u active
    exact (List.mem_append.mp active).elim (fun h => fits last.1.1 (bounds u h)) (others u)
  | ordinary one _ ih =>
    obtain ⟨_,actual,bounds⟩ := argument_sound one (reflexive _)
    have order := names_one actual
    obtain ⟨last,rest,others⟩ := ih
    refine ⟨chain (old_sound one) last,by simp only [List.map_append,order,rest,normalizeArgs,variablesArgs],?_⟩
    intro u active
    exact (List.mem_append.mp active).elim (fun h => fits last.1.1 (bounds u h)) (others u)

theorem extend_compound {w : World done} (seen : Source (restriction w.source) lo hi (normalize pat))
    (anchors : Anchors (restriction w.source) a lo hi) (bounds : Bounds w.state a) :
    ∃ v spans, Inputs c i keep w [a] [pat] v spans := by
  obtain ⟨v,spans,run,_⟩ := exact seen keep anchors bounds
  refine ⟨v,spans,?_⟩
  simpa only [List.append_nil] using Inputs.compound (c := c) (i := i) run Inputs.nil

theorem models_back {w v : World done} (h : w.Grows v) (fit : fitsModel v m) : fitsModel w m :=
  ⟨restrict h.1 m fit.1,fun e p => fit.2 e (h.2.1 p)⟩

theorem root_bounds {w v : World done} (t : Tree keep w a p v used) : Bounds w.state a := by
  cases t with
  | binder fit => exact fit
  | record ticket => exact ticket.read.valid

def range (m : Assignment) (a : Capture) : Prop :=
  InInterval (m a.lower).1 (m a.upper).1 (m a.center).1

inductive Observed (c : Constructors) (i : Interpretation) (m : Assignment) : Capture → Pattern → Prop where
  | compound {w v : World done} (read : Tree keep w a (normalize p) v used) :
    fitsModel v m → range m a → (∀ u ∈ used, range m u.2) → Observed c i m a p
  | ordinary {s : State} (core : GeneralDeclarativeStableReads329.One s c i a p used) :
    Models s m → range m a → Observed c i m a p

theorem observed {w v : World done} (inputs : Inputs c i keep w args pats v spans) (m : Assignment)
    (fit : fitsModel v m) : All₂ (Observed c i m) args pats := by
  induction inputs with
  | nil => exact .nil
  | compound one later ih =>
    have earlier := models_back (input_exact later).1.1 fit
    have now := tree_exact one
    have source := models_back now.1.1 earlier
    exact .cons (.compound one earlier (bounds_sound (root_bounds one) m source.1)
      (fun _ found => bounds_sound (now.2.2 _ found) m earlier.1)) (ih fit)
  | ordinary old later ih =>
    obtain ⟨_,core,_⟩ := argument_sound old (reflexive _)
    have earlier := models_back (input_exact later).1.1 fit
    exact .cons (.ordinary core earlier.1 (bounds_sound core.fits m earlier.1)) (ih fit)

end Yulang.GeneralDeclarativeCompoundInputs338
