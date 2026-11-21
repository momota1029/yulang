import Yulang.GeneralDeclarativeInlineGrowth331
import Yulang.GeneralDeclarativeInlineEndpoint331
import Yulang.GeneralDeclarativeCurrentReceipt330
import Yulang.GeneralDeclarativeExactFrame331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineCompiler331
open GeneralDeclarations (Checked Declaration Clause Registry)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeInlineMaterial331 (seed ordinary read)
open GeneralDeclarativeInlineAllocation331 (captures)
open GeneralDeclarativeInlineGrowth331 (extend)
open GeneralDeclarativeObserverSource330 (Input observe_one)
open GeneralDeclarativeObserverGrowth330 (backed_same preserve sources_grow)
open GeneralDeclarativeGrowth327 (Extends trans fits)
open GeneralDeclarativeOpaqueConserve328 (Retains refl chain)
open GeneralDeclarativeStableReads329 (Heads One weakened)
open GeneralDeclarativeAritySource330 (transport_one)
open GeneralDeclarativeStableInputs329 (demandNames)
open GeneralDeclarativeExactFrame331 (frame_after_exact)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeNFComplete324 (facts)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (translate)

inductive Source {s : State} (p : Supported s done) (c : Constructors) (i : Interpretation) :
    List Capture → List Pattern → Prop where
  | nil : Source p c i [] []
  | exactOld : Input p c i a pat → Source p c i args pats → Source p c i (a::args) (pat::pats)
  | inline : Bounds s a → translate c i (normalize pat) = some code →
    Read (restriction p) .actual (.variable a.center) code occurrences →
    Source p c i args pats → Source p c i (a::args) (pat::pats)

theorem heads {s t : State} {p : Supported s done}
    (fromSource : Source p c i args pats) (grows : Extends s t) (keep : List Nat) :
    ∃ out uses, Retains t out keep ∧ Heads out c i args pats uses ∧
      ∀ occurrence ∈ uses, Bounds out occurrence.2 := by
  induction fromSource generalizing t with
  | nil => exact ⟨t,[],refl t keep,.nil,fun _ h => False.elim (List.not_mem_nil h)⟩
  | exactOld first _ tail =>
    obtain ⟨mid,spans,store,one,known⟩ := observe_one first grows keep
    obtain ⟨out,rest,kept,seen,bounds⟩ := tail (trans grows store.grows)
    exact ⟨out,spans++rest,chain store kept,.cons (transport_one kept.grows one) seen,
      fun x h => (List.mem_append.mp h).elim (fun member => fits kept.grows (known _ member)) (bounds x)⟩
  | inline box printed traced _ tail =>
    obtain ⟨mid,kept,one,_,known⟩ :=
      read (p := preserve p grows) (fits grows box) printed (extend (sources_grow p grows) traced) keep
    obtain ⟨out,rest,safe,seen,bounds⟩ := tail (trans grows kept.grows)
    exact ⟨out,_,chain kept safe,.cons (transport_one safe.grows one) seen,
      fun x h => (List.mem_append.mp h).elim (fun member => fits safe.grows (known _ member)) (bounds x)⟩

/-- Independently observed actual occurrences reach the existing
I-58 compiler, preserving written child order and caller-specified
fixed output targets. This builds a frame, not a candidate election.
Only the actual stage uses a centre; the supported endpoint guard
belongs to the independent preliminary observation. -/
theorem compile {s : State} {d : Demand} {p : Supported s done}
    (checked : Checked r) (coverage : Coverage r i)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (declared : Declared r d)
    (source : Source p r.constructors i d.arguments impl.head) (fixed : List Nat)
    (fallback : Nat → Capture) (targets : Clause → Nat → Nat) :
    ∃ (assembled : State) (kids : List Demand) (frame : Frame assembled r i d impl kids),
      Extends s assembled ∧ frame.targets = targets ∧
      assembled = appendFacts (appendFacts frame.prepared frame.whereRows) frame.rootRows ∧
      Result assembled (facts r i frame.capture impl d kids) ∧
      (∀ m, Models assembled m → Meaning r i m d impl frame.capture kids) ∧
      ∀ child ∈ kids, Declared r child := by
  let keep := demandNames d ++ fixed
  obtain ⟨mid,spans,retained,observed,bounds⟩ :=
    heads source (GeneralDeclarativeClauseBatch327.reflexive s) keep
  obtain ⟨endState,kids,frame,_,_,targetsExact,writesExact,endSteps,_⟩ :=
    frame_after_exact checked coverage visible role declared keep fallback targets observed bounds
  refine ⟨endState,kids,frame,trans (trans retained.grows (GeneralDeclarativeGrowth327.facts _ _)) endSteps,targetsExact,writesExact,
    GeneralDeclarativeStableCompiler329.read checked coverage visible role declared frame⟩

end Yulang.GeneralDeclarativeInlineCompiler331
