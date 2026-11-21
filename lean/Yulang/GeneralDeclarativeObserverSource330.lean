import Yulang.GeneralDeclarativeObserverGrowth330
import Yulang.GeneralDeclarativeStableReplay329

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeObserverSource330
open GeneralDeclarations (Checked Clause Declaration)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeGrowth327 (Extends trans derives fits)
open GeneralDeclarativeObserverGrowth330 (preserve sources_grow trace spine fields endpoints located)
open GeneralDeclarationPatterns (Pattern Constructors normalize)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeStableTrace329 (Actual from_trace)
open GeneralDeclarativeEndpointProbe321 (Matches)
open GeneralDeclarativeArityPlan330 (Shape extract)
open GeneralDeclarativeRecordSpine330 (Spine)
open GeneralDeclarativeRecordFieldRead330 (Fields one)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeRecordMaterial330 (ready tailRow)
open GeneralDeclarativeOrderedRecord326 (order)
open GeneralDeclarativeOpaqueNominal328 (point)
open GeneralDeclarativeStableReads329 (Heads One)
open GeneralDeclarativeOpaqueConserve328 (Retains refl chain)
open GeneralDeclarativeStableInputs329 (demandNames)
open GeneralDeclarativeStableCompiler329 (Frame read)
open GeneralDeclarativeStableAssemble329 (frame_after)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeNFComplete324 (facts)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)

/-- Independent ways the approved source can supply an actual read.
The record branch demands a genuine known terminal and supported
subtraction; it cannot choose an existential tail from a model. -/
inductive Input {s : State} (p : Supported s done) (c : Constructors) (i : Interpretation) :
    Capture → Pattern → Prop where
  | actual : Actual s c i p a pat spans → Input p c i a pat
  | projected : Matches (restriction p) c i a pat →
      (∀ e, translate c i (normalize pat) = some e → Shape e) → Input p c i a pat
  | record : Bounds s a → Spine (restriction p) a.center raw term → keys.Nodup →
      order (CommonRoleCanonicalRows.normalize raw) keys = some chosen → Fields p chosen written binds →
      translate c i (normalize pat) = some (withTail written (.variable binder)) → Input p c i a pat

inductive Inputs {s : State} (p : Supported s done) (c : Constructors) (i : Interpretation) :
    List Capture → List Pattern → Prop where
  | nil : Inputs p c i [] []
  | cons : Input p c i a ptn → Inputs p c i args pats → Inputs p c i (a::args) (ptn::pats)

theorem observe_one {s t : State} {p : Supported s done} (given : Input p c i a pat)
    (older : Extends s t) (protect : List Nat) :
    ∃ out binds, Retains t out protect ∧ One out c i a pat binds ∧
      ∀ use ∈ binds, Bounds out use.2 := by
  cases given with
  | actual known =>
    obtain ⟨_,_,print,shape,positions⟩ := known.reads
    obtain ⟨shown,range⟩ := from_trace (p := preserve p older) (fits older known.args)
      print (trace (sources_grow p older) shape) (located older positions)
    exact ⟨t,_,refl t protect,shown,range⟩
  | projected seen allowed =>
    obtain ⟨range,code,_,_,print,lo,hi⟩ := endpoints (sources_grow p older) seen
    obtain ⟨plan,spelling,known⟩ := extract (p := preserve p older) (allowed code print) lo hi
    have captured := GeneralDeclarativeArityRun330.build (s := t) protect a plan range known
    exact ⟨_,_,captured.modeled,⟨fits captured.modeled.grows range,_,
      _,spelling ▸ print,captured.center,captured.walks⟩,captured.bounds⟩
  | record box looked distinct printed shape translated =>
    have accepted := one (p := preserve p older) (fits older box) (spine (sources_grow p older) looked)
      distinct printed (fields older shape) translated protect
    exact ⟨_,_,accepted⟩

theorem observe_all {s t : State} {p : Supported s done} (given : Inputs p c i args pats)
    (older : Extends s t) (protect : List Nat) :
    ∃ out binds, Retains t out protect ∧ Heads out c i args pats binds ∧
      ∀ use ∈ binds, Bounds out use.2 := by
  induction given generalizing t with
  | nil => exact ⟨t,[],refl t protect,.nil,fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons first _ next =>
    obtain ⟨mid,known,conserve,one,ranges⟩ := observe_one first older protect
    obtain ⟨out,last,together,seen,lastBounds⟩ := next (trans older conserve.grows)
    refine ⟨out,known++last,chain conserve together,.cons (GeneralDeclarativeAritySource330.transport_one
      together.grows one) seen,?_⟩
    intro use listed
    rcases List.mem_append.mp listed with this|that
    · exact fits together.grows (ranges use this)
    · exact lastBounds use that

/-- Source observation drives the real I-58 compiler for arbitrary
mixed head lists in this fragment. No semantic recipe or arbitrary
fresh tail is a premise. Coverage of the latest rule's actual chosen
state beyond this observer fragment is not asserted. -/
theorem compile {s : State} {d : Demand} {p : Supported s done}
    (checked : Checked r) (covered : Coverage r i)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (wanted : Declared r d)
    (sources : Inputs p r.constructors i d.arguments impl.head)
    (protect : List Nat) (fallback : Nat → Capture) (targets : Clause → Nat → Nat) :
    ∃ (stable : State) (kids : List Demand) (frame : Frame stable r i d impl kids),
      Extends s stable ∧ Result stable (facts r i frame.capture impl d kids) ∧
      (∀ m, Models stable m → Meaning r i m d impl frame.capture kids) ∧
      ∀ child ∈ kids, Declared r child := by
  let keep := demandNames d ++ protect
  obtain ⟨observed,spans,lift,seen,found⟩ :=
    observe_all sources (GeneralDeclarativeClauseBatch327.reflexive s) keep
  obtain ⟨now,kids,frame,_,_,writes,_⟩ :=
    frame_after (s := observed) checked covered visible role wanted keep fallback targets seen found
  exact ⟨now,kids,frame,trans (trans lift.grows (GeneralDeclarativeGrowth327.facts _ _)) writes,
    read checked covered visible role wanted frame⟩

end Yulang.GeneralDeclarativeObserverSource330
