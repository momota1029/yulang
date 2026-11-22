import Yulang.GeneralDeclarativeWitnessTagSources351
import Yulang.GeneralDeclarativeWitnessCompiler350
import Yulang.GeneralDeclarativeEndpointBody336

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTagLocal351
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand Bounds bounds_sound)
open GeneralDeclarativeWitnessOrigins350 (Table Attached support)
open GeneralDeclarativeWitnessTagSources351 (DirectBounds NamedBounds)
open GeneralDeclarativeTaggedWhole340 (fullState copied existing_head)
open GeneralDeclarativeTaggedPatch340 (captured)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeStableReads329 (One names_one)
open GeneralDeclarativeWitnessCompiler350 (Context Accepted)
open GeneralDeclarativeEndpointBody336 (Body calculate sound Meaning)
open GeneralDeclarativeExactDictionary337 (Observed)
open GeneralDeclarativeEqualities322 (semantic)
open GeneralDeclarativeGrowth327 (trans facts restrict)
open GeneralDeclarativeStableAssemble329 (tieState)
open GeneralDeclarativeCurrentReceipt330 (relays_models)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarationPatterns (Pattern Constructors normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralCandidateInspection (plainNames)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Registry Declaration Checked Clause)

/-- The two routes have the same operational preparation, but not the
same source judgment. This does not turn nested alias steps into a
literal recorded RHS. -/
inductive Route {s : State} {t : Table} (a : Attached s t) (arg : Capture) (tag : Nat) where
  | direct : DirectBounds a arg tag → Route a arg tag
  | named : NamedBounds a arg tag → Route a arg tag

def Route.low {s : State} {t : Table} {a : Attached s t} : Route a arg tag → Expr
  | .direct d => d.lower
  | .named d => d.lower.payload
def Route.high {s : State} {t : Table} {a : Attached s t} : Route a arg tag → Expr
  | .direct d => d.upper
  | .named d => d.upper.payload

structure PatternData (c : Constructors) (i : Interpretation) (pat : Pattern) (tag : Nat) where
  payload : Pattern
  ordered : List Nat
  code : Expr
  normal : normalize pat = .variant tag payload
  plain : plainNames payload = some ordered
  translated : translate c i payload = some code

def parse (c : Constructors) (i : Interpretation) (pat : Pattern) (tag : Nat) :
    Option (PatternData c i pat tag) :=
  match known : normalize pat with
  | .variant k payload =>
    if tagOK : k = tag then
      match plain : plainNames payload, printed : translate c i payload with
      | some names,some code =>
        some ⟨payload,names,code,tagOK ▸ known,plain,printed⟩
      | _,_ => none
    else none
  | _ => none

variable {s : State} {t : Table} {a : Attached s t} {arg : Capture} {tag : Nat}
variable {c : Constructors} {i : Interpretation} {pat : Pattern}

def next (h : Route a arg tag) (x : PatternData c i pat tag) (keep : List Nat) : State :=
  fullState s arg tag h.low h.high keep x.code

def spans (h : Route a arg tag) (x : PatternData c i pat tag) (keep : List Nat) : List (Nat × Capture) :=
  copied (captured s arg tag h.low h.high keep) x.ordered

theorem input_direct (read : DirectBounds a arg tag) (p : PatternData c i pat tag) (keep : List Nat) :
    GeneralDeclarativeTaggedInputs340.Input (support a) c i keep s arg pat
      (next (.direct read) p keep) (spans (.direct read) p keep) [] :=
  .whole read.fact p.normal p.plain p.translated

theorem prepared (h : Route a arg tag) (x : PatternData c i pat tag) (keep : List Nat) :
    Retains s (next h x keep) keep ∧
      One (next h x keep) c i arg pat (spans h x keep) ∧
      (∀ a ∈ spans h x keep, Bounds (next h x keep) a.2) := by
  cases h with
  | direct d => exact existing_head d.fact keep x.normal x.plain x.translated
  | named d =>
    exact GeneralDeclarativeTaggedNamedPatch340.checked_head
      d.fact d.lower.actual d.upper.actual keep x.normal x.plain x.translated

def context {r : Registry} (d : Demand) (impl : Declaration)
    (h : Route a arg tag) (x : PatternData r.constructors i pat tag) (keep : List Nat)
    (fallback : Nat → Capture) (targets : Clause → Nat → Nat) : Context :=
  ⟨r,i,d,impl,next h x keep,spans h x keep,keep,fallback,targets⟩

theorem sound_local {r : Registry} {d : Demand} {impl : Declaration}
    (h : Route a arg tag) (x : PatternData r.constructors i pat tag)
    {keep fallback targets current wire}
    (ran : Accepted (context d impl h x keep fallback targets) current wire)
    (header : Checked r) (coverage : Coverage r i)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (declared : Declared r d)
    (_args : d.arguments = [arg]) (head : impl.head = [pat])
    (m : Assignment) (fit : Models current m) :
    Observed r.constructors i m arg pat ∧
      (∃ cap, Meaning r i m d impl cap ran.compiled.kids) ∧
      (∀ child ∈ ran.compiled.kids,Declared r child) := by
  obtain ⟨_,read,ranges⟩ := prepared h x keep
  have ord : (spans h x keep).map Prod.fst = impl.inputNames := by
    rw [GeneralDeclarations.Declaration.inputNames,head]
    simpa only [GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.variablesArgs,
      List.append_nil] using names_one read
  obtain ⟨ordinary,kids,body,ranActual,_,_,_,_,grows⟩ :=
    calculate header coverage visible role declared keep fallback targets ord ranges
  have compiled := GeneralDeclarativeWitnessCompiler350.actual ran
  change GeneralDeclarativeNestedBody332.compileBody r i d impl (next h x keep)
    (spans h x keep) keep fallback targets = some (ran.compiled.state,ran.compiled.kids) at compiled
  have same := Option.some.inj (ranActual.symm.trans compiled)
  cases same
  have viewed := relays_models (GeneralDeclarativeWitnessCompiler350.retained ran) m fit
  have named := restrict (trans (facts (next h x keep) _) grows) m viewed
  obtain ⟨code,form,printed,center,walk⟩ := read.actual
  obtain ⟨meaning,children⟩ := sound body header coverage visible role declared m viewed
  exact ⟨.literal (bounds_sound read.fits m named) printed (semantic center m named) walk,
    ⟨body.capture,meaning⟩,children⟩

end Yulang.GeneralDeclarativeWitnessTagLocal351
