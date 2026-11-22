import Yulang.GeneralDeclarativeAlternativeNamedComplete333
import Yulang.GeneralDeclarativeAlternativeRangedReplay333
import Yulang.GeneralDeclarativeStableTrace329

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAlternativeNamedHeads333
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds Demand)
open GeneralDeclarativeAlternativeView333 (Index)
open GeneralDeclarativeAlternativeNeeds333 (Planned Eventually eventually_pair Need finiteIndex)
open GeneralDeclarativeAlternativeNamed333 (named Result)
open GeneralDeclarativeAlternativeNamedComplete333 (named_plan)
open GeneralDeclarativeAlternativeRange333 (Known located located_ok)
open GeneralDeclarativeAlternativeHeads333 (endpoint endpoint_plan endpoint_sound inhabited_list from_nonempty)
open GeneralDeclarativeEndpointProbe321 (Matches HeadMatches)
open GeneralDeclarativeTrace321 (Trace Occurrence)
open GeneralDeclarativeStableTrace329 (Located Actual)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (All₂)

def normalized (src : Index s) (depth : Nat) (c : Constructors) (i : Interpretation)
    (mode : GeneralNominalMaterialization.Mode) (n : Nat) (pat : Pattern) : List (List Occurrence) :=
  match translate c i (normalize pat) with
  | none => []
  | some code => (named src depth mode n code).map Subtype.val

theorem read_sound {src : Index s} (member : used ∈ normalized src depth c i mode n pat) :
    ∃ code, translate c i (normalize pat) = some code ∧ Trace s mode n code used := by
  cases printed : translate c i (normalize pat) with
  | none => simp [normalized,printed] at member
  | some code =>
    rw [normalized,printed] at member
    obtain ⟨result,_,rfl⟩ := List.mem_map.mp member
    exact ⟨code,rfl,result.property⟩

theorem read_plan {s : State} (printed : translate c i (normalize pat) = some code)
    (previous : Trace s mode arg code used) :
    Planned (fun src : Index s => Eventually (fun f => used ∈ normalized src f c i mode arg pat)) := by
  apply (named_plan previous).map
  intro src future
  obtain ⟨start,good⟩ := future
  refine ⟨start,fun f enough => ?_⟩
  change _ ∈ normalized src f c i mode arg pat
  rw [normalized,printed]
  exact List.mem_map.mpr ⟨⟨used,previous⟩,good f enough,rfl⟩

def namedEndpoint (src : Index s) (depth : Nat) (c : Constructors) (i : Interpretation)
    : List Capture → List Pattern → Bool
  | [],[] => true
  | a::as,p::ps => !(normalized src depth c i .lower a.lower p).isEmpty &&
      !(normalized src depth c i .upper a.upper p).isEmpty &&
      namedEndpoint src depth c i as ps
  | _,_ => false

theorem endpoints_plan {s : State} (observed : All₂ (Matches s c i) args pats) :
    Planned (fun src : Index s => Eventually (fun f => namedEndpoint src f c i args pats = true)) := by
  induction observed with
  | nil => exact Planned.pure fun _ => ⟨0,fun _ _ => rfl⟩
  | cons first _ after =>
    obtain ⟨_,_,_,_,printed,lo,hi⟩ := first
    apply (((read_plan printed lo).both (read_plan printed hi)).both after).map
    intro src pieces
    obtain ⟨depth,holds⟩ := eventually_pair (eventually_pair pieces.1.1 pieces.1.2) pieces.2
    refine ⟨depth,fun n enough => ?_⟩
    have observed := holds n enough
    change (!_ && !_ && _) = true
    rw [inhabited_list observed.1.1,inhabited_list observed.1.2,observed.2]
    rfl

theorem endpoints_sound {s : State} {src : Index s} (fit : ∀ a ∈ args, Bounds s a)
    (checked : namedEndpoint src depth c i args pats = true) : All₂ (Matches s c i) args pats := by
  induction args generalizing pats with
  | nil =>
    cases pats with
    | nil => exact .nil
    | cons => cases checked
  | cons a as ih =>
    cases pats with
    | nil => cases checked
    | cons p ps =>
      simp only [namedEndpoint,Bool.and_eq_true] at checked
      obtain ⟨l,gotL,_⟩ := from_nonempty checked.1.1
      obtain ⟨u,gotU,_⟩ := from_nonempty checked.1.2
      obtain ⟨code,printed,low⟩ := read_sound gotL
      obtain ⟨other,also,high⟩ := read_sound gotU
      cases Option.some.inj (also.symm.trans printed)
      exact .cons ⟨fit a List.mem_cons_self,code,l,u,printed,low,high⟩
        (ih (fun b present => fit b (List.mem_cons_of_mem _ present)) checked.2)

def bothEndpoints (src : Index s) (depth : Nat) (c : Constructors) (i : Interpretation)
    (args : List Capture) (pats : List Pattern) : Bool :=
  namedEndpoint src depth c i args pats || endpoint src depth c i args pats

/-- This is exactly the positive predicate of C331's actual candidate
construction, not a new test for pending, rejection or precedence. -/
theorem candidate_exact {s : State} {p : Supported s done}
    (fit : ∀ a ∈ d.arguments, Bounds (restriction p) a) :
    (GeneralDeclarativeInlineEndpoint331.candidates p r i waiting).viable d impl ↔
    ∃ packet : List (Need (restriction p)), Eventually (fun f =>
      bothEndpoints (finiteIndex packet) f r.constructors i d.arguments impl.head = true) := by
  constructor
  · intro viable
    have exact : Planned (fun src : Index (restriction p) => Eventually (fun f =>
        bothEndpoints src f r.constructors i d.arguments impl.head = true)) := by
      rcases viable with legacy|inline
      · apply (endpoints_plan legacy).map
        intro src avail
        obtain ⟨k,good⟩ := avail
        exact ⟨k,fun f enough => by simp [bothEndpoints,good f enough]⟩
      · apply (endpoint_plan inline).map
        intro src avail
        obtain ⟨k,good⟩ := avail
        exact ⟨k,fun f enough => by simp [bothEndpoints,good f enough]⟩
    exact exact.finite
  · rintro ⟨packet,depth,proof⟩
    have h := proof depth (Nat.le_refl _)
    change bothEndpoints (finiteIndex packet) depth r.constructors i d.arguments impl.head = true at h
    have cases : namedEndpoint (finiteIndex packet) depth r.constructors i d.arguments impl.head = true ∨
      endpoint (finiteIndex packet) depth r.constructors i d.arguments impl.head = true := by
      simpa [bothEndpoints,Bool.or_eq_true] using h
    rcases cases with old|inline
    · exact .inl (endpoints_sound fit old)
    · exact .inr (endpoint_sound _ fit inline)

def materialSpans (view : Known s) (used : List Occurrence) : List (Nat × Capture) :=
  used.map fun o => (o.binder,located view o.argument)

theorem located_spans (view : Known s) (used : List Occurrence) :
    All₂ (Located s) used (materialSpans view used) := by
  induction used with
  | nil => exact .nil
  | cons o os ih =>
    have found := located_ok (view := view) o.argument
    exact .cons ⟨rfl,found.1.symm,found.2⟩ ih

theorem actual_named {s : State} {p : Supported s done} {src : Index (restriction p)}
    (view : Known s) (box : Bounds s a)
    (got : sites ∈ normalized src f c i .actual a.center pat) :
    Actual s c i p a pat (materialSpans view sites) := by
  obtain ⟨code,printed,source⟩ := read_sound got
  exact ⟨box,code,sites,printed,source,located_spans view sites⟩

end Yulang.GeneralDeclarativeAlternativeNamedHeads333
