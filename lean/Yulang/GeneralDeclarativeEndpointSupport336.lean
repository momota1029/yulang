import Yulang.GeneralDeclarativeEndpointOverlay336
import Yulang.GeneralDeclarativeAggregate324
import Yulang.GeneralDeclarativeObserverGrowth330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointSupport336
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeEntailment320 (appendFacts Holds model_append)
open GeneralDeclarativeEndpointOverlay336 (Entry ModelsWith)
open GeneralDeclarativeEndpointProgram336 (Projection ready)
open GeneralDeclarativeEndpointRecord336 (Read interp)
open GeneralDeclarativeEndpointBatch336 (atSlots)
open GeneralDeclarativeRecordChannel330 (project)
open GeneralDeclarativeLowerKnown321 (Knows Alias constructorTag knows_row knows_alias)
open GeneralDeclarativeGrowth327 (Extends facts derives)
open GeneralDeclarativeObserverGrowth330 (preserve sources_grow)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)

def writes (e : Entry) : List Equation :=
  match e.1 with
  | .field _ _ low high => [⟨e.2.lower,low⟩,⟨e.2.upper,high⟩]
  | .rest _ _ _ _ => []

/-- Only the genuine *field endpoint* payload expressions can be
copied into ordinary rows. Neither an actual-center field nor a
mask-sensitive residual gets a pretend Expr equality. -/
theorem writes_sound {m : Assignment} {e : Entry} (h : GeneralDeclarativeEndpointOverlay336.Holds m e) :
    ∀ row ∈ writes e, Holds m row := by
  obtain ⟨route,cap⟩ := e
  cases route with
  | rest a keys lo hi => intro row impossible; cases impossible
  | field a label lo hi =>
    obtain ⟨ideal,compiled,agrees⟩ := h
    cases test : project label false [] (m a.center).1 with
    | none => simp [Projection.eval,test] at compiled
    | some field =>
      have eq : (interp m lo,field,interp m hi) = ideal := by
        apply Option.some.inj
        simpa only [Projection.eval,test,Option.map_some] using compiled
      subst ideal
      intro row written
      change row ∈ [⟨cap.lower,lo⟩,⟨cap.upper,hi⟩] at written
      rcases List.mem_cons.mp written with rfl|last
      · exact agrees.1
      · cases List.mem_singleton.mp last
        exact agrees.2.2

def Certified {s : State} (p : Supported s done) (e : Entry) : Prop :=
  ∃ arg shape tail ls us first last le ue jobs before keep,
    Read p arg (shape.map Prod.fst) ls us first last le ue ∧
    ready arg shape tail ls us first last le ue = some jobs ∧
    e ∈ GeneralDeclarativeEndpointOverlay336.receipts before
      (GeneralDeclarativeEndpointOverlay336.footprintKeep keep jobs) jobs

def rows (rs : List Entry) : List Equation := rs.flatMap writes

theorem materialize (s : State) (rs : List Entry) (m : Assignment) :
    ModelsWith (appendFacts s (rows rs)) rs m ↔ ModelsWith s rs m := by
  rw [ModelsWith,ModelsWith,model_append]
  exact ⟨fun fit => ⟨fit.1.1,fit.2⟩,fun fit => ⟨⟨fit.1,fun row haveIt => by
    obtain ⟨e,active,added⟩ := List.mem_flatMap.mp haveIt
    exact writes_sound (fit.2 e active) row added⟩,fit.2⟩⟩

/-- This is an adapter for the old two-case origin type. Its explicit
certificate is the supported I-61 source derivation, not satisfaction
of an ordinary equation and not a claim of parser authorship. -/
def authorize {s : State} (p : Supported s done) (rs : List Entry)
    (_legit : ∀ e ∈ rs, Certified p e) : Supported (appendFacts s (rows rs)) done where
  derivesFrom e o := p.derivesFrom e o ∨ (∃ receipt ∈ rs, Certified p receipt ∧ e ∈ writes receipt) ∧ o = .source
  ordinary := by
    intro e o proof
    rcases proof with old|⟨⟨entry,present,real,written⟩,src⟩
    · exact List.mem_append_left _ (p.ordinary old)
    · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨entry,present,written⟩)

theorem old_kept {s : State} {p : Supported s done} {legit : ∀ e ∈ rs, Certified p e}
    (h : e ∈ (restriction p).equations) :
    e ∈ (restriction (authorize p rs legit)).equations :=
  (GeneralDeclarativeOrigins321.backed_iff _ _).mpr <| by
    obtain ⟨o,old,available⟩ := (GeneralDeclarativeOrigins321.backed_iff _ _).mp h
    exact ⟨o,.inl old,available⟩

theorem projected_row {s : State} {p : Supported s done} {legit : ∀ e ∈ rs, Certified p e}
    (part : e ∈ rs) (written : row ∈ writes e) :
    row ∈ (restriction (authorize p rs legit)).equations :=
  from_source _ (.inr ⟨⟨e,part,legit e part,written⟩,rfl⟩)

theorem bounded_field {s : State} {p : Supported s done} {legit : ∀ e ∈ rs, Certified p e}
    {e : Entry} (part : e ∈ rs) (src : e.1 = .field arg label lo hi) :
    (⟨e.2.lower,lo⟩ : Equation) ∈ (restriction (authorize p rs legit)).equations ∧
    (⟨e.2.upper,hi⟩ : Equation) ∈ (restriction (authorize p rs legit)).equations := by
  have low : (⟨e.2.lower,lo⟩ : Equation) ∈ writes e := by simp [writes,src]
  have high : (⟨e.2.upper,hi⟩ : Equation) ∈ writes e := by simp [writes,src]
  exact ⟨projected_row part low,projected_row part high⟩

/-- Existing supported payload heads survive the projection alias.
A variable payload with no observed head remains genuinely unknown. -/
theorem lower_name {s : State} {p : Supported s done} {legit : ∀ e ∈ rs, Certified p e}
    {e : Entry} (part : e ∈ rs) (src : e.1 = .field arg label (.variable n) hi)
    (known : Knows (restriction p) n tag) :
    Knows (restriction (authorize p rs legit)) e.2.lower tag := by
  have grown := GeneralDeclarativeLowerKnown321.knows_mono (s := restriction p)
    (t := restriction (authorize p rs legit)) rfl (fun _ h => old_kept h) known
  exact knows_alias (.forward (bounded_field part src).1) grown

open GeneralDeclarativeAggregate324 (span ready aggregates assembled)
open GeneralDeclarativeMerge320 (lower upper)
open GeneralDeclarativeCaptureClosure320 (withOrdinary)
open GeneralDeclarativeBounds319 (Bound)

theorem singleton_bounds {s : State} (keep : List Nat) (source : Capture)
    (fit : GeneralDeclarativeDemand320.Bounds s source) :
    Alias (ready s keep source []) (span s keep source []).lower source.lower ∧
    Alias (ready s keep source []) (span s keep source []).upper source.upper := by
  have all : ∀ x ∈ [source], GeneralDeclarativeDemand320.Bounds s x := by
    intro x part; cases List.mem_singleton.mp part; exact fit
  have merged := assembled (extra := keep) (seed := source) (rest := []) all
  have lo := merged.lowerEq
  have hi := merged.upperEq
  exact ⟨.bounds (.constraint (List.mem_append_left _ lo.1)) (.constraint (List.mem_append_left _ lo.2)),
    .bounds (.constraint (List.mem_append_left _ hi.1)) (.constraint (List.mem_append_left _ hi.2))⟩

end Yulang.GeneralDeclarativeEndpointSupport336
