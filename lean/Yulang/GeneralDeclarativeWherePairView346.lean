import Yulang.GeneralDeclarativeWhereRelease346

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWherePairView346
open GeneralDeclarations (Registry)
open GeneralNominalCenters (Plan Site)
open GeneralWhereOriginDelta318 (Cell)
open GeneralWhereVersionInstall317 (Journal InstallStep Models install)
open GeneralDeclarativeWhereEndpoint346 (At)
open GeneralDeclarativeWhereBoth346 (polar paired)
open GeneralDeclarativeWhereRelease346 (Released attach backed)
open GeneralDeclarativeWhereAttributed346 (literal model_exact retained_model)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeEntailment320 (Holds appendFacts)
open GeneralDeclarativeOrigins321 (Supported Backed restriction backed_iff)
open GeneralDeclarativeRawCapture344 (rawCap)
open GeneralDeclarativeSubstitution320 (EquationRead)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Subtype)

def extendBounds (s : State) (c : Capture) : State :=
  ⟨⟨s.normal.ordinary,s.normal.intervals ++ [(c.lower,c.center),(c.center,c.upper)]⟩,s.equations⟩

def preserve {s : State} (p : Supported s done) (c : Capture) : Supported (extendBounds s c) done :=
  ⟨p.derivesFrom,p.ordinary⟩

theorem bounded_models {s : State} {c : Capture} (m : Assignment)
    (valid : GeneralDeclarativeHead320.Models s m)
    (first : Subtype (m c.lower).1 (m c.center).1) (last : Subtype (m c.center).1 (m c.upper).1) :
    GeneralDeclarativeHead320.Models (extendBounds s c) m := by
  refine ⟨⟨valid.1.1,?_⟩,valid.2⟩
  intro pair h
  rcases List.mem_append.mp h with prior|fresh
  · exact valid.1.2 pair prior
  · rcases List.mem_cons.mp fresh with rfl|rest
    · exact first
    · cases List.mem_singleton.mp rest
      exact last

theorem bounds {s : State} (c : Capture) (rows₁ rows₂ : List GeneralDeclarativeHead320.Equation) :
    Bounds (appendFacts (appendFacts (extendBounds s c) rows₁) rows₂) c := by
  exact ⟨.interval (List.mem_append_right _ List.mem_cons_self),
    .interval (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

/-- A single actual installed child produces both literal observations
and the true stored center in the same view. The raw model supplies
bounds; the externally grounded release supplies use as input support. -/
theorem view {r : Registry} {before : Journal rs} {ctx : GeneralNominalCandidates.Context} {p : Plan rs}
    (step : InstallStep r before (install before ctx p)) (c : Cell p)
    {s : State} (orig : Supported s done) (release : Released rs) (m : Assignment)
    (post : Models (install before ctx p) m)
    (valid : GeneralDeclarativeHead320.Models s m) :
    ∃ (ord : Nat) (site : Site rs) (cap : Capture)
      (low : At before (install before ctx p) p (polar c .lower) ord site)
      (high : At before (install before ctx p) p (polar c .upper) ord site),
      let p₀ := attach (preserve orig cap) low release
      let p₁ := attach p₀ high release
      cap.lower = (polar c .lower).row.target ∧ cap.upper = (polar c .upper).row.target ∧
      Bounds (appendFacts (appendFacts (extendBounds s cap) [literal (polar c .lower)]) [literal (polar c .upper)]) cap ∧
      GeneralDeclarativeHead320.Models
        (appendFacts (appendFacts (extendBounds s cap) [literal (polar c .lower)]) [literal (polar c .upper)]) m ∧
      (done p.packet.site.occurrence.identity →
        release p before.versionedWhere.length (before.mixed.core.sites.length + ord) c.index .lower →
        release p before.versionedWhere.length (before.mixed.core.sites.length + ord) c.index .upper →
        EquationRead (restriction p₁) (rawCap p) .lower cap.lower c.expression ∧
        EquationRead (restriction p₁) (rawCap p) .upper cap.upper c.expression) := by
  obtain ⟨ord,site,_,cap,_,lowName,_,highName,low,high,lo,hi⟩ := paired step c m post
  have planMem : p ∈ (install before ctx p).versionedWhere :=
    List.mem_iff_getElem?.mpr ⟨_,low.stamp⟩
  have packet := (post.2 p planMem).1
  have typed := retained_model (polar c .upper) m
    (retained_model (polar c .lower) m (bounded_models m valid lo hi) (packet.rows _ low.written))
    (packet.rows _ high.written)
  refine ⟨ord,site,cap,low,high,lowName,highName,bounds cap _ _,typed,?_⟩
  intro owner releasedLo releasedHi
  rw [lowName,highName]
  constructor
  · apply EquationRead.whole
    apply (backed _ high release).mpr
    apply Or.inl
    exact (backed_iff _ _).mp ((backed _ low release).mpr (.inr ⟨rfl,owner,releasedLo⟩))
  · exact GeneralDeclarativeWhereRelease346.with_release _ high owner releasedHi

end Yulang.GeneralDeclarativeWherePairView346
