import Yulang.GeneralDeclarativePackageBoundary344
import Yulang.GeneralDeclarativeObserverGrowth330

namespace Yulang.GeneralDeclarativeAmbient344
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeObserverGrowth330 (preserve backed_same)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeCommitPackage344 (Witness)
open GeneralDeclarativePackageBoundary344 (actual)
open GeneralNominalCenters (Plan)
open GeneralWhereVersionInstall317 (Journal InstallStep install)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralDeclarations (Registry)

def joined (old new : State) : State :=
  ⟨⟨old.normal.ordinary ++ new.normal.ordinary,old.normal.intervals ++ new.normal.intervals⟩,
    old.equations ++ new.equations⟩

theorem source_grows (a b : State) : Extends a (joined a b) :=
  ⟨fun _ h => List.mem_append_left _ h,fun _ h => List.mem_append_left _ h,fun _ h => List.mem_append_left _ h⟩

theorem both_models {a b : State} {m : Assignment} (first : Models a m) (last : Models b m) :
    Models (joined a b) m := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro atom inside
    exact (List.mem_append.mp inside).elim (first.1.1 atom) (last.1.1 atom)
  · intro interval inside
    exact (List.mem_append.mp inside).elim (first.1.2 interval) (last.1.2 interval)
  · intro row inside
    exact (List.mem_append.mp inside).elim (first.2 row) (last.2 row)

def origins {s : State} (p : Supported s done) (addition : State) : Supported (joined s addition) done :=
  preserve p (source_grows s addition)

theorem same_origin_rows {s : State} (p : Supported s done) (addition : State) (e : Equation) :
    e ∈ (restriction (origins p addition)).equations ↔ e ∈ (restriction p).equations :=
  backed_same p (source_grows s addition) e

/-- A separately established rooted source view survives an actual
raw replay. The replay does not manufacture independent source
provenance or promise that joining ordinary graphs preserves K2. -/
theorem with_source {r : Registry} {before : Journal rs} {ctx : GeneralNominalCandidates.Context} {p : Plan rs}
    (step : InstallStep r before (install before ctx p))
    (m : Assignment) (fit : GeneralWhereVersionInstall317.Models (install before ctx p) m)
    (source : State) (known : Models source m)
    (ready : Ready (install before ctx p).mixed.core p.packet.site.occurrence p)
    (protect : List Nat) :
    ∃ base replay ports whereRows rootRows n,
      Witness (install before ctx p) p m n (stateNames source ++ protect) base replay ports whereRows rootRows ∧
      Models (joined source replay) n ∧ (∀ k ∈ protect,n k = m k) := by
  obtain ⟨base,replay,ports,whereRows,rootRows,n,got⟩ :=
    actual step m fit (stateNames source ++ protect) ready
  have agrees : ∀ k ∈ stateNames source, m k = n k :=
    fun k used => (got.kept k (List.mem_append_left _ used)).symm
  exact ⟨base,replay,ports,whereRows,rootRows,n,got,both_models ((preserves_models source agrees).mp known) got.ordinary,
    fun _ h => got.kept _ (List.mem_append_right _ h)⟩

end Yulang.GeneralDeclarativeAmbient344
