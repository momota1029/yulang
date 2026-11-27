import Yulang.GeneralDeclarativeI65I74FiniteSourceShell461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
open GeneralDeclarationPatterns (StableSmaller)
open Checker408 (Problem)
open WrittenPattern460

/-- A producer of finite, independently reflected evidence of stability at
the actual original head and where. This interface does not assert that
StableSmaller itself has a finite decision procedure. -/
structure StableSourceProtocol (p : Problem) where
  Certificate : Type
  supports : OriginalAnchor p → Prop
  stability : ∀ a, supports a → StableSmaller a.declaration.head a.clause.arguments
  verifies : OriginalAnchor p → Certificate → Bool
  exact : ∀ a, (∃ cert, verifies a cert = true) ↔ supports a

structure SourceTicket {p : Problem} (h : StableSourceProtocol p) where
  source : AnchorAddress
  descent : h.Certificate

def readStableShell {p : Problem} (g : StableSourceProtocol p) (ticket : SourceTicket g) :
    Option (EligibleStart p) := do
  let a ← readFiniteSourceShell p ticket.source
  if yes : g.verifies a.1 ticket.descent = true then
    let support := (g.exact a.1).mp ⟨ticket.descent,yes⟩
    return joinActualStable a.2 (g.stability _ support)
  else none

def independentSourceEligibility {p : Problem}
    (g : StableSourceProtocol p) (a : EligibleStart p) : Prop :=
  ∃ (orig : OriginalAnchor p) (shell : StartShell p orig) (cert : g.supports orig),
    joinActualStable shell (g.stability orig cert) = a

theorem finite_source_shell_plus_genuine_stability_exact {p : Problem}
    (g : StableSourceProtocol p) (a : EligibleStart p) :
    (∃ w, readStableShell g w = some a) ↔ independentSourceEligibility g a := by
  constructor
  · rintro ⟨w,accepted⟩
    cases found : readFiniteSourceShell p w.source with
    | none => simp [readStableShell,found,Option.bind] at accepted
    | some a0 =>
      by_cases yes : g.verifies a0.1 w.descent = true
      · have exact : joinActualStable a0.2
            (g.stability _ ((g.exact a0.1).mp ⟨w.descent,yes⟩)) = a := by
          simpa [readStableShell,found,yes,Option.bind] using accepted
        exact ⟨a0.1,a0.2,(g.exact a0.1).mp ⟨w.descent,yes⟩,exact⟩
      · simp [readStableShell,found,yes,Option.bind] at accepted
  · rintro ⟨orig,shell,cert,rfl⟩
    obtain ⟨w,yes⟩ := (g.exact orig).mpr cert
    refine ⟨⟨orig.location,w⟩,?_⟩
    simp [readStableShell,actual_finite_shell_replays_without_any_stability_claim orig shell,
      yes,Option.bind]

def shellReadyReader {p : Problem} (g : StableSourceProtocol p) : ReadyRead p :=
  ⟨SourceTicket g,independentSourceEligibility g,readStableShell g,
    finite_source_shell_plus_genuine_stability_exact g⟩

theorem finite_stable_shell_and_compiled_path_give_the_exact_same_report {p : Problem}
    (g : StableSourceProtocol p) (r : RoutedReadyMixed457.ReportAtField) :
    (∃ w, readEligibleField (shellReadyReader g) w = some r) ↔
      EligibleScoped (shellReadyReader g) r :=
  exact_eligible_scope_iff_independent_finite_route _ _

end Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
