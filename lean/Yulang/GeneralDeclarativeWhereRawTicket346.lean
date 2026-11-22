import Yulang.GeneralDeclarativeWhereRawAtoms346
import Yulang.GeneralWhereOriginInstall318

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWhereRawTicket346
open GeneralNominalCenters (Plan)
open GeneralWhereVersionInstall317 (Journal Models)
open GeneralWhereOriginDelta318 (Cell Delta)
open GeneralWhereOriginTrace318 (rawOf)
open GeneralWhereOriginInstall318 (RawTicket)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralNominalCommonBridge (Assignment assignment)
open GeneralNominalVersionedPlans231 (variables)
open GeneralWherePhysicalBase319 (Layout expand)
open GeneralWherePhysicalNominal319 (Extra models_iff)
open GeneralWherePhysicalDeferred319 (laid deferred noAdded)
open GeneralDeclarativeWhereRawAtoms346 (batch batch_exact)

def emitted {j : Journal rs} {p : Plan rs} {n : Nat} (l : Layout (rawOf j).base n)
    (selected : List (Cell p)) : Option (Extra (rawOf j) n) :=
  batch (expand l []) selected

theorem extended_models {j : Journal rs} {p : Plan rs} {n : Nat}
    (l : Layout (rawOf j).base n) {selected : List (Cell p)}
    {atoms : Extra (rawOf j) n} (ran : emitted l selected = some atoms) (m : Assignment) :
    GeneralNominalState.Models (laid (rawOf j) l atoms) m ↔
      GeneralNominalState.Models (rawOf j) m ∧
      (∀ c ∈ selected,c.row.Holds (variables p m) m) := by
  rw [models_iff]
  have exact := batch_exact ran m
  change PresenceNormalForm.All CommonNominalFullCarrier.model
    (assignment (expand l atoms) m) atoms ↔ _ at exact
  exact and_congr_right (fun _ => exact)

/-- Structural fresh writes are compiled literally, rather than
assumed as a model-preserving observer update. The ticket follows from
the actual materialized rows and layout, independently of output Ready. -/
theorem gives_ticket {j : Journal rs} {p : Plan rs} {n : Nat}
    (l : Layout (rawOf j).base n) {selected : List (Cell p)}
    {atoms : Extra (rawOf j) n} (ran : emitted l selected = some atoms)
    {ctx : GeneralNominalCandidates.Context} (actual : ctx.state = laid (rawOf j) l atoms) :
    RawTicket j p ctx := by
  intro m valid packet
  rw [actual,(extended_models l ran m)]
  exact ⟨valid.1.1.1,fun c _ => packet.rows c.row c.written.1⟩

end Yulang.GeneralDeclarativeWhereRawTicket346
