import Yulang.GeneralDeclarativeEntailment320

namespace Yulang.GeneralDeclarativeOrigins321
open GeneralDeclarativeHead320 (State Equation Models Read read_sound)
open GeneralDeclarativeEntailment320 (Entails)
open GeneralDeclarativeWhere319 (variables)
open GeneralNominalCenteredHeadMatExpressions (value)

inductive Origin where
  | source
  | output (demand : Nat)

/-- Origins justify use as input support, not ordinary truth. A logical
equation can have more than one independent justification. -/
inductive Available (completed : Nat → Prop) : Origin → Prop where
  | source : Available completed .source
  | completed : completed owner → Available completed (.output owner)

structure Supported (s : State) (completed : Nat → Prop) where
  derivesFrom : Equation → Origin → Prop
  ordinary : ∀ {eq o}, derivesFrom eq o → eq ∈ s.equations

def Backed (p : Supported s completed) (row : Equation) : Prop :=
  ∃ origin, p.derivesFrom row origin ∧ Available completed origin

noncomputable def restriction (p : Supported s completed) : State := by
  classical
  exact ⟨s.normal,s.equations.filter (fun row => decide (Backed p row))⟩

theorem backed_iff (p : Supported s completed) (row : Equation) :
    row ∈ (restriction p).equations ↔ Backed p row := by
  classical
  simp only [restriction,List.mem_filter,decide_eq_true_eq]
  exact ⟨And.right,fun h => ⟨p.ordinary h.choose_spec.1,h⟩⟩

theorem restrict_models (p : Supported s completed) (m)
    (valid : Models s m) : Models (restriction p) m :=
  ⟨valid.1,fun row present => valid.2 row (p.ordinary ((backed_iff p row).mp present).choose_spec.1)⟩

theorem supported_read (p : Supported s completed)
    (proof : Read (restriction p) capture mode name expr) (m) (valid : Models s m) :
    CommonNominalFullCarrier.Equivalent (m name).1 (value (variables capture m) mode expr) :=
  read_sound proof m (restrict_models p m valid)

theorem pending_only (p : Supported s completed) (row)
    (only : ∀ origin, p.derivesFrom row origin → ∃ owner, origin = .output owner ∧ ¬completed owner) :
    row ∉ (restriction p).equations := by
  intro available
  obtain ⟨origin,proven,settled⟩ := (backed_iff p row).mp available
  obtain ⟨owner,rfl,pending⟩ := only origin proven
  cases settled with
  | completed ready => exact pending ready

theorem ordinary_despite_pending (p : Supported s completed) {row}
    (fromOutput : p.derivesFrom row (.output owner)) : Entails s row :=
  fun _ model => model.2 row (p.ordinary fromOutput)

theorem from_source (p : Supported s completed) {row}
    (fromSource : p.derivesFrom row .source) : row ∈ (restriction p).equations :=
  (backed_iff p row).mpr ⟨.source,fromSource,.source⟩

theorem from_completed (p : Supported s completed) {row}
    (fromOutput : p.derivesFrom row (.output owner)) (ready : completed owner) :
    row ∈ (restriction p).equations :=
  (backed_iff p row).mpr ⟨.output owner,fromOutput,.completed ready⟩

end Yulang.GeneralDeclarativeOrigins321
