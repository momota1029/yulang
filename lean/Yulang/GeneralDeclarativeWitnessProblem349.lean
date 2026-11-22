import Yulang.GeneralSourceMetadataBareBundle291
import Yulang.GeneralDeclarativeOutputSource323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessProblem349
open GeneralSourceMetadataBareBundle291 (InputBundle compile preserves_input)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralSourceMetadataRoleManifest291 (manifestRows exact_manifest)
open GeneralSourceMetadataDiagnostics291 (diagnostics no_diagnostics_iff)
open GeneralSourceMetadataRoles291 (Valid)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeHead320 (State)

structure Problem where
  source : InputBundle
  state : State
  demand : Demand

theorem splitAnd {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  simpa only [Bool.and_eq_true] using h

theorem splitOr {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  simpa only [Bool.or_eq_true] using h

def tables (s : SourceBundle) : Bool :=
  (GeneralSourceMetadataValidation291.check s.declared &&
    GeneralSourceMetadataValidation291.check s.snapshot) &&
  decide (GeneralSourceMetadataComparison291.compare s.declared s.snapshot [] = .compared .good)

def covered (s : SourceBundle) : Bool :=
  (diagnostics (registry s) (interpretation s.snapshot) (manifestRows s.roles)).isEmpty

theorem covered_iff {s : SourceBundle} (valid : Valid s.roles) :
    covered s = true ↔ Coverage (registry s) (interpretation s.snapshot) := by
  unfold covered
  rw [List.isEmpty_iff]
  exact no_diagnostics_iff _ _ _ (exact_manifest s.roles valid)

def declared (s : SourceBundle) (d : Demand) : Bool :=
  d.outputs.all (fun o => ((registry s).roles d.role).assoc o.name |>.isSome)

theorem declared_iff (s : SourceBundle) (d : Demand) :
    declared s d = true ↔ Declared (registry s) d := by
  rw [declared,List.all_eq_true]
  constructor
  · intro ok out used
    have fact := ok out used
    cases h : ((registry s).roles d.role).assoc out.name with
    | none => simp [h] at fact
    | some body => exact ⟨body,rfl⟩
  · intro ok out used
    obtain ⟨v,h⟩ := ok out used
    simp [h]

/-- The input bundle is taken from the caller's fixed problem, not from
the claimed witness. Even defaults of unused roles participate. -/
def first (p : Problem) : Option SourceBundle := do
  let s ← compile p.source
  if (tables s && covered s) && declared s p.demand then some s else none

theorem first_sound {p : Problem} {s : SourceBundle} (ok : first p = some s) :
    GeneralSourceMetadataBareBundle291.forget s = p.source ∧ Valid s.roles ∧ tables s = true ∧
    Coverage (registry s) (interpretation s.snapshot) ∧ Declared (registry s) p.demand := by
  unfold first at ok
  cases h : compile p.source with
  | none => simp [h] at ok
  | some data =>
    rw [h] at ok
    change (if (tables data && covered data) && declared data p.demand then some data else none) = some s at ok
    split at ok
    · rename_i checks
      cases Option.some.inj ok
      have parts := GeneralDeclarativeWitnessProblem349.splitAnd checks
      have tbl := GeneralDeclarativeWitnessProblem349.splitAnd parts.1
      obtain ⟨same,coherent⟩ := preserves_input p.source s h
      exact ⟨same,coherent,tbl.1,(covered_iff coherent).mp tbl.2,(declared_iff _ _).mp parts.2⟩
    · cases ok

end Yulang.GeneralDeclarativeWitnessProblem349
