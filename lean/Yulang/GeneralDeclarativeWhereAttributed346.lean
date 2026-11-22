import Yulang.GeneralDeclarativeWhereEndpoint346
import Yulang.GeneralDeclarativeRawCapture344

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWhereAttributed346
open GeneralDeclarations (Registry)
open GeneralNominalCenters (Plan Site)
open GeneralWhereOriginDelta318 (Cell)
open GeneralWhereVersionInstall317 (Journal InstallStep Models install)
open GeneralDeclarativeWhereEndpoint346 (At)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedExpressionFrame236 (value_eq variable_value)
open GeneralNominalCenteredHeadMatExpressions (value)
open GeneralDeclarativeSubstitution320 (logical logical_value EquationRead)
open GeneralDeclarativeRawCapture344 (rawCap by_mode)
open GeneralDeclarativeHead320 (State Equation environment variables_eq)
open GeneralDeclarativeEntailment320 (appendFacts Holds model_append)
open GeneralDeclarativeOrigins321 (Origin Supported Backed Available restriction backed_iff from_completed)

def literal {p : Plan rs} (c : Cell p) : Equation :=
  ⟨c.row.target,logical (rawCap p) c.side.mode c.expression⟩

theorem model_exact {p : Plan rs} (c : Cell p) (m : Assignment) :
    Holds m (literal c) ↔ c.row.Holds (variables p m) m := by
  change CommonNominalFullCarrier.Equivalent (m c.row.target).1
      (value (environment m) .actual (logical (rawCap p) c.side.mode c.expression)) ↔
    CommonNominalFullCarrier.Equivalent (m c.row.target).1 (value (variables p m) c.side.mode c.expression)
  rw [logical_value]
  have rhs : value (GeneralDeclarativeWhere319.variables (rawCap p) m) c.side.mode c.expression =
      value (variables p m) c.side.mode c.expression := by
    apply value_eq
    intro r _
    rw [variables_eq,by_mode,variable_value]
  rw [rhs]

def attach {s : State} (orig : Supported s done) {before after : Journal rs} {p : Plan rs}
    {c : Cell p} {ord : Nat} {site : Site rs} (_written : At before after p c ord site) :
    Supported (appendFacts s [literal c]) done where
  derivesFrom row origin := orig.derivesFrom row origin ∨
    row = literal c ∧ origin = .output p.packet.site.occurrence.identity
  ordinary := by
    intro row o h
    rcases h with prior|⟨rfl,rfl⟩
    · exact List.mem_append_left _ (orig.ordinary prior)
    · exact List.mem_append_right _ List.mem_cons_self

theorem exact_backing {s : State} (orig : Supported s done) {before after : Journal rs}
    {p : Plan rs} {c : Cell p} {ord : Nat} {site : Site rs} (written : At before after p c ord site) :
    row ∈ (restriction (attach orig written)).equations ↔
      Backed orig row ∨ row = literal c ∧ done p.packet.site.occurrence.identity := by
  rw [backed_iff]
  constructor
  · rintro ⟨o,old|⟨rfl,rfl⟩,good⟩
    · exact .inl ⟨o,old,good⟩
    · cases good with
      | completed ready => exact .inr ⟨rfl,ready⟩
  · rintro (⟨o,old,good⟩|⟨rfl,done⟩)
    · exact ⟨o,.inl old,good⟩
    · exact ⟨_,.inr ⟨rfl,rfl⟩,.completed done⟩

theorem retained_model {s : State} {p : Plan rs} (c : Cell p) (m : Assignment)
    (ordinary : GeneralDeclarativeHead320.Models s m) (valid : c.row.Holds (variables p m) m) :
    GeneralDeclarativeHead320.Models (appendFacts s [literal c]) m := by
  apply (model_append m).mpr
  exact ⟨ordinary,fun row seen => (List.mem_singleton.mp seen).symm ▸ (model_exact c m).mpr valid⟩

/-- Even with the accepted raw row, completion is separately required
to reuse it in a source-supported query; no publication of unsupported
output evidence into the source slice. -/
theorem backed_read {s : State} (orig : Supported s done) {before after : Journal rs}
    {p : Plan rs} {c : Cell p} {ord : Nat} {site : Site rs} (written : At before after p c ord site)
    (settled : done p.packet.site.occurrence.identity) :
    EquationRead (restriction (attach orig written)) (rawCap p) c.side.mode c.row.target c.expression := by
  apply EquationRead.whole
  exact (exact_backing orig written).mpr (.inr ⟨rfl,settled⟩)

end Yulang.GeneralDeclarativeWhereAttributed346
