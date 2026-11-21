import Yulang.GeneralDeclarativeExistingFixture322
import Yulang.GeneralDeclarativeEndpointProbe321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeExistingFixtureProbe322
open GeneralDeclarativeExistingFixture322
open GeneralDeclarativeExampleSource320 (registry interp input root leaf)
open GeneralDeclarationExamples (wrap)
open GeneralDeclarativeOrigins321 (restriction from_source)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeLowerKnown321 (Ready Alias Knows knows_alias knows_row alias_refl)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralNominalCenteredHeadMatExpressions (Expr)

theorem low : (⟨0,nominalCode (.variable 3)⟩ : Equation) ∈ (restriction supported).equations :=
  from_source supported ⟨by simp [equations],rfl,by simp [inputOnly]⟩

theorem high : (⟨2,nominalCode (.variable 4)⟩ : Equation) ∈ (restriction supported).equations :=
  from_source supported ⟨by simp [equations],rfl,by simp [inputOnly]⟩

theorem pairRow : (⟨3,product⟩ : Equation) ∈ (restriction supported).equations :=
  from_source supported ⟨by simp [equations],rfl,by simp [inputOnly]⟩

theorem childAlias : Alias (restriction supported) 8 3 :=
  .forward (from_source supported ⟨by simp [equations],rfl,by simp [inputOnly]⟩)

theorem readyRoot : Ready supported root := by
  intro arg known
  cases List.mem_singleton.mp known
  exact ⟨_,knows_row low rfl⟩

theorem readyChild : Ready supported child := by
  intro arg known
  cases List.mem_singleton.mp known
  exact ⟨_,knows_alias childAlias (knows_row pairRow rfl)⟩

theorem rootMatches : HeadMatches (restriction supported) registry.constructors interp root wrap := by
  let expected : Expr := .nominal 0 [.variable 0]
  have one : Trace (restriction supported) .lower 0 expected [⟨0,.actual,3⟩] :=
    .nominal (args := [3]) (alias_refl _) low (.cons .capture .nil)
  have two : Trace (restriction supported) .upper 2 expected [⟨0,.actual,4⟩] :=
    .nominal (args := [4]) (alias_refl _) high (.cons .capture .nil)
  exact .cons ⟨rootBounds,expected,_,_,rfl,one,two⟩ .nil

theorem childMatches : HeadMatches (restriction supported) registry.constructors interp child leaf :=
  .cons ⟨childBounds,.variable 0,[⟨0,.lower,8⟩],[⟨0,.upper,10⟩],rfl,.capture,.capture⟩ .nil

end Yulang.GeneralDeclarativeExistingFixtureProbe322
