import Yulang.GeneralDeclarativeOrdinaryProducer322
import Yulang.GeneralDeclarativeEmissionFixture322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeProducerFixture322
open GeneralDeclarativeExistingFixture322 (state supported parentCapture pointBounds rootBounds equations product nominalCode valid)
open GeneralDeclarativeExistingFixtureRead322 (hit rootReturn head)
open GeneralDeclarativeEmissionFixture322 (place no_materializer_needed)
open GeneralDeclarativeExampleSource320 (registry interp root leaf child checked)
open GeneralDeclarationExamples (wrap constructors roles outDefinition containerChild bareRole outputRole binaryRole)
open GeneralDeclarativeTermWalk322 (Occurrence Walk)
open GeneralDeclarativeTermCapture322 (Shared KnownNames named first)
open GeneralDeclarativeOrdinaryProducer322 (namesOf Residual ordinary_produces)
open GeneralDeclarativeNameLookup322 (singleton_exact)
open GeneralDeclarativeTermCapturedHead322 (ActualSyntax)
open GeneralNominalCenteredHeadWFSource (ConstructorUse Coverage DeclarationCovered)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeEmissionOperands322 (Compound)
open GeneralDeclarativeEmissionOutputs322 (Direct)
open GeneralDeclarativeEntailment320 (BatchRecipe)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleOutermostResolver (All₂)

abbrev occurrence : Occurrence := ⟨0,.actual,product⟩
abbrev pool (_ : Nat) : List Nat := [3]

theorem nominal_use : ConstructorUse registry.constructors interp 0 1 :=
  ⟨⟨[.type],0⟩,rfl,rfl,.inr ⟨rfl,rfl⟩⟩

theorem metadata : Coverage registry interp := by
  constructor
  · intro impl visible
    rcases List.mem_cons.mp visible with rfl|last
    · refine ⟨⟨⟨nominal_use,trivial,trivial⟩,trivial⟩,?_,?_⟩
      · intro clause included
        cases List.mem_singleton.mp included
        exact ⟨⟨trivial,trivial⟩,fun equation h => by cases List.mem_singleton.mp h; trivial⟩
      · intro eq included
        cases List.mem_singleton.mp included
        exact ⟨nominal_use,trivial,trivial⟩
    · cases List.mem_singleton.mp last
      refine ⟨⟨trivial,trivial⟩,?_,?_⟩
      · intro _ h
        cases h
      · intro eq h
        cases List.mem_singleton.mp h
        trivial
  · intro role name term declared
    change (roles role).assoc name = some (some term) at declared
    have never (key : Nat) : (outputRole key).assoc name ≠ some (some term) := by
      by_cases same : name = key <;> simp [same]
    by_cases one : role = 1
    · subst role
      exact False.elim (never 0 declared)
    · by_cases two : role = 2
      · subst role
        exact False.elim (never 1 declared)
      · by_cases four : role = 4
        · subst role
          cases declared
        · simp [roles,one,two,four,bareRole] at declared

theorem observed : ActualSyntax state registry interp root wrap [occurrence] :=
  ⟨.cons ⟨⟨nominal_use,trivial,trivial⟩,nominalCode product,head,[occurrence],
    hit 1 (nominalCode product) (by simp [equations]),rfl,.nominal (.cons .capture .nil),
    fun _ h => h⟩ .nil⟩

theorem shared : Shared state [occurrence] := by
  intro a one b two _ _ _
  cases List.mem_singleton.mp one
  cases List.mem_singleton.mp two
  exact .refl _

theorem anchored : KnownNames state [occurrence] pool := by
  intro found selected _
  cases List.mem_singleton.mp selected
  exact ⟨3,List.mem_cons_self,hit 3 product (by simp [equations])⟩

theorem actual_map : (namesOf state [occurrence] pool parentCapture).input = parentCapture := by
  funext n
  by_cases same : n = 0
  · subst n
    have choose : GeneralDeclarativeNameLookup322.find state [3] product = some 3 :=
      singleton_exact (hit 3 product (by simp [equations]))
    simp [namesOf,named,first,parentCapture,choose,GeneralDeclarativeExampleSource320.point]
  · have other : 0 ≠ n := Ne.symm same
    simp [namesOf,named,first,other]

theorem residual :
    Residual state registry interp root wrap (namesOf state [occurrence] pool parentCapture) place := by
  constructor
  · intro binder inHead
    rw [actual_map]
    change binder ∈ [0] at inHead
    cases List.mem_singleton.mp inHead
    exact pointBounds 3
  · intro arg found
    cases List.mem_singleton.mp found
    exact rootBounds
  · intro clause belongs i pat code there _ notVar
    cases List.mem_singleton.mp belongs
    have eq := List.mem_singleton.mp (List.mem_of_getElem? there)
    subst pat
    exact False.elim (notVar 0 rfl)
  · intro clause listed eqn used code _ notDirect
    cases List.mem_singleton.mp listed
    cases List.mem_singleton.mp used
    exact False.elim (notDirect ⟨1,rfl,List.mem_cons_self⟩)
  · intro out present
    cases List.mem_singleton.mp present
    exact ⟨none,rfl⟩
  · intro out asked body provided code compiled
    cases List.mem_singleton.mp asked
    rw [actual_map]
    cases provided with
    | explicit eq found name =>
      cases List.mem_singleton.mp found
      have normalized : code = .nominal 0 [.variable 1] := Option.some.inj compiled.symm
      subst code
      exact .trans (hit 6 (.variable 14) (by simp [equations]))
        (.trans (hit 14 (nominalCode (.variable 15)) (by simp [equations]))
          (.nominal (.cons (hit 15 (.variable 5) (by simp [equations])) .nil)))
    | default rhs _ impossible =>
      change some (none : Option Roles.Term) = some (some rhs) at impossible
      cases Option.some.inj impossible

theorem produced : BatchRecipe state registry interp root wrap.id
    (children wrap (namesOf state [occurrence] pool parentCapture) place) :=
  ordinary_produces (p := supported) checked metadata List.mem_cons_self rfl observed shared anchored residual

end Yulang.GeneralDeclarativeProducerFixture322
