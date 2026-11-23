import Yulang.GeneralDeclarativeWitnessDeclaredState357
import Yulang.GeneralDeclarativeWitnessClassify334

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessClassifyVariance357
open GeneralDeclarativeWitnessDeclaredState357
  (Current Joined ModelsCurrent Views Value pointSpans WrittenBody authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (Coverage DeclarationCovered)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarationPatterns (Pattern Smaller StableSmaller)
open GeneralDeclarations (Declaration Registry Checked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralSourceMetadataRows291 (interpretation)
open CommonRoleOutermostResolver (All₂ Frontier Tree Dictionary Result Classify Resolves Summarizes)
open CommonNominalFullCarrier (Equivalent)

def roleView (s : Current) (role : Nat) : Registry :=
  {authoredRegistry s with declarations := (authoredRegistry s).declarations.filter (fun d => d.role == role)}

theorem roleView_span (s : Current) (role : Nat) (decl : Declaration) :
    decl ∈ (roleView s role).declarations ↔ decl ∈ (authoredRegistry s).declarations ∧ decl.role = role := by
  simp [roleView]

structure DeclarationReady (r : Registry) (d : Declaration) : Prop where
  signature : d.Signature r.roles
  identified : d.Identified
  produced : d.Produced
  outputOnly : d.OutputOnly
  scopeOK : d.Scoped
  constructorScoped : d.ConstructorScoped r.constructors
  descent : ∀ c ∈ d.requirements,Smaller d.head c.arguments ∧ StableSmaller d.head c.arguments

def SourceChecked (s : Current) : Prop :=
  ((authoredRegistry s).declarations.map Declaration.id).Nodup ∧
    ∀ decl ∈ (authoredRegistry s).declarations,DeclarationReady (authoredRegistry s) decl

theorem of_ordinary {s : Current} (e : Checked (authoredRegistry s)) : SourceChecked s := by
  refine ⟨e.1,?_⟩
  intro decl found
  have d := e.2 decl found
  exact ⟨d.signature,d.identified,d.produced,d.outputOnly,d.scope,d.constructorScoped,
    fun c member => ⟨d.paterson c member,d.captureStable c member⟩⟩

structure JoinedLocal (s : Current) (d : Demand) (impl : Declaration) (kids : List Demand) where
  single : (roleView s d.role).declarations = [impl]
  head : Joined s d impl
  body : WrittenBody s d impl (pointSpans head.firstBinder head.lastBinder head.actualValue) kids

def JoinedMeaning (m : Assignment) (v : Views) {s : Current} {d impl kids} (l : JoinedLocal s d impl kids) : Prop :=
  (∃ a : Value, v l.head.actual = some a ∧ a.tag = l.head.tag ∧ a.name = l.head.name ∧
    a.arguments = [.inl (m l.head.actualValue).1]) ∧
  (∀ span ∈ pointSpans l.head.firstBinder l.head.lastBinder l.head.actualValue,
    Equivalent (m span.2.center).1 (.union (m l.head.firstValue).1 (m l.head.lastValue).1)) ∧
  l.body.finished.fixed.map Equation.left = d.outputs.map GeneralSourceState.Output.target ∧
  ∀ eq ∈ l.body.finished.fixed,Holds m eq

/-- Independent positive rules for the reached fragments. Ordinary
C334 enters only as an already ordinary role with all its declarations
present. Declared unary covariance enters by a new rule on authored rows
and the current source-derived mode, not via old Coverage. Otherwise the
absence of a constructor here says no verdict about source eligibility. -/
inductive Rule (s : Current) : Demand → Frontier Demand → Prop where
  | ordinary {p : Supported s.ordinary done} {waiting d res}
      (checked : Checked (roleView s d.role))
      (legacy : GeneralNominalCenteredHeadWFSource.Coverage (roleView s d.role)
        (interpretation s.environment.source.snapshot)) :
      GeneralDeclarativeWitnessClassify334.Rule p (roleView s d.role)
        (interpretation s.environment.source.snapshot) waiting d res → Rule s d res
  | join {d impl kids} :
      JoinedLocal s d impl kids → Rule s d (.selected impl.id kids)

inductive LocalEvidence (s : Current) (m : Assignment) (v : Views) :
    Demand → Nat → List Demand → Prop where
  | ordinary {d impl cap kids} :
      impl.id = key →
      Meaning (roleView s d.role) (interpretation s.environment.source.snapshot) m d impl cap kids →
      LocalEvidence s m v d key kids
  | join {d impl kids} (read : JoinedLocal s d impl kids) :
      DeclarationCovered s.environment impl → JoinedMeaning m v read → LocalEvidence s m v d impl.id kids

theorem local_sound {s : Current} (checked : SourceChecked s) (cover : Coverage s.environment)
    {d key kids} (selected : Rule s d (.selected key kids)) (declared : Declared (authoredRegistry s) d)
    (m : Assignment) (v : Views) (fit : ModelsCurrent s m v) :
    LocalEvidence s m v d key kids ∧ ∀ child ∈ kids,Declared (authoredRegistry s) child := by
  cases selected with
  | ordinary ordinaryChecked legacy rule =>
    have old := GeneralDeclarativeWitnessClassify334.local_sound ordinaryChecked legacy
      m fit.1 d declared key kids rule
    obtain ⟨⟨impl,cap,id,meaning⟩,ordered⟩ := old
    exact ⟨.ordinary id meaning,ordered⟩
  | @join _ impl _ read =>
    have live : impl ∈ (roleView s d.role).declarations := by rw [read.single]; exact List.mem_cons_self
    have visible := ((roleView_span s _ _).mp live).1
    obtain ⟨typed,whole⟩ := GeneralDeclarativeWitnessDeclaredState357.joined_values read.head m v fit
    exact ⟨.join read (cover.1 impl visible) ⟨typed,whole,GeneralDeclarativeWitnessDeclaredState357.output_meaning read.body m fit.1⟩,
      GeneralDeclarativeWitnessDeclaredState357.body_declared read.body (checked.2 impl visible).signature⟩

inductive Evidence (s : Current) (m : Assignment) (v : Views) : Demand → Dictionary → Prop where
  | node :
      LocalEvidence s m v d key kids →
      All₂ (Evidence s m v) kids dicts → Evidence s m v d (.node key dicts)

section
variable {s : Current} {m : Assignment} {v : Views}

mutual
theorem node_sound (checked : SourceChecked s) (cover : Coverage s.environment) (fit : ModelsCurrent s m v)
    (asked : Declared (authoredRegistry s) d) (tree : Tree) (dict : Dictionary)
    (resolves : Resolves (Rule s) d tree) (summarizes : Summarizes tree (.selected dict)) :
    Evidence s m v d dict := by
  cases resolves with
  | pending _ => cases summarizes
  | ambiguous _ => cases summarizes
  | rejected _ => cases summarizes
  | selected choice children =>
    obtain ⟨localProof,requests⟩ := local_sound checked cover choice asked m v fit
    cases summarizes with
    | selected results combined =>
      cases combined with
      | selected matching =>
        subst_vars
        exact .node localProof (list_sound checked cover fit requests _ _ children results)
termination_by sizeOf tree

theorem list_sound (checked : SourceChecked s) (cover : Coverage s.environment) (fit : ModelsCurrent s m v)
    (asked : ∀ d ∈ ds,Declared (authoredRegistry s) d) (trees : List Tree) (dicts : List Dictionary)
    (resolves : All₂ (Resolves (Rule s)) ds trees)
    (summarizes : All₂ Summarizes trees (dicts.map Result.selected)) :
    All₂ (Evidence s m v) ds dicts := by
  cases dicts with
  | nil => cases summarizes; cases resolves; exact .nil
  | cons first rest =>
    cases summarizes with
    | cons won later =>
      cases resolves with
      | cons has next =>
        exact .cons (node_sound checked cover fit (asked _ List.mem_cons_self) _ _ has won)
          (list_sound checked cover fit (fun d h => asked d (List.mem_cons_of_mem _ h)) _ _ next later)
termination_by sizeOf trees
end

end

theorem dictionary_sound {s : Current}
    (checked : SourceChecked s) (cover : Coverage s.environment)
    (asked : Declared (authoredRegistry s) d) (selected : Classify (Rule s) d (.selected dict)) :
    ∀ (m : Assignment) (v : Views), ModelsCurrent s m v → Evidence s m v d dict := by
  obtain ⟨tree,chart,result⟩ := selected
  exact fun _ _ valid => node_sound checked cover valid asked tree dict chart result

end Yulang.GeneralDeclarativeWitnessClassifyVariance357
