import Yulang.CommonNominalSiteGeneration
import Yulang.NominalConstructions

/-!
# Actual source generation for whole resolved nominal field declarations

All original fields and source sites are paired, with mismatched arities
rejected. The same type/row parameter vector instantiates every field template.
The declaration's nominal identity and enum constructor tag remain explicit.
Registry body constraints are generated once, in addition to every field's
source and deferred-boundary constraints and the nominal result bound.

Declarations here have already resolved names and finite graph references;
source declaration lookup/validation, weak EOF and a full generated-bound
all-instance solver are still separate obligations.
-/

namespace Yulang.CommonNominalFieldGeneration

open CommonNominalCarrier
open Core.PresenceGeneration (Comp CompTerm TyTerm RowTerm SchemeEnv Binding EnvRel)
open CommonNominalFieldTemplates (Term Formula Template TemplateRow)
open CommonNominalSourceRegistry (Registry Boundary)
open CommonNominalSiteGeneration (Site SitesTyping)

structure Field (types rows : Nat) where
  label : Nat
  template : Template types rows

structure SourceSite where
  position : Nat
  expression : Inference.Expr

structure Declaration (types rows : Nat) where
  constructor : NominalConstructions.Constructor
  parameters : List (Fin types ⊕ Fin rows)
  fields : List (Field types rows)

def Declaration.name (declaration : Declaration types rows) : Nat :=
  match declaration.constructor with
  | .listLiteral name | .structLiteral name | .enumConstructor name _ => name

def resultTemplate (name : Nat) (parameters : List (Fin types ⊕ Fin rows)) : Template types rows :=
  ⟨1, fun _ => .nominal name (parameters.map (Sum.map Sum.inr TemplateRow.var)), .inl 0⟩

def resultType (declaration : Declaration types rows) (arguments : Fin types → Ty)
    (rowArguments : Fin rows → Row) : Ty :=
  nominal declaration.name (declaration.parameters.map (Sum.map arguments rowArguments))

theorem result_template_exact (declaration : Declaration types rows) (arguments : Fin types → Ty)
    (rowArguments : Fin rows → Row) :
    (resultTemplate declaration.name declaration.parameters).eval arguments rowArguments =
      resultType declaration arguments rowArguments := by
  simp only [Template.eval, resultTemplate, CommonNominalGuardedClosure.instantiate_graph,
    CommonNominalFieldTemplates.rowsLayer, CommonNominalSyntax.Layer.map,
    resultType, nominal, List.map_map]
  congr 1
  apply List.map_congr_left
  intro parameter _
  cases parameter <;> rfl

def prepareSites (arguments : Fin types → TyTerm α) (rows : Fin rowCount → RowTerm α) :
    List (Field types rowCount) → List SourceSite → Option (List (Site α))
  | [], [] => some []
  | field :: rest, source :: tail =>
      (prepareSites arguments rows rest tail).map fun sites =>
        ⟨source.position, field.label, source.expression, .template field.template arguments rows⟩ :: sites
  | _, _ => none

/-- Independent source rules. Every fixed and parameterized field is checked
and contributes its source row. No generated formula occurs in this definition. -/
def FieldsTyping (registry : Registry vertices α) (assignment : α → Comp model)
    (environment : List (Binding model)) (arguments : Fin types → Ty) (rows : Fin rowCount → Row) :
    List (Field types rowCount) → List SourceSite → Row → Prop
  | [], [], output => Common.rowLe Common.rowEmpty output
  | field :: rest, site :: tail, output =>
      ∃ source suffix, Core.PresenceGeneration.Typing model environment site.expression source ∧
        Boundary registry assignment source.1 (field.template.eval arguments rows) ∧
        FieldsTyping registry assignment environment arguments rows rest tail suffix ∧
        Common.rowLe (Common.rowJoin source.2 suffix) output
  | _, _, _ => False

private theorem prepared_cons_exact (registry : Registry vertices α) (assignment : α → Comp model)
    (environment : List (Binding model)) (site : Site α) (prepared : Option (List (Site α))) (row : Row) :
    (∃ sites, prepared.map (site :: ·) = some sites ∧ SitesTyping registry assignment environment sites row) ↔
      ∃ source suffix, Core.PresenceGeneration.Typing model environment site.expression source ∧
        Boundary registry assignment source.1 (site.target.eval assignment) ∧
        (∃ sites, prepared = some sites ∧ SitesTyping registry assignment environment sites suffix) ∧
        Common.rowLe (Common.rowJoin source.2 suffix) row := by
  cases prepared with
  | none => simp
  | some sites =>
      simp only [Option.map_some, Option.some.injEq, exists_eq_left']
      constructor
      · intro typed
        cases typed with
        | cons source boundary tail below => exact ⟨_, _, source, boundary, tail, below⟩
      · rintro ⟨_, _, source, boundary, tail, below⟩
        exact .cons source boundary tail below

theorem prepare_sites_exact (registry : Registry vertices α) (assignment : α → Comp model)
    (environment : List (Binding model)) (arguments : Fin types → TyTerm α)
    (rows : Fin rowCount → RowTerm α) (fields : List (Field types rowCount)) (sources : List SourceSite) (row : Row) :
    (∃ sites, prepareSites arguments rows fields sources = some sites ∧
      SitesTyping registry assignment environment sites row) ↔
    FieldsTyping registry assignment environment
      (fun index => (arguments index).eval model assignment) (fun index => (rows index).eval model assignment)
      fields sources row := by
  induction fields generalizing sources row with
  | nil =>
      cases sources with
      | nil =>
          simp only [prepareSites, Option.some.injEq, exists_eq_left', FieldsTyping]
          constructor
          · intro typed; cases typed with | nil below => exact below
          · exact .nil
      | cons _ _ => simp [prepareSites, FieldsTyping]
  | cons field rest ih =>
      cases sources with
      | nil => simp [prepareSites, FieldsTyping]
      | cons site tail =>
          rw [prepareSites, prepared_cons_exact]
          simp only [ih, FieldsTyping, Term.eval]

/-- Original source positions, expressions, field IDs and whole templates are
retained in order, including fixed fields and repeated parameter occurrences. -/
theorem prepare_sites_retains_all (arguments : Fin types → TyTerm α) (rows : Fin rowCount → RowTerm α)
    (fields : List (Field types rowCount)) (sources : List SourceSite) (sites : List (Site α))
    (prepared : prepareSites arguments rows fields sources = some sites) :
    sites.map (fun site => (site.position, site.expression)) = sources.map (fun site => (site.position, site.expression)) ∧
    sites.map Site.field = fields.map Field.label ∧
    sites.map Site.target = fields.map (fun field => Term.template field.template arguments rows) := by
  induction fields generalizing sources sites with
  | nil =>
      cases sources <;> simp [prepareSites] at prepared
      subst sites
      exact ⟨rfl, rfl, rfl⟩
  | cons field rest ih =>
      cases sources with
      | nil => simp [prepareSites] at prepared
      | cons source tail =>
          cases found : prepareSites arguments rows rest tail with
          | none => simp [prepareSites, found] at prepared
          | some remaining =>
              simp only [prepareSites, found, Option.map_some, Option.some.injEq] at prepared
              subst sites
              obtain ⟨sourceSame, fieldSame, targetSame⟩ := ih tail remaining found
              exact ⟨by simp only [List.map_cons, sourceSame],
                by simp only [List.map_cons, fieldSame], by simp only [List.map_cons, targetSame]⟩

def generate (registry : Registry vertices α) (environment : SchemeEnv α)
    (declaration : Declaration types rows) (sources : List SourceSite)
    (arguments : Fin types → TyTerm α) (rowArguments : Fin rows → RowTerm α) (output : CompTerm α) : Formula α :=
  .and (registry.generate environment)
    (.and (.tyLe (.template (resultTemplate declaration.name declaration.parameters) arguments rowArguments) (.ordinary output.ty))
      (match prepareSites arguments rowArguments declaration.fields sources with
      | none => .ordinary .bot
      | some sites => CommonNominalSiteGeneration.generateSites registry environment sites output.row))

def ConstructionTyping (registry : Registry vertices α) (assignment : α → Comp model)
    (environment : List (Binding model)) (declaration : Declaration types rows) (sources : List SourceSite)
    (arguments : Fin types → Ty) (rowArguments : Fin rows → Row) (output : Comp model) : Prop :=
  registry.Valid environment assignment ∧
    CommonNominalCarrier.Subtype (resultType declaration arguments rowArguments) output.1 ∧
    FieldsTyping registry assignment environment arguments rowArguments declaration.fields sources output.2

/-- Exact finite generation for every resolved field declaration, every
original source-site list, every shared type/row assignment and output. The
same original captured environment verifies cast bodies and all source sites. -/
theorem generate_fields_exact (registry : Registry vertices α) (symbolic : SchemeEnv α)
    (environment : List (Binding model)) (assignment : α → Comp model)
    (declaration : Declaration types rows) (sources : List SourceSite)
    (arguments : Fin types → TyTerm α) (rowArguments : Fin rows → RowTerm α) (output : CompTerm α)
    (related : EnvRel model assignment symbolic environment) :
    (generate registry symbolic declaration sources arguments rowArguments output).Models assignment ↔
      ConstructionTyping registry assignment environment declaration sources
        (fun index => (arguments index).eval model assignment)
        (fun index => (rowArguments index).eval model assignment) (output.eval model assignment) := by
  have fieldExact :
      (match prepareSites arguments rowArguments declaration.fields sources with
      | none => Formula.ordinary .bot
      | some sites => CommonNominalSiteGeneration.generateSites registry symbolic sites output.row).Models assignment ↔
      FieldsTyping registry assignment environment
        (fun index => (arguments index).eval model assignment)
        (fun index => (rowArguments index).eval model assignment) declaration.fields sources
        (output.row.eval model assignment) := by
    apply Iff.trans ?_ (prepare_sites_exact registry assignment environment arguments rowArguments
      declaration.fields sources (output.row.eval model assignment))
    cases prepared : prepareSites arguments rowArguments declaration.fields sources with
    | none => simp [Formula.Models, Core.PresenceGeneration.Formula.Holds]
    | some sites =>
        simp only [Option.some.injEq, exists_eq_left']
        exact CommonNominalSiteGeneration.generate_sites_exact registry symbolic environment assignment sites output.row related
  change _ ↔ registry.Valid environment assignment ∧ _ ∧ _
  simp only [generate, Formula.Models]
  exact and_congr (registry.generate_exact symbolic environment assignment related)
    (and_congr (by
      exact (congrArg (fun type => CommonNominalCarrier.Subtype type (output.ty.eval model assignment))
        (result_template_exact declaration (fun index => (arguments index).eval model assignment)
          (fun index => (rowArguments index).eval model assignment))).to_iff) fieldExact)

end Yulang.CommonNominalFieldGeneration
