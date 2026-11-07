import Yulang.CommonNominalCoreSiteGeneration
import Yulang.CommonNominalFieldNormalForm

/-!
# Whole original Core construction fields and actual finite generation

This is the literal-bearing Core counterpart of FieldGeneration. It reuses the
same resolved declaration, arbitrary mixed type/row parameter order and full
regular field templates. Every original Core source site is retained. Cast
body validity is generated once with the same original captured environment.

The source judgment is the original independent common Core judgment at
Signature.empty. Feature extensions, declaration verification, all-bound
solving, source evaluation and weak EOF remain separate obligations.
-/

namespace Yulang.CommonNominalCoreFieldGeneration

open CommonNominalCarrier
open Core.PresenceGeneration (Comp CompTerm TyTerm RowTerm SchemeEnv Binding EnvRel)
open CommonNominalFieldTemplates (Term Formula Template)
open CommonNominalCoreCastRegistry (Registry)
open CommonNominalCoreSiteGeneration (Site SitesTyping Boundary)

abbrev Field := CommonNominalFieldGeneration.Field
abbrev Declaration := CommonNominalFieldGeneration.Declaration
abbrev resultTemplate (name : Nat) (parameters : List (Fin types ⊕ Fin rows)) :=
  CommonNominalFieldGeneration.resultTemplate name parameters
abbrev resultType (declaration : Declaration types rows) (arguments : Fin types → Ty)
    (rowArguments : Fin rows → Row) := CommonNominalFieldGeneration.resultType declaration arguments rowArguments

structure SourceSite where
  position : Nat
  expression : Core.CommonSyntax.Term

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
    (environment : List (Core.CommonSyntax.Binding model)) (arguments : Fin types → Ty) (rows : Fin rowCount → Row) :
    List (Field types rowCount) → List SourceSite → Row → Prop
  | [], [], output => Common.rowLe Common.rowEmpty output
  | field :: rest, site :: tail, output =>
      ∃ source suffix, Core.CommonSyntax.Typing model environment site.expression source ∧
        Boundary registry assignment source.1 (field.template.eval arguments rows) ∧
        FieldsTyping registry assignment environment arguments rows rest tail suffix ∧
        Common.rowLe (Common.rowJoin source.2 suffix) output
  | _, _, _ => False

private theorem prepared_cons_exact (registry : Registry vertices α) (assignment : α → Comp model)
    (environment : List (Core.CommonSyntax.Binding model)) (site : Site α) (prepared : Option (List (Site α))) (row : Row) :
    (∃ sites, prepared.map (site :: ·) = some sites ∧ SitesTyping registry assignment environment sites row) ↔
      ∃ source suffix, Core.CommonSyntax.Typing model environment site.expression source ∧
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
    (environment : List (Core.CommonSyntax.Binding model)) (arguments : Fin types → TyTerm α)
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
    sites.map Site.field = fields.map CommonNominalFieldGeneration.Field.label ∧
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
      | some sites => CommonNominalCoreSiteGeneration.generateSites registry environment sites output.row))

def ConstructionTyping (registry : Registry vertices α) (assignment : α → Comp model)
    (environment : List (Core.CommonSyntax.Binding model)) (declaration : Declaration types rows) (sources : List SourceSite)
    (arguments : Fin types → Ty) (rowArguments : Fin rows → Row) (output : Comp model) : Prop :=
  registry.Valid environment assignment ∧
    CommonNominalCarrier.Subtype (resultType declaration arguments rowArguments) output.1 ∧
    FieldsTyping registry assignment environment arguments rowArguments declaration.fields sources output.2

/-- Exact finite generation for every resolved field declaration, every
original source-site list, every shared type/row assignment and output. The
same original captured environment verifies cast bodies and all source sites. -/
theorem generate_fields_exact (registry : Registry vertices α) (symbolic : SchemeEnv α)
    (environment : List (Core.CommonSyntax.Binding model)) (assignment : α → Comp model)
    (declaration : Declaration types rows) (sources : List SourceSite)
    (arguments : Fin types → TyTerm α) (rowArguments : Fin rows → RowTerm α) (output : CompTerm α)
    (sourceEnvironment : List (Binding model))
    (actualRelated : Core.CommonSyntax.EnvRel model environment sourceEnvironment)
    (related : EnvRel model assignment symbolic sourceEnvironment) :
    (generate registry symbolic declaration sources arguments rowArguments output).Models assignment ↔
      ConstructionTyping registry assignment environment declaration sources
        (fun index => (arguments index).eval model assignment)
        (fun index => (rowArguments index).eval model assignment) (output.eval model assignment) := by
  have fieldExact :
      (match prepareSites arguments rowArguments declaration.fields sources with
      | none => Formula.ordinary .bot
      | some sites => CommonNominalCoreSiteGeneration.generateSites registry symbolic sites output.row).Models assignment ↔
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
        exact CommonNominalCoreSiteGeneration.generate_sites_exact registry symbolic environment assignment sites output.row sourceEnvironment actualRelated related
  change _ ↔ registry.Valid environment assignment ∧ _ ∧ _
  simp only [generate, Formula.Models]
  exact and_congr (registry.generate_exact symbolic environment sourceEnvironment assignment actualRelated related)
    (and_congr (by
      exact (congrArg (fun type => CommonNominalCarrier.Subtype type (output.ty.eval model assignment))
        (CommonNominalFieldGeneration.result_template_exact declaration (fun index => (arguments index).eval model assignment)
          (fun index => (rowArguments index).eval model assignment))).to_iff) fieldExact)


/-- Actual original Core field expressions have the same exact finite numeric
constraint-set semantics, with every ambient computation fixed literally. -/
theorem construction_atomic_exact
    (registry : CommonNominalCoreCastRegistry.Registry vertices (Fin ambient))
    (symbolic : Core.PresenceGeneration.SchemeEnv (Fin ambient))
    (environment : List (Core.CommonSyntax.Binding model)) (assignment : Fin ambient → Comp model)
    (declaration : CommonNominalCoreFieldGeneration.Declaration types rows)
    (sources : List CommonNominalCoreFieldGeneration.SourceSite)
    (arguments : Fin types → Core.PresenceGeneration.TyTerm (Fin ambient))
    (rowArguments : Fin rows → RowTerm (Fin ambient)) (output : Core.PresenceGeneration.CompTerm (Fin ambient))
    (sourceEnvironment : List (Core.PresenceGeneration.Binding model))
    (actualRelated : Core.CommonSyntax.EnvRel model environment sourceEnvironment)
    (related : Core.PresenceGeneration.EnvRel model assignment symbolic sourceEnvironment) :
    CommonNominalCoreFieldGeneration.ConstructionTyping registry assignment environment declaration sources
      (fun index => (arguments index).eval model assignment)
      (fun index => (rowArguments index).eval model assignment) (output.eval model assignment) ↔
      ∃ clause ∈ CommonNominalFieldNormalForm.normalise (CommonNominalCoreFieldGeneration.generate registry symbolic declaration sources arguments rowArguments output),
        ∃ values : Fin (clause.locals + ambient) → Comp model,
          (∀ index, values (Fin.natAdd clause.locals index) = assignment index) ∧ CommonNominalFieldNormalForm.All values clause.pack := by
  rw [← CommonNominalCoreFieldGeneration.generate_fields_exact registry symbolic environment assignment
    declaration sources arguments rowArguments output sourceEnvironment actualRelated related]
  exact (CommonNominalFieldNormalForm.normalise_exact assignment _).symm.trans (by
    apply exists_congr
    intro clause
    exact and_congr Iff.rfl (clause.pack_exact assignment))

end Yulang.CommonNominalCoreFieldGeneration
