import Yulang.CommonNominalCoreCastRegistry

/-!
# Whole ordered construction sites over regular Common field templates

Every site retains its original source expression, position and field ID. The
generator allocates distinct source and suffix-row slots and emits the actual
source constraints, a deferred registry boundary, and the aggregate row
constraint. Target templates may mention several shared invariant parameters.

The independent typing rule does not call the generator. Exactness concerns
finite generation, not the remaining all-instance solver or source evaluator.
Source expressions are original literal-bearing Core terms. The original
Common constructor judgment is used, without changing the public entry;
feature extensions outside that judgment and source evaluation remain open.
-/

namespace Yulang.CommonNominalCoreSiteGeneration

open CommonNominalCarrier
open Core.PresenceGeneration (Comp CompTerm TyTerm RowTerm SchemeEnv Binding EnvRel extend)
open CommonNominalFieldTemplates (Term Formula Template)
open CommonNominalCoreCastRegistry (Registry)

abbrev Boundary (registry : Registry vertices α) := CommonNominalSourceRegistry.Boundary registry.lowered

def generateBoundary (registry : Registry vertices α) (source target : Term α) : Formula α :=
  CommonNominalSourceRegistry.generateBoundary registry.lowered source target

private theorem boundary_rename (registry : Registry vertices α) (rename : α → β)
    (assignment : β → Comp model) (source target : Ty) :
    Boundary (registry.rename rename) assignment source target ↔ Boundary registry (assignment ∘ rename) source target :=
  CommonNominalSourceRegistry.boundary_rename registry.lowered rename assignment source target

private theorem generate_boundary_exact (registry : Registry vertices α) (assignment : α → Comp model)
    (source target : Term α) :
    (generateBoundary registry source target).Models assignment ↔ Boundary registry assignment (source.eval assignment) (target.eval assignment) :=
  CommonNominalSourceRegistry.generate_boundary_exact registry.lowered assignment source target

structure Site (α : Type) where
  position : Nat
  field : Nat
  expression : Core.CommonSyntax.Term
  target : Term α

def Site.rename (site : Site α) (rename : α → β) : Site β :=
  ⟨site.position, site.field, site.expression, site.target.rename rename⟩

inductive SitesTyping (registry : Registry vertices α) (assignment : α → Comp model)
    (environment : List (Core.CommonSyntax.Binding model)) : List (Site α) → Row → Prop where
  | nil : Common.rowLe Common.rowEmpty result → SitesTyping registry assignment environment [] result
  | cons : Core.CommonSyntax.Typing model environment site.expression source →
      Boundary registry assignment source.1 (site.target.eval assignment) →
      SitesTyping registry assignment environment rest suffix →
      Common.rowLe (Common.rowJoin source.2 suffix) result →
      SitesTyping registry assignment environment (site :: rest) result

private theorem sites_nil_iff (registry : Registry vertices α) (assignment : α → Comp model)
    (environment : List (Core.CommonSyntax.Binding model)) (result : Row) :
    SitesTyping registry assignment environment [] result ↔ Common.rowLe Common.rowEmpty result := by
  constructor
  · intro typed; cases typed with | nil below => exact below
  · exact .nil

private theorem sites_cons_iff (registry : Registry vertices α) (assignment : α → Comp model)
    (environment : List (Core.CommonSyntax.Binding model)) (site : Site α) (rest : List (Site α)) (result : Row) :
    SitesTyping registry assignment environment (site :: rest) result ↔
      ∃ source suffix, Core.CommonSyntax.Typing model environment site.expression source ∧
        Boundary registry assignment source.1 (site.target.eval assignment) ∧
        SitesTyping registry assignment environment rest suffix ∧
        Common.rowLe (Common.rowJoin source.2 suffix) result := by
  constructor
  · intro typed
    cases typed with
    | cons source boundary suffix below => exact ⟨_, _, source, boundary, suffix, below⟩
  · rintro ⟨_, _, source, boundary, suffix, below⟩
    exact .cons source boundary suffix below

private def liftName : α → Option (Option α) := fun index => some (some index)

def generateSites (registry : Registry vertices α) (environment : SchemeEnv α) :
    List (Site α) → RowTerm α → Formula α
  | [], output => .ordinary (.rowLe .empty output)
  | site :: rest, output => .existsSlot (.existsSlot (
      .and (.ordinary (Core.CommonSyntax.generateNominalCore
        (Core.PresenceGeneration.env₂ environment) site.expression Core.PresenceGeneration.fresh₀))
      (.and (generateBoundary (registry.rename liftName)
        (.ordinary Core.PresenceGeneration.fresh₀.ty) (site.target.rename liftName))
      (.and (generateSites (registry.rename liftName) (Core.PresenceGeneration.env₂ environment)
        (rest.map fun site => site.rename liftName) Core.PresenceGeneration.fresh₁.row)
        (.ordinary (.rowLe (.join Core.PresenceGeneration.fresh₀.row Core.PresenceGeneration.fresh₁.row)
          (output.rename liftName)))))))
termination_by sites _ => sites.length

theorem sites_typing_rename (registry : Registry vertices α) (rename : α → β)
    (assignment : β → Comp model) (environment : List (Core.CommonSyntax.Binding model)) (sites : List (Site α)) (row : Row) :
    SitesTyping (registry.rename rename) assignment environment (sites.map fun site => site.rename rename) row ↔
      SitesTyping registry (assignment ∘ rename) environment sites row := by
  induction sites generalizing row with
  | nil => simp only [List.map_nil, sites_nil_iff]
  | cons site rest ih =>
      simp only [List.map_cons, sites_cons_iff]
      apply exists_congr
      intro source
      apply exists_congr
      intro suffix
      change (Core.CommonSyntax.Typing model environment site.expression source ∧
        Boundary (registry.rename rename) assignment source.1 ((site.target.rename rename).eval assignment) ∧
        SitesTyping (registry.rename rename) assignment environment (rest.map fun site => site.rename rename) suffix ∧
        Common.rowLe (Common.rowJoin source.2 suffix) row) ↔ _
      have boundarySame := boundary_rename registry rename assignment
        source.1 (site.target.eval (assignment ∘ rename))
      exact and_congr Iff.rfl (and_congr (by simpa only [Term.eval_rename] using boundarySame)
        (and_congr (ih suffix) Iff.rfl))

/-- Every original site expression is generated, even fixed fields; every
boundary uses the same captured assignment. All source rows are retained. -/
theorem generate_sites_exact (registry : Registry vertices α) (symbolic : SchemeEnv α)
    (environment : List (Core.CommonSyntax.Binding model)) (assignment : α → Comp model) (sites : List (Site α))
    (output : RowTerm α) (sourceEnvironment : List (Binding model))
    (actualRelated : Core.CommonSyntax.EnvRel model environment sourceEnvironment)
    (related : EnvRel model assignment symbolic sourceEnvironment) :
    (generateSites registry symbolic sites output).Models assignment ↔
      SitesTyping registry assignment environment sites (output.eval model assignment) := by
  cases sites with
  | nil =>
      rw [generateSites]
      change Common.rowLe Common.rowEmpty (output.eval model assignment) ↔ _
      exact (sites_nil_iff registry assignment environment _).symm
  | cons site rest =>
    have tailExact (source suffix : Comp model) :
        (generateSites (registry.rename liftName) (Core.PresenceGeneration.env₂ symbolic)
          (rest.map fun site => site.rename liftName) Core.PresenceGeneration.fresh₁.row).Models
            (extend (extend assignment source) suffix) ↔
        SitesTyping registry assignment environment rest suffix.2 := by
      have exactTail := generate_sites_exact
        (registry.rename liftName) (Core.PresenceGeneration.env₂ symbolic) environment
        (extend (extend assignment source) suffix) (rest.map fun site => site.rename liftName)
        Core.PresenceGeneration.fresh₁.row sourceEnvironment actualRelated
        ((related.lift source).lift suffix)
      exact exactTail.trans (by
        simpa only [Core.PresenceGeneration.fresh₁, CompTerm.var, RowTerm.eval,
          Core.PresenceGeneration.extend_none, liftName, Function.comp_def,
          Core.PresenceGeneration.extend_some] using
          sites_typing_rename registry liftName (extend (extend assignment source) suffix)
            environment rest suffix.2)
    have sourceExact (source suffix : Comp model) :
        (Core.CommonSyntax.generateNominalCore (Core.PresenceGeneration.env₂ symbolic)
          site.expression Core.PresenceGeneration.fresh₀).Holds model
            (extend (extend assignment source) suffix) ↔
        Core.CommonSyntax.Typing model environment site.expression source := by
      simpa only [Core.PresenceGeneration.env₂, Core.PresenceGeneration.fresh₀, CompTerm.eval_var,
        Core.PresenceGeneration.extend_some, Core.PresenceGeneration.extend_none] using
        Core.CommonSyntax.generate_nominal_core_exact (Core.PresenceGeneration.env₂ symbolic)
          environment sourceEnvironment (extend (extend assignment source) suffix) site.expression
          Core.PresenceGeneration.fresh₀ actualRelated ((related.lift source).lift suffix)
    have boundaryExact (source suffix : Comp model) :
        (generateBoundary (registry.rename liftName) (.ordinary Core.PresenceGeneration.fresh₀.ty)
          (site.target.rename liftName)).Models (extend (extend assignment source) suffix) ↔
        Boundary registry assignment source.1 (site.target.eval assignment) := by
      rw [generate_boundary_exact]
      change Boundary (registry.rename liftName) (extend (extend assignment source) suffix)
        source.1 ((site.target.rename liftName).eval (extend (extend assignment source) suffix)) ↔ _
      rw [Term.eval_rename]
      exact boundary_rename registry liftName
        (extend (extend assignment source) suffix) source.1 (site.target.eval assignment)
    have rowExact (source suffix : Comp model) :
        (Formula.ordinary (.rowLe (.join Core.PresenceGeneration.fresh₀.row Core.PresenceGeneration.fresh₁.row)
          (output.rename liftName))).Models (extend (extend assignment source) suffix) ↔
        Common.rowLe (Common.rowJoin source.2 suffix.2) (output.eval model assignment) := by
      change Common.rowLe (Common.rowJoin source.2 suffix.2)
        ((output.rename liftName).eval model (extend (extend assignment source) suffix)) ↔ _
      rw [RowTerm.eval_rename]
      rfl
    rw [generateSites]
    change (∃ source suffix, _ ∧ _ ∧ _ ∧ _) ↔ _
    constructor
    · rintro ⟨source, suffix, typed, boundary, tail, row⟩
      exact .cons ((sourceExact source suffix).mp typed)
        ((boundaryExact source suffix).mp boundary) ((tailExact source suffix).mp tail)
        ((rowExact source suffix).mp row)
    · intro typed
      obtain ⟨source, suffix, typed, boundary, tail, row⟩ :=
        (sites_cons_iff registry assignment environment site rest (output.eval model assignment)).mp typed
      exact ⟨source, (.bottom, suffix), (sourceExact _ _).mpr typed,
        (boundaryExact _ _).mpr boundary, (tailExact _ _).mpr tail, (rowExact _ _).mpr row⟩

termination_by sites.length

end Yulang.CommonNominalCoreSiteGeneration
