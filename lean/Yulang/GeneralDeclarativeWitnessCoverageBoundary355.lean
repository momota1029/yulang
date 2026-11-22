import Yulang.GeneralDeclarativeWitnessWhereFresh355
import Yulang.GeneralDeclarativeWitnessTypedLegacyCut354
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCoverageBoundary355
open GeneralDeclarativeWitnessCovariantCompiler353 (Prepared declarations)
open GeneralDeclarativeWitnessTypedRangeWriter354 (Run)
open GeneralDeclarativeWitnessSpineNode355 (Node)
open GeneralDeclarativeWitnessNominalSpine355 (Checked)
open GeneralDeclarativeWitnessTypedLegacyCut354 (source_not_invariant)
open GeneralNominalCenteredHeadWFSource (Coverage PatternsCovered PatternCovered ConstructorUse constructor_interpreted)
open GeneralDeclarativeNormalizeCovered322 (normalize_args_covered)
open GeneralDeclarationPatterns (normalizeArgs)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeHead320 (State)

theorem visible_selected_decl {p w} (a : Prepared p w) :
    a.decl ∈ a.ctx.registry.declarations := by
  have h : a.decl ∈ declarations a.anchor := by rw [a.only]; exact List.mem_cons_self
  unfold declarations at h
  exact (List.mem_filter.mp h).1

/-- C334 speaks about the ordinary interpretation of the same source.
A successful typed witness cannot synthesize its Coverage premise by
merely quoting the same registry, because an actual selected unary
covariant application defeats that old carrier's coverage test. -/
theorem checked_nominal_excludes_legacy_coverage {p w} (a : Prepared p w) :
    ¬ Coverage a.ctx.registry a.ctx.interp := by
  intro covered
  have body := (covered.1 _ (visible_selected_decl a)).1
  have normal := normalize_args_covered body
  rw [a.written] at normal
  simp only [normalizeArgs,a.anchor.shape.extracted] at normal
  have constructor : ConstructorUse a.ctx.registry.constructors a.ctx.interp a.anchor.shape.box 1 :=
    normal.1.1.1
  have old := source_not_invariant a.anchor.metadataProof
  have primitiveMissing := (congrArg (fun n => (interpretation a.anchor.metadataProof.source.snapshot).primitives n)
    a.anchor.sameBox).trans old.2
  have invariantMissing := (congrArg (fun n => (interpretation a.anchor.metadataProof.source.snapshot).invariantNominal n)
    a.anchor.sameBox).trans old.1
  rcases constructor_interpreted constructor with ⟨primitive,x⟩|invariant
  · change (interpretation a.anchor.metadataProof.source.snapshot).primitives a.anchor.shape.box = some primitive at x
    rw [primitiveMissing] at x
    cases x
  · change (interpretation a.anchor.metadataProof.source.snapshot).invariantNominal a.anchor.shape.box = true at invariant
    rw [invariantMissing] at invariant
    cases invariant

theorem range_not_legacy_coverage {p w} (a : Run p w) :
    ¬ Coverage a.readFrom.ctx.registry a.readFrom.ctx.interp :=
  checked_nominal_excludes_legacy_coverage a.readFrom.center

theorem whole_spine_not_old_carrier {s : State} {p : Node s} (a : Checked p) :
    ∀ n ∈ a.nodes, ¬ Coverage n.proof.compiled.readFrom.ctx.registry n.proof.compiled.readFrom.ctx.interp :=
  fun n _ => range_not_legacy_coverage n.proof.compiled

end Yulang.GeneralDeclarativeWitnessCoverageBoundary355
