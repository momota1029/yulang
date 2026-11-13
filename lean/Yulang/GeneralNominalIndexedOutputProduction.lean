import Yulang.GeneralNominalOpenChildProduction

/-! Materialized outputs and output-only uses compose fixed-hole readbacks.
New target identities are interpreted by the same finite substitutions as
captured inputs and earlier settled binder outputs. -/
namespace Yulang.GeneralNominalIndexedOutputProduction
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalMaterialization
open GeneralNominalIndexedHoleReadback GeneralNominalHoleElimination GeneralNominalReadbackFunctionality
open GeneralNominalSharedCaptures GeneralNominalCommonBridge

variable {model : Assignment}

theorem interpret_bind (term : Expr α) (substitution : α → Expr Nat) (origins : Nat → Origin) :
    interpret origins (term.bind substitution) = term.bind (fun name => interpret origins (substitution name)) := by
  induction term with
  | leaf => rfl
  | node test children ih =>
    change Expr.node test _ = Expr.node test _
    congr 1
    exact funext ih

theorem compose (term : Expr Origin) (substitution : Origin → Expr Nat)
    (readback : ∀ model, models model → Holds model term root)
    (leaves : ∀ leaf ∈ term.leaves, Readback models origins remaining leaf (substitution leaf)) :
    Readback models origins remaining root (term.bind substitution) := by
  constructor
  · intro model valid
    rw [interpret_bind]
    exact GeneralNominalHoleReadback.holds_bind (readback model valid) _
      (fun leaf member => (leaves leaf member).1 model valid)
  · intro hole member
    obtain ⟨leaf,present,member⟩ := (leaves_bind term substitution hole).mp member
    exact (leaves leaf present).2 hole member

theorem recipe_canonical (recipe : Recipe body root term)
    (tests : ∀ entry ∈ body.tests, TestCanonical entry.2) : Canonical term := by
  induction recipe with
  | capture => trivial
  | node root test children member recipes ih => exact ⟨tests _ member,ih⟩

theorem recipe_indexed (recipe : Recipe body root term) (substitution : Nat → Expr Nat)
    (heads : ∀ model, models model → ∀ test ∈ body.tests, Head model test.1 test.2)
    (uses : ∀ entry ∈ body.variables, entry.mode = .actual →
      Readback models origins remaining entry.origin (substitution entry.name)) :
    Readback models origins remaining root (term.bind substitution) := by
  constructor
  · intro model valid
    rw [interpret_bind]
    exact recipe_readback recipe ⟨heads model valid,fun entry member actual => (uses entry member actual).1 model valid⟩
  · intro hole member
    obtain ⟨name,present,member⟩ := (leaves_bind term substitution hole).mp member
    obtain ⟨whereUsed,used⟩ := recipe_leaf_use recipe present
    exact (uses _ used rfl).2 hole member

/-- Each actual-mode input use follows a real capture origin; every output
binder follows its reserved output identity's prior readback. No endpoint
selection is involved, and no binder introduces another source hole. -/
theorem materialized_uses
    (valid : ∀ model, models model → GeneralNominalMaterialization.Models state declaration capture report body model)
    (substitution : Nat → Expr Nat)
    (inputs : ∀ entry ∈ body.variables, entry.mode = .actual → entry.name ∉ declaration.outputNames →
      ∃ captured ∈ report.captures, captured.name = entry.name ∧ ∃ root,
        captured.origin = some root ∧ Readback models origins remaining root (substitution entry.name))
    (binders : ∀ entry ∈ body.variables, entry.mode = .actual → entry.name ∈ declaration.outputNames →
      Readback models origins remaining (.source (capture.outputs entry.name)) (substitution entry.name)) :
    ∀ entry ∈ body.variables, entry.mode = .actual →
      Readback models origins remaining entry.origin (substitution entry.name) := by
  intro entry present actual
  by_cases output : entry.name ∈ declaration.outputNames
  · apply alias (binders entry present actual output)
    intro model represented
    exact same_symm (output_binder_use (valid model represented) present output)
  · obtain ⟨captured,member,same,root,recorded,readback⟩ := inputs entry present actual output
    apply alias readback
    intro model represented
    have read := readback.1 model represented
    have located : ∃ value, Observes model root value := by
      cases expression : interpret origins (substitution entry.name) with
      | leaf => rw [expression] at read; exact read.1
      | node => rw [expression] at read; exact read.1.1
    exact same_symm (retained_use (valid model represented) present actual captured member same.symm recorded located)

theorem materialized_output (recipe : Recipe body (.source target) term)
    (valid : ∀ model, models model → GeneralNominalMaterialization.Models state declaration capture report body model)
    (substitution : Nat → Expr Nat)
    (inputs : ∀ entry ∈ body.variables, entry.mode = .actual → entry.name ∉ declaration.outputNames →
      ∃ captured ∈ report.captures, captured.name = entry.name ∧ ∃ root,
        captured.origin = some root ∧ Readback models origins remaining root (substitution entry.name))
    (binders : ∀ entry ∈ body.variables, entry.mode = .actual → entry.name ∈ declaration.outputNames →
      Readback models origins remaining (.source (capture.outputs entry.name)) (substitution entry.name)) :
    Readback models origins remaining (.source target) (term.bind substitution) :=
  recipe_indexed recipe substitution (fun model present => (valid model present).1)
    (materialized_uses valid substitution inputs binders)

/-- Existing trusted settlement, including its prior-binder ordering, now
produces indexed output terms once its actual input origins are represented. -/
theorem promoted_output (trusted : GeneralNominalSharedSupport.Trusted state facts readbacks)
    (present : GeneralNominalSupport.Fact.outputs packet support ∈ facts)
    (output : GeneralSourceState.Output) (member : output ∈ packet.site.occurrence.demand.outputs)
    (substitution : Origin → Expr Nat)
    (represented : ∀ root ∈ GeneralNominalSharedSupport.inputOrigins facts,
      Readback (GeneralNominalSharedSupport.Models state facts) origins remaining root (substitution root)) :
    ∃ term, Readback (GeneralNominalSharedSupport.Models state facts) origins remaining (.source output.target) term := by
  obtain ⟨term,valid,leaves⟩ := GeneralNominalSharedSupport.promoted_output_readback trusted present output member
  exact ⟨term.bind substitution,compose term substitution valid (fun root member => represented root (leaves root member))⟩

end Yulang.GeneralNominalIndexedOutputProduction
