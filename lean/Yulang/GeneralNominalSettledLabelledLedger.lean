import Yulang.GeneralNominalScopedRecipeLabels

/-! The actual trusted ledger orders output-only binders before their uses.
Uniform source input expressions and finite source constructor templates
therefore produce labelled outputs without a settlement-depth premise. -/
namespace Yulang.GeneralNominalSettledLabelledLedger
open GeneralNominalSaturationState GeneralNominalSupport GeneralNominalSharedSupport
open GeneralNominalOriginTerms GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalReadbackFunctionality GeneralNominalIndexedHoleReadback GeneralNominalHoleElimination
open GeneralNominalScopedRecipeLabels GeneralNominalLabelledOriginClosure GeneralNominalSourceLabelVocabulary

variable {roles : Roles.RoleDecls} {tests : List Test} {keys remaining : List Nat}
variable {origins : Nat → Origin}

theorem canonical_bind (term : Expr α) (canonical : Canonical term) (substitution : α → Expr β)
    (images : ∀ name ∈ term.leaves, Canonical (substitution name)) : Canonical (term.bind substitution) := by
  induction term with
  | leaf name => exact images name (List.mem_singleton_self _)
  | node test children ih =>
    exact ⟨canonical.1,fun i => ih i (canonical.2 i) (fun name member => images name
      (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,member⟩))⟩

def Schemas (facts : List (Fact roles)) (tests : List Test) : Prop :=
  ∀ packet support, Fact.outputs packet support ∈ facts →
    ∀ entry ∈ (GeneralNominalPacketSupport.namedSchema packet).tests,
      TestCanonical entry.2 ∧ entry.2 ∈ tests

theorem schemas_tail (known : Schemas (fact :: facts) tests) : Schemas facts tests :=
  fun packet support member => known packet support (List.mem_cons_of_mem _ member)

theorem certificate_tree (certificate : OutputCertificate state facts readbacks packet)
    (recipe : Recipe (GeneralNominalPacketSupport.namedSchema packet) root term)
    (schema : ∀ entry ∈ (GeneralNominalPacketSupport.namedSchema packet).tests,
      TestCanonical entry.2 ∧ entry.2 ∈ tests)
    (prior : ∀ target expression, (target,expression) ∈ readbacks →
      Canonical expression ∧ Vocabulary tests expression) :
    Canonical (term.bind certificate.substitution) ∧ Vocabulary tests (term.bind certificate.substitution) := by
  have images : ∀ name ∈ term.leaves, Canonical (certificate.substitution name) ∧ Vocabulary tests (certificate.substitution name) := by
    intro name member
    obtain ⟨whereUsed,used⟩ := recipe_leaf_use recipe member
    by_cases output : name ∈ packet.declaration.outputNames
    · exact prior _ _ (certificate.binders _ used rfl output)
    · obtain ⟨recorded,equal,_⟩ := certificate.inputs _ used rfl output
      rw [equal]
      exact ⟨True.intro,True.intro⟩
  exact ⟨canonical_bind term (GeneralNominalIndexedOutputProduction.recipe_canonical recipe (fun entry member => (schema entry member).1))
      certificate.substitution (fun name member => (images name member).1),
    vocabulary_bind (recipe_vocabulary recipe (fun entry member => (schema entry member).2))
      (fun name member => (images name member).2)⟩

theorem trusted_trees (trusted : Trusted state facts readbacks) (known : Schemas facts tests) :
    ∀ target expression, (target,expression) ∈ readbacks → Canonical expression ∧ Vocabulary tests expression := by
  revert known
  induction trusted with
  | source => intro known target expression member; cases member
  | input packet support previous member readback explanation ih =>
    intro known target expression member
    exact ih (schemas_tail known) target expression member
  | merge first last support previous member evidence ih =>
    intro known target expression member
    exact ih (schemas_tail known) target expression member
  | output packet support certificate target term previous member included done recipe ih =>
    intro known result expression present
    rcases List.mem_cons.mp present with equal | present
    · cases equal
      exact certificate_tree certificate recipe (known packet support (List.mem_cons_self ..)) (ih (schemas_tail known))
    · exact ih (schemas_tail known) result expression present

theorem certificate_origins (certificate : OutputCertificate state facts readbacks packet)
    (recipe : Recipe (GeneralNominalPacketSupport.namedSchema packet) root term)
    (prior : ∀ target expression, (target,expression) ∈ readbacks →
      ∀ actual ∈ expression.leaves, actual ∈ inputOrigins facts) :
    ∀ actual ∈ (term.bind certificate.substitution).leaves,
      actual ∈ inputOrigins (Fact.outputs packet support :: facts) := by
  intro actual member
  obtain ⟨name,present,member⟩ := (leaves_bind term certificate.substitution actual).mp member
  obtain ⟨whereUsed,used⟩ := recipe_leaf_use recipe present
  by_cases output : name ∈ packet.declaration.outputNames
  · exact List.mem_append_right _ (prior _ _ (certificate.binders _ used rfl output) actual member)
  · obtain ⟨recorded,equal,captured⟩ := certificate.inputs _ used rfl output
    rw [equal] at member
    cases List.mem_singleton.mp member
    obtain ⟨capture,present,_,recorded⟩ := captured.1
    exact List.mem_append_left _ (List.mem_filterMap.mpr ⟨capture,present,recorded⟩)

theorem promoted_tree (trusted : Trusted state facts readbacks) (known : Schemas facts tests)
    (present : Fact.outputs packet support ∈ facts)
    (output : GeneralSourceState.Output) (member : output ∈ packet.site.occurrence.demand.outputs) :
    ∃ expression : Expr Origin, Canonical expression ∧ Vocabulary tests expression ∧
      (∀ model, GeneralNominalSharedSupport.Models state facts model → Holds model expression (.source output.target)) ∧
      ∀ actual ∈ expression.leaves, actual ∈ inputOrigins facts := by
  revert known
  induction trusted with
  | source => intro known; cases present
  | input added dependencies previous recorded readback explanation ih =>
    intro known
    rcases List.mem_cons.mp present with impossible | present
    · cases impossible
    · obtain ⟨expression,canonical,vocabulary,meaning,leaves⟩ := ih present (schemas_tail known)
      exact ⟨expression,canonical,vocabulary,fun model valid => meaning model
        ⟨valid.1,fun entry mem => valid.2 entry (List.mem_cons_of_mem _ mem)⟩,
        fun actual mem => List.mem_append_right _ (leaves actual mem)⟩
  | merge first last dependencies previous recorded evidence ih =>
    intro known
    rcases List.mem_cons.mp present with impossible | present
    · cases impossible
    · obtain ⟨expression,canonical,vocabulary,meaning,leaves⟩ := ih present (schemas_tail known)
      exact ⟨expression,canonical,vocabulary,fun model valid => meaning model
        ⟨valid.1,fun entry mem => valid.2 entry (List.mem_cons_of_mem _ mem)⟩,
        fun actual mem => List.mem_append_right _ (leaves actual mem)⟩
  | output added dependencies certificate target expression previous recorded included done recipe ih =>
    intro known
    rcases List.mem_cons.mp present with equal | present
    · cases equal
      obtain ⟨term,recipe⟩ := certificate.recipes output member
      have shape := certificate_tree certificate recipe (known _ _ (List.mem_cons_self ..))
        (trusted_trees previous (schemas_tail known))
      refine ⟨term.bind certificate.substitution,shape.1,shape.2,?_,
        certificate_origins certificate recipe (settled_readback_leaves previous)⟩
      intro model valid
      have old : GeneralNominalSharedSupport.Models state _ model :=
        ⟨valid.1,fun entry mem => valid.2 entry (List.mem_cons_of_mem _ mem)⟩
      exact recipe_readback recipe (certificate_coherent certificate model old
        ⟨old.2 _ included,valid.2 _ (List.mem_cons_self ..)⟩)
    · obtain ⟨term,canonical,vocabulary,meaning,leaves⟩ := ih present (schemas_tail known)
      exact ⟨term,canonical,vocabulary,fun model valid => meaning model
        ⟨valid.1,fun entry mem => valid.2 entry (List.mem_cons_of_mem _ mem)⟩,
        fun actual mem => List.mem_append_right _ (leaves actual mem)⟩

/-- Uniform source-key labels for promoted outputs follow from the earlier
binder ledger and represented trusted input origins. No binder target is
introduced as a fresh hole and no packet-height estimate is assumed. -/
theorem promoted_labelled (trusted : Trusted state facts readbacks) (known : Schemas facts tests)
    (templates : NodeTemplates context keys tests)
    (inputs : ∀ root ∈ inputOrigins facts,
      ∃ value : Value (GeneralNominalSharedSupport.Models state facts) context origins remaining keys root,
        Vocabulary tests value.term)
    (present : Fact.outputs packet support ∈ facts)
    (output : GeneralSourceState.Output) (member : output ∈ packet.site.occurrence.demand.outputs) :
    ∃ value : Value (GeneralNominalSharedSupport.Models state facts) context origins remaining keys (.source output.target),
      Vocabulary tests value.term := by
  classical
  obtain ⟨expression,canonical,vocabulary,meaning,leaves⟩ := promoted_tree trusted known present output member
  let choose : Origin → Expr Nat := fun root => if mem : root ∈ inputOrigins facts then
    (Classical.choose (inputs root mem)).term else .leaf 0
  have represented : ∀ root ∈ inputOrigins facts,
      Readback (GeneralNominalSharedSupport.Models state facts) origins remaining root (choose root) := by
    intro root mem
    simpa only [choose,dite_eq_left mem] using (Classical.choose (inputs root mem)).labelled.2
  have canonicalImages : ∀ root ∈ inputOrigins facts, Canonical (choose root) := by
    intro root mem
    simpa only [choose,dite_eq_left mem] using (Classical.choose (inputs root mem)).labelled.1.2.2
  have vocabularyImages : ∀ root ∈ inputOrigins facts, Vocabulary tests (choose root) := by
    intro root mem
    simpa only [choose,dite_eq_left mem] using Classical.choose_spec (inputs root mem)
  have readback := GeneralNominalIndexedOutputProduction.compose expression choose meaning
    (fun root mem => represented root (leaves root mem))
  have shape := canonical_bind expression canonical choose (fun root mem => canonicalImages root (leaves root mem))
  have vocab := vocabulary_bind vocabulary (fun root mem => vocabularyImages root (leaves root mem))
  obtain ⟨pattern,label,scope⟩ := reify templates (expression.bind choose) vocab shape readback.2
  exact ⟨⟨pattern,expression.bind choose,⟨label,readback⟩,scope⟩,vocab⟩

end Yulang.GeneralNominalSettledLabelledLedger
