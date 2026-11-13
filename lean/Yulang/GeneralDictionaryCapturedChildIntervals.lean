import Yulang.GeneralDictionaryReachableRootIntervals

/-! Interval formation of actual variable-only emitted child inputs, including
merged repeated captures. The source cross matrix and merge equations prove
lower ≤ upper; no interval centre or semantic-order premise is supplied. -/
namespace Yulang.GeneralDictionaryCapturedChildIntervals
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalAllocation GeneralNominalCaptureMerges CommonNominalFullCarrier
variable {roles : Roles.RoleDecls}

theorem occurrences_member (bindings : Bindings) (name : Nat) (pair : GeneralSourceState.Interval)
    (member : pair ∈ occurrences bindings name) : (name,pair) ∈ bindings := by
  obtain ⟨entry,kept,equal⟩ := List.mem_map.mp member
  obtain ⟨present,same⟩ := List.mem_filter.mp kept
  have key : entry.1 = name := by simpa using same
  cases entry
  simp only at equal key
  subst_vars
  exact present

theorem capture_order (state : GeneralNominalState.State) (registry : Registry)
    (invocation : Nat) (declaration : Declaration) (bindings : Bindings)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (propagate state registry invocation declaration bindings) model)
    (name : Nat) (declared : name ∈ declaration.inputNames) :
    Subtype (model ((capture state registry invocation declaration.id bindings).inputs name).1).1
      (model ((capture state registry invocation declaration.id bindings).inputs name).2).1 := by
  have all := (propagate_models ..).mp valid
  have cross : ∀ first ∈ occurrences bindings name, ∀ last ∈ occurrences bindings name,
      Subtype (model first.1).1 (model last.2).1 := by
    intro first one last two
    exact all.2.1 (name,first) (occurrences_member bindings name first one)
      (name,last) (occurrences_member bindings name last two) rfl
  cases observed : occurrences bindings name with
  | nil =>
    have generated : PresenceNormalForm.All CommonNominalFullCarrier.model model
        (equations ((capture state registry invocation declaration.id bindings).inputs name).1 (lower []) ++
          equations ((capture state registry invocation declaration.id bindings).inputs name).2 (upper [])) := by
      intro atom member
      apply all.2.2 atom
      exact List.mem_flatMap.mpr ⟨name,declared,by simpa [observed] using member⟩
    have split := (PresenceNormalForm.all_append ..).mp generated
    have lo := (equations_exact ..).mp split.1
    have hi := (equations_exact ..).mp split.2
    apply subtype_trans lo.1
    apply subtype_trans _ hi.2
    change Subtype .bottom .top
    intro depth
    apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
    intro rank env obs _
    exact CommonNominalFullDemand.probeAt_bottom rank obs
  | cons first rest =>
    cases rest with
    | nil => simpa [capture,observed] using cross first (by simp [observed]) first (by simp [observed])
    | cons second tail =>
      have generated : PresenceNormalForm.All CommonNominalFullCarrier.model model
          (equations ((capture state registry invocation declaration.id bindings).inputs name).1 (lower (first :: second :: tail)) ++
            equations ((capture state registry invocation declaration.id bindings).inputs name).2 (upper (first :: second :: tail))) := by
        intro atom member
        apply all.2.2 atom
        exact List.mem_flatMap.mpr ⟨name,declared,by simpa [observed] using member⟩
      have split := (PresenceNormalForm.all_append ..).mp generated
      have lo := (equations_exact ..).mp split.1
      have hi := (equations_exact ..).mp split.2
      apply subtype_trans lo.1
      apply subtype_trans _ hi.2
      apply (lower_exact model (first :: second :: tail) (by simp) _).mpr
      intro a ha
      apply (upper_exact model (first :: second :: tail) (by simp) _).mpr
      intro b hb
      exact cross a (by simpa [observed] using ha) b (by simpa [observed] using hb)

theorem packet_capture_order (packet : Packet roles) (model : GeneralNominalCommonBridge.Assignment)
    (valid : packet.Holds model) (name : Nat) (declared : name ∈ packet.declaration.inputNames) :
    Subtype (model ((capture packet.context.state packet.registry packet.site.occurrence.identity
      packet.declaration.id packet.bindings).inputs name).1).1
      (model ((capture packet.context.state packet.registry packet.site.occurrence.identity
      packet.declaration.id packet.bindings).inputs name).2).1 :=
  capture_order packet.context.state packet.registry packet.site.occurrence.identity packet.declaration
    packet.bindings model ((GeneralNominalState.extend_models ..).mp valid.1).1 name declared

theorem clause_input_order (packet : Packet roles) (clause : Clause) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity) (name : Nat)
    (patternEq : GeneralDeclarationPatterns.normalize
      (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) = .var name)
    (declared : name ∈ packet.declaration.inputNames)
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model) :
    let child := GeneralNominalFeedbackSites.clauseChild packet clause signature
    Subtype (model (child.demand.arguments index).1).1 (model (child.demand.arguments index).2).1 := by
  simpa only [GeneralNominalFeedbackSites.clauseChild,GeneralDictionaryEmissionPlans.occurrence,
    GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.inputInterval,GeneralNominalFeedbackSites.frame,GeneralNominalAllocation.frame,patternEq] using packet_capture_order packet model valid name declared

theorem variable_name {patterns : List GeneralDeclarationPatterns.Pattern}
    {pattern : GeneralDeclarationPatterns.Pattern} {name : Nat} (member : pattern ∈ patterns)
    (normalized : GeneralDeclarationPatterns.normalize pattern = .var name) :
    name ∈ GeneralDeclarationPatterns.variablesArgs (GeneralDeclarationPatterns.normalizeArgs patterns) := by
  induction patterns with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst first
      simp [GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.variablesArgs,
        normalized,GeneralDeclarationPatterns.Pattern.variables]
    · exact List.mem_append_right _ (ih later)

theorem clause_input_declared (packet : Packet roles) (clause : Clause)
    (member : clause ∈ packet.declaration.requirements) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity) (name : Nat)
    (patternEq : GeneralDeclarationPatterns.normalize
      (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) = .var name) :
    name ∈ packet.declaration.inputNames :=
  packet.checked.scope.1 clause member name (variable_name (List.getElem_mem _) patternEq)

/-- A structural fragment of the actual where clauses, not a semantic validity
condition: every emitted argument is a variable. Checked declaration scoping derives declaration membership.
The inspection capture list may be empty; its
existing default merge then has bottom/top bounds. Repeated captures and nonpoint intervals are allowed. -/
def VariableInputs (packet : Packet roles) : Prop :=
  ∀ clause ∈ packet.declaration.requirements, ∀ signature : clause.Signature roles,
    ∀ index : Fin (roles clause.role).arity, ∃ name,
      GeneralDeclarationPatterns.normalize
        (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) = .var name

theorem child_origin (packet : Packet roles) (child : Occurrence roles) (member : child ∈ packet.children) :
    ∃ clause ∈ packet.declaration.requirements, ∃ signature : clause.Signature roles,
      child = GeneralNominalFeedbackSites.clauseChild packet clause signature := by
  obtain ⟨emission,present,equal⟩ := List.mem_map.mp member
  have original := (GeneralCanonicalChildOrder.canonicalEmit_perm packet.site.occurrence.identity
    packet.declaration packet.checked ((GeneralNominalFeedbackSites.frame packet).capture packet.declaration.id)
    ((GeneralNominalFeedbackSites.frame packet).allocation packet.declaration.id)).mem_iff.mpr present
  obtain ⟨clause,_,same⟩ := List.mem_map.mp original
  refine ⟨clause.val,clause.property,packet.checked.signature.2.2.2 clause.val clause.property,?_⟩
  rw [←equal,←same]
  rfl

theorem child_intervals (packet : Packet roles) (shape : VariableInputs packet)
    (child : Occurrence roles) (member : child ∈ packet.children)
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model)
    (index : Fin (roles child.demand.role).arity) :
    Subtype (model (child.demand.arguments index).1).1 (model (child.demand.arguments index).2).1 := by
  obtain ⟨clause,present,signature,rfl⟩ := child_origin packet child member
  obtain ⟨name,patternEq⟩ := shape clause present signature index
  exact clause_input_order packet clause signature index name patternEq
    (clause_input_declared packet clause present signature index name patternEq) model valid

end Yulang.GeneralDictionaryCapturedChildIntervals
