import Yulang.GeneralNominalRegistrySourceTemplates

/-! Trusted explanations can share one finite ledger. Its models remain the
coarse source-and-trusted-facts predicate throughout global replacement. -/
namespace Yulang.GeneralNominalCommonTrustedLedger
open GeneralNominalSharedSupport GeneralNominalSupport GeneralNominalSaturationState
open GeneralNominalSharedCaptures GeneralNominalOriginTerms GeneralNominalRecursiveInspection
open GeneralNominalLabelledOriginClosure GeneralNominalScopedRecipeLabels
open GeneralNominalSourceProducerHandoff GeneralNominalLabelledExposureElimination
open GeneralNominalHoleElimination

variable {roles : Roles.RoleDecls} {state : Tracked roles}
variable {first last : List (Fact roles)} {one two : Readbacks}

theorem models_subset (included : first ⊆ last) (valid : Models state last model) : Models state first model :=
  ⟨valid.1,fun fact member => valid.2 fact (included member)⟩

theorem captured_restrict (captured : Captured packet before name origin)
    (included : ∀ model, after model → before model) : Captured packet after name origin := by
  refine ⟨captured.1,?_⟩
  intro capture member same
  obtain ⟨other,found,agree⟩ := captured.2 capture member same
  exact ⟨other,found,fun model valid => agree model (included model valid)⟩

def certificate_weaken (certificate : OutputCertificate state first one packet)
    (facts : first ⊆ last) (readbacks : one ⊆ two) : OutputCertificate state last two packet where
  substitution := certificate.substitution
  recipes := certificate.recipes
  inputs := by
    intro entry member actual input
    obtain ⟨origin,equal,captured⟩ := certificate.inputs entry member actual input
    exact ⟨origin,equal,captured_restrict captured (fun model valid => ⟨models_subset facts valid.1,valid.2⟩)⟩
  binders := fun entry member actual output => readbacks (certificate.binders entry member actual output)
  uses := fun model valid delta => certificate.uses model (models_subset facts valid) delta

theorem explanation_weaken (explanation : InputExplanation state first packet)
    (facts : first ⊆ last) : InputExplanation state last packet := by
  intro entry member actual
  obtain ⟨origin,captured,same⟩ := explanation entry member actual
  exact ⟨origin,captured_restrict captured (fun model valid => ⟨models_subset facts valid.1,valid.2⟩),
    fun model valid input => same model (models_subset facts valid) input⟩

theorem same_inputs_restrict (same : GeneralNominalDemandMerging.SameInputs before left right)
    (included : ∀ model, after model → before model) :
    GeneralNominalDemandMerging.SameInputs after left right := by
  refine ⟨same.1,?_⟩
  have lift {xs ys} (related : GeneralNominalDemandMerging.All₂ (GeneralNominalDemandMerging.Related before) xs ys) :
      GeneralNominalDemandMerging.All₂ (GeneralNominalDemandMerging.Related after) xs ys := by
    induction related with
    | nil => exact .nil
    | cons known rest ih =>
      obtain ⟨a,b,one,two,equal⟩ := known
      exact .cons ⟨a,b,one,two,fun model valid => equal model (included model valid)⟩ ih
  exact lift same.2

theorem merge_weaken (evidence : GeneralNominalSettledSupport.MergeEvidence before left right)
    (included : ∀ model, after model → before model) :
    GeneralNominalSettledSupport.MergeEvidence after left right := by
  refine ⟨fun model valid => evidence.1 model (included model valid),
    fun model valid => evidence.2.1 model (included model valid),?_⟩
  rcases evidence.2.2 with same | ⟨snapshot,same,leftRecovery,rightRecovery⟩
  · exact Or.inl (same_inputs_restrict same included)
  · exact Or.inr ⟨snapshot,same_inputs_restrict same included,
      fun index missing model valid => leftRecovery index missing model (included model valid),
      fun index missing model valid => rightRecovery index missing model (included model valid)⟩

theorem trusted_append (left : Trusted state first one) (right : Trusted state last two) :
    Trusted state (first ++ last) (one ++ two) := by
  induction left with
  | source => exact right
  | input packet support previous member readback explanation ih =>
    apply Trusted.input packet support ih member
    · intro slot seen test observation head model valid
      exact readback slot seen test observation head model (models_subset (List.subset_append_left ..) valid)
    · exact explanation_weaken explanation (List.subset_append_left ..)
  | output packet support certificate target term previous member input settled recipe ih =>
    exact Trusted.output packet support
      (certificate_weaken certificate (List.subset_append_left ..) (List.subset_append_left ..))
      target term ih member (List.mem_append_left _ input) settled recipe
  | merge first last support previous member evidence ih =>
    exact Trusted.merge first last support ih member
      (merge_weaken evidence (fun _ valid => models_subset (List.subset_append_left ..) valid))

def Supported (state : Tracked roles) (fact : Fact roles) : Prop :=
  ∃ facts readbacks, Trusted state facts readbacks ∧ fact ∈ facts

theorem finite_common_ledger (items : List (Fact roles)) :
    ∃ facts readbacks, Trusted state facts readbacks ∧
      ∀ fact ∈ items, Supported state fact → fact ∈ facts := by
  classical
  induction items with
  | nil => exact ⟨[],[],.source,by simp⟩
  | cons head tail ih =>
    obtain ⟨facts,readbacks,trusted,covered⟩ := ih
    by_cases supported : Supported state head
    · obtain ⟨more,trees,known,member⟩ := supported
      refine ⟨more ++ facts,trees ++ readbacks,trusted_append known trusted,?_⟩
      intro fact present supported
      rcases List.mem_cons.mp present with rfl | present
      · exact List.mem_append_left _ member
      · exact List.mem_append_right _ (covered fact present supported)
    · refine ⟨facts,readbacks,trusted,?_⟩
      intro fact present known
      rcases List.mem_cons.mp present with rfl | present
      · exact False.elim (supported known)
      · exact covered fact present known

theorem common_ledger (state : Tracked roles) :
    ∃ facts readbacks, Trusted state facts readbacks ∧
      ∀ other trees, Trusted state other trees → other ⊆ facts := by
  obtain ⟨facts,readbacks,trusted,covered⟩ := finite_common_ledger (state := state) state.facts
  refine ⟨facts,readbacks,trusted,?_⟩
  intro other trees known fact member
  exact covered fact (GeneralNominalSettledSupport.trusted_members (trusted_old known) fact member)
    ⟨other,trees,known,member⟩

theorem common_models (state : Tracked roles) :
    ∃ facts readbacks, Trusted state facts readbacks ∧
      ∀ other trees, Trusted state other trees →
        ∀ model, Models state facts model → Models state other model := by
  obtain ⟨facts,readbacks,trusted,contains⟩ := common_ledger state
  exact ⟨facts,readbacks,trusted,fun other trees known _ valid => models_subset (contains other trees known) valid⟩

theorem inputs_append
    (left : TrustedInputs state first context origins remaining keys tests)
    (right : TrustedInputs state last context origins remaining keys tests) :
    TrustedInputs state (first ++ last) context origins remaining keys tests := by
  intro root member
  have members : inputOrigins (first ++ last) = inputOrigins first ++ inputOrigins last := by
    simp only [inputOrigins,List.flatMap_append]
  rw [members] at member
  rcases List.mem_append.mp member with member | member
  · obtain ⟨value,vocabulary⟩ := left root member
    exact ⟨value.restrict (fun _ valid => models_subset (List.subset_append_left ..) valid),vocabulary⟩
  · obtain ⟨value,vocabulary⟩ := right root member
    exact ⟨value.restrict (fun _ valid => models_subset (List.subset_append_right ..) valid),vocabulary⟩

theorem inputs_replace (inputs : TrustedInputs state first context origins remaining keys tests)
    (replacement : Value (Models state first) context origins (remaining.erase hole) keys (origins hole))
    (known : Vocabulary tests replacement.term) :
    TrustedInputs state first context origins (remaining.erase hole) keys tests := by
  intro root member
  obtain ⟨value,vocabulary⟩ := inputs root member
  refine ⟨GeneralNominalLabelledExposureElimination.Value.replace value replacement,?_⟩
  apply vocabulary_bind vocabulary
  intro name present
  by_cases equal : name = hole
  · simpa only [substitute,equal,ite_true] using known
  · simp only [substitute,equal,ite_false,Vocabulary]

end Yulang.GeneralNominalCommonTrustedLedger
