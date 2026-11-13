import Yulang.GeneralDictionarySharedConstantRefresh
import Yulang.GeneralDictionarySharedTrustTransport
/-! Certified readiness of the pre-existing output identity 1 after actual
constant-output installation and refresh. This is not fresh allocation and
constructs no generated consumer. -/
namespace Yulang.GeneralDictionarySharedConstantReady
open GeneralNominalSaturationState GeneralNominalSupport GeneralNominalSharedSupport
open GeneralNominalOriginTerms GeneralDictionarySharedConstantRefresh
open GeneralDictionaryRecursiveObstruction
open GeneralDictionaryCommittedEvidenceExamples (packet packet_children)

abbrev input : Fact GeneralDeclarationExamples.roles := .inputs packet []
abbrev output : Fact GeneralDeclarationExamples.roles := .outputs packet []

theorem facts : installed.facts = [input,output] := by
  change GeneralNominalSupportChoices.installedFacts start packet ++ [] = _
  rw [GeneralNominalSupportChoices.empty_alternatives start packet rfl old_guard]
  rfl

theorem input_trusted : Trusted installed [input] [] := by
  apply Trusted.input packet [] Trusted.source
  · rw [facts]; exact List.mem_cons_self
  · intro slot read test observation head model valid
    exact GeneralCanonicalObservations.recorded_sound packet.context.state model valid.1 (head_recorded head)
  · apply empty_input_explanation
    rw [GeneralNominalSharedPositive.leaf_input_schema packet rfl]

theorem schema : GeneralNominalPacketSupport.namedSchema packet =
    { tests := [(.source 1,.scalar .int)] } := schema_calculated

noncomputable def term : Expr Nat := .node (.scalar .int) (fun index => Fin.elim0 index)
theorem recipe : Recipe (GeneralNominalPacketSupport.namedSchema packet) (.source 1) term := by
  apply Recipe.node
  · rw [schema]; exact List.mem_cons_self
  · intro index; exact Fin.elim0 index

theorem recipes : Recipes packet := by
  intro requested member
  have same : requested = ⟨1,1⟩ := List.mem_singleton.mp member
  subst requested
  exact ⟨term,recipe⟩

noncomputable def certificate : OutputCertificate installed [input] [] packet :=
  Classical.choice (GeneralNominalSharedPositive.constant_certificate installed [input] [] packet
    (by rw [schema]) recipes)

theorem output_trusted : Trusted installed [output,input] [(1,term.bind certificate.substitution)] := by
  apply Trusted.output packet [] certificate 1 term input_trusted
  · rw [facts]; exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_self
  · refine ⟨List.mem_cons_self,?_⟩
    intro child member
    rw [packet_children] at member
    cases member
  · exact recipe

theorem refreshed_trusted : Trusted refreshed [output,input] [(1,term.bind certificate.substitution)] :=
  GeneralDictionarySharedTrustTransport.trusted_at refresh_step.choose_spec.2 output_trusted

theorem ready : GeneralNominalSharedSupport.ReadyAt refreshed 1 := by
  let observation := GeneralCanonicalObservations.Observation.normalized
    refreshed.current.context.state.base (1 : Fin 2) (.base .int)
  have head : Head refreshed.current.context.state 1 (.scalar .int) observation :=
    Head.scalar (snapshot := refreshed.current.context.state) (1 : Fin 2) .int rfl
  refine ⟨.scalar .int,observation,head,[output,input],[(1,term.bind certificate.substitution)],
    refreshed_trusted,refreshed.current.context.state,observation,head,?_⟩
  intro model valid
  have outputs := valid.2 output List.mem_cons_self
  change GeneralNominalPacketSupport.Outputs packet model at outputs
  unfold GeneralNominalPacketSupport.Outputs at outputs
  rw [schema] at outputs
  have tested := (outputs.1 (.source 1,.scalar .int) List.mem_cons_self).2 _ (.source 1)
  exact tested
theorem ledger_inhabited : GeneralNominalSharedSupport.Models refreshed [output,input]
    GeneralNominalExamples.model := by
  have branch := inhabited.2.1 packet (by exact List.mem_cons_self)
  have facts := (GeneralNominalPacketSupport.packet_exact packet _).mp branch
  refine ⟨facts.1,?_⟩
  intro fact member
  rcases List.mem_cons.mp member with rfl | member
  · exact facts.2.2
  · cases List.mem_singleton.mp member
    exact facts.2.1

end Yulang.GeneralDictionarySharedConstantReady
