import Yulang.GeneralNominalFeedbackSteps
import Yulang.GeneralNominalProgressObstruction
import Yulang.GeneralNominalReadbackCounterexample

/-! A checked associated-output feedback obstruction on the general carrier.
The finite installation entails a nominal self-cycle in its journal, while
its old raw context still has a finite model and unresolved child endpoints.
This is a finite obstruction certificate, not an infinite old Step trace. -/
namespace Yulang.GeneralNominalFeedbackObstruction

open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts
open GeneralNominalSaturationState CommonNominalFullCarrier

abbrev clause : Clause := ⟨20,1,[.var 0],[⟨21,0,.var 0⟩]⟩
abbrev declaration : Declaration := ⟨2,1,[.app 0 [.var 0]],[clause],[⟨22,0,.app 0 [.var 0]⟩],[]⟩

theorem declaration_checked : DeclarationChecked constructors roles declaration := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro equation member
      have same := List.mem_singleton.mp member; subst equation
      exact ⟨none,rfl⟩
    · intro name body present
      by_cases zero : name = 0
      · subst name
        exact Or.inl ⟨⟨22,0,.app 0 [.var 0]⟩,by simp,rfl⟩
      · simp [roles,GeneralDeclarationExamples.outputRole,zero] at present
    · intro c member
      have same := List.mem_singleton.mp member; subst c
      refine ⟨rfl,?_⟩
      intro equation member
      have same := List.mem_singleton.mp member; subst equation
      exact ⟨none,rfl⟩
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro c member
    have same := List.mem_singleton.mp member; subst c; exact ⟨rfl,rfl⟩
  · intro c member
    have same := List.mem_singleton.mp member; subst c
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro c member
    have same := List.mem_singleton.mp member; subst c
    unfold ConservativeSmaller
    decide +kernel
  · intro c member
    have same := List.mem_singleton.mp member; subst c
    exact unary_descent 0 0

abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev source : GeneralNominalState.State := { GeneralNominalIntervalExamples.source with
  ordinary := GeneralNominalAllocation.equations 2 (.var 3) }
abbrev context : Context := ⟨source,GeneralNominalExamples.interpretation⟩
abbrev root : Occurrence roles := ⟨100,⟨1,fun _ => (0,0),[⟨0,2⟩],by
  intro output member; have same := List.mem_singleton.mp member; subst output; exact ⟨none,rfl⟩⟩⟩
abbrev packet : Packet roles := ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(0,0)]⟩
abbrev initialState := initial context root
abbrev oldInstalled := GeneralNominalSaturationState.install initialState packet (pointEmitted packet)
noncomputable def installed := GeneralNominalFeedbackSites.install initialState packet (GeneralNominalFeedbackSites.emitted packet)
abbrev value := GeneralNominalProgressObstruction.value
abbrev model := GeneralNominalProgressObstruction.model
abbrev output := GeneralNominalAllocation.source source registry root.identity (GeneralNominalAllocation.origin root.identity 2 5 21 0)
abbrev child : Occurrence roles :=
  ⟨GeneralNominalAllocation.source source registry root.identity (GeneralNominalAllocation.origin root.identity 2 6 20 0),
    ⟨1,fun _ => (2,3),[⟨0,output⟩],by
      intro o member; have same := List.mem_singleton.mp member; subst o; exact ⟨none,rfl⟩⟩⟩

theorem checked : Checked registry :=
  ⟨by decide +kernel,by intro d member; have same := List.mem_singleton.mp member; subst d; exact declaration_checked⟩

private theorem query : GeneralNominalInspection.queries source context.interpretation declaration = [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]

theorem report_exact : report context declaration [(0,0)] = captured source 0 0 0 (2,3) :=
  GeneralNominalUnaryCaptureFacts.report_exact context declaration 0 GeneralNominalIntervalExamples.descriptor rfl 0 (2,3) rfl query

theorem children_exact : packet.children = [child] := by
  unfold Packet.children Packet.bindings
  rw [report_exact]
  unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  simp [GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralDictionaryEmissionPlans.occurrence,
    GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,GeneralDeclarationDemands.outputTarget,
    GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,
    normalize,child,Declaration.outputNames,bindings,captured,GeneralNominalAllocation.allocation,output]
  exact ⟨rfl,rfl,rfl⟩


theorem schema_exact : generated registry context root declaration declaration_checked [(0,0)] =
    ⟨[⟨0,.nominal (.source 2) 0 0,.actual⟩,⟨0,.source output,.actual⟩],[(.source 2,.nominal 0 1)],false⟩ := by
  unfold generated
  rw [report_exact]
  unfold GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  simp [GeneralNominalMaterialization.generated,GeneralNominalMaterialization.rootRequests,
    GeneralNominalMaterialization.emissionRequests,GeneralNominalMaterialization.inputRequests,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.Schema.append,
    GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.inputInterval,GeneralDeclarationDemands.outputTarget,Declaration.outputNames,
    GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,normalize,normalizeArgs,bindings,captured,
    output,GeneralNominalAllocation.allocation]

private theorem base_models (m : GeneralNominalCommonBridge.Assignment)
    (values : ∀ slot : Fin 4, slot.val < 2 → ∃ actual,
      Subtype (m 2).1 actual ∧ Subtype actual (m 3).1 ∧ Equivalent (m slot.val).1 (nominal 0 [.inl actual]))
    (equal : Equivalent (m 2).1 (m 3).1) : GeneralNominalState.Models source m := by
  apply (GeneralNominalState.extend_models ..).mpr
  refine ⟨⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩,
    (GeneralNominalCaptureMerges.equations_exact m 2 (.var 3)).mpr equal⟩
  · exact PresenceNormalForm.all_nil _ _
  · intro _ _ recorded; cases recorded
  · intro _ member; cases member
  · intro slot d recorded
    have small : slot.val < 2 := by
      by_cases h : slot.val < 2
      · exact h
      · simp [GeneralNominalIntervalExamples.source,h] at recorded
    have same : d = GeneralNominalIntervalExamples.descriptor := by
      simpa [GeneralNominalIntervalExamples.source,small] using recorded.symm
    subst d
    obtain ⟨actual,lo,hi,equal⟩ := values slot small
    exact ⟨[.inl actual],.cons ⟨lo,hi⟩ .nil,equal⟩

theorem source_models : GeneralNominalState.Models source model :=
  base_models model (fun _ _ => ⟨value,subtype_refl _,subtype_refl _,GeneralNominalProgressObstruction.equation⟩)
    ⟨subtype_refl _,subtype_refl _⟩

private theorem observed_nominal (identity : Nat) : Observes model (.nominal (.source identity) 0 0) value :=
  .nominal (.source identity) GeneralNominalProgressObstruction.equation rfl

private theorem nominal_value (identity : Nat) (actual : Ty)
    (seen : Observes model (.nominal (.source identity) 0 0) actual) : Equivalent actual value :=
  nominal_observation_unique model (.argument (.source identity) 0 0) actual value seen (observed_nominal identity)

private theorem schema_models : GeneralNominalMaterialization.Models source declaration
    (GeneralNominalAllocation.capture source registry root.identity declaration.id packet.bindings)
    (report context declaration [(0,0)]) (generated registry context root declaration declaration_checked [(0,0)]) model := by
  rw [schema_exact,report_exact]
  have bindings : packet.bindings = [(0,(2,3))] := by unfold Packet.bindings; rw [report_exact]; rfl
  rw [bindings]
  refine ⟨?_,?_,?_,?_⟩
  · intro test member
    have same := List.mem_singleton.mp member; subst test
    refine ⟨⟨value,.source 2⟩,?_⟩
    intro actual seen
    cases seen
    exact ⟨[.inl value],rfl,GeneralNominalProgressObstruction.equation⟩
  · intro use member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · refine ⟨⟨value,observed_nominal 2⟩,?_⟩
      intro actual seen
      have equal := nominal_value 2 actual seen
      exact ⟨equal.2,equal.1⟩
    · refine ⟨⟨value,.source output⟩,?_⟩
      intro actual seen
      cases seen
      exact ⟨subtype_refl _,subtype_refl _⟩
  · intro first one last two _ _ _ a b ha hb
    have unique : ∀ u ∈ [({ name := 0, origin := .nominal (.source 2) 0 0, mode := .actual } : GeneralNominalMaterialization.Use),
        ⟨0,.source output,.actual⟩], ∀ actual, Observes model u.origin actual → Equivalent actual value := by
      intro u member actual seen
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact nominal_value 2 actual seen
      · cases seen; exact ⟨subtype_refl _,subtype_refl _⟩
    exact ⟨subtype_trans (unique first one a ha).1 (unique last two b hb).2,
      subtype_trans (unique last two b hb).1 (unique first one a ha).2⟩
  · intro use member capture captured _ _ origin recorded a b ha hb
    have same := List.mem_singleton.mp captured; subst capture
    have same := Option.some.inj recorded; subst origin
    have right := nominal_value 0 b hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · have left := nominal_value 2 a ha
      exact ⟨subtype_trans left.1 right.2,subtype_trans right.1 left.2⟩
    · cases ha
      exact ⟨right.2,right.1⟩

theorem packet_models : packet.Holds model := by
  have raw := private_models context registry root declaration 0 GeneralNominalIntervalExamples.descriptor rfl 0 rfl (2,3) rfl
    query model source_models
  exact ⟨raw.1,raw.2,schema_models⟩

theorem old_installed_models : Models oldInstalled model :=
  (GeneralNominalSaturationState.install_models initialState packet (pointEmitted packet) rfl model).mpr
    ⟨(initial_models context root model).mpr source_models,packet_models⟩

theorem installed_models : Models installed model :=
  (GeneralNominalFeedbackSites.install_equivalent initialState packet _ rfl model).mpr old_installed_models

theorem journal_endpoints (m : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds m) :
    Equivalent (m 2).1 (m 3).1 := by
  have original := (GeneralNominalRecursiveCandidates.branch_interval_sound _ _ _ _ _ _ _ valid).1
  exact (GeneralNominalCaptureMerges.equations_exact m 2 (.var 3)).mp
    ((GeneralNominalState.extend_models GeneralNominalIntervalExamples.source [] _ m).mp original).2

theorem packet_self_argument (m : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds m) :
    ∃ actual, GeneralNominalProjections.Observes m (.argument (.source 2) 0 0) (.inl actual) ∧
      Equivalent actual (m 2).1 := by
  have material := valid.2.2
  change GeneralNominalMaterialization.Models source declaration _ _
    (generated registry context root declaration declaration_checked [(0,0)]) m at material
  rw [schema_exact] at material
  have present := material.2.1 ⟨0,.nominal (.source 2) 0 0,.actual⟩ (by simp)
  obtain ⟨actual,seen⟩ := present.1
  have bounded := present.2 actual seen
  have bindings : packet.bindings = [(0,(2,3))] := by unfold Packet.bindings; rw [report_exact]; rfl
  change GeneralNominalMaterialization.VariableHolds declaration
    (GeneralNominalAllocation.capture source registry root.identity declaration.id packet.bindings) m 0 .actual actual at bounded
  rw [bindings] at bounded
  change Subtype (m 2).1 actual ∧ Subtype actual (m 3).1 at bounded
  exact ⟨actual,recover_observation m _ actual seen,subtype_trans bounded.2 (journal_endpoints m valid).2,bounded.1⟩

theorem old_journal_self_argument : GeneralNominalFeedbackK2.Argument oldInstalled 2 2 :=
  ⟨0,0,fun m valid => packet_self_argument m (valid.2.1 packet (by simp [oldInstalled,GeneralNominalSaturationState.install]))⟩

theorem journal_self_argument : GeneralNominalFeedbackK2.Argument installed 2 2 :=
  ⟨0,0,fun m valid => packet_self_argument m (valid.2.1 packet (by simp [installed,GeneralNominalFeedbackSites.install]))⟩

theorem chain_blocked (after : State roles)
    (path : B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) installed after)
    (next : Packet roles) (focus : next.site.occurrence = child) :
    ¬ GeneralNominalFeedbackSteps.Installable registry after next := by
  have role : next.site.occurrence.demand.role = 1 := congrArg (fun o => o.demand.role) focus
  let index : Fin (roles next.site.occurrence.demand.role).arity := ⟨0,by rw [role]; decide +kernel⟩
  apply GeneralNominalFeedbackSteps.self_argument_blocks_trace 2 journal_self_argument path next index
  have bounds : ∀ i : Fin (roles next.site.occurrence.demand.role).arity,
      (next.site.occurrence.demand.arguments i).1 = 2 := by
    rw [focus]
    intro i
    rfl
  exact bounds index


abbrev finiteModel : GeneralNominalCommonBridge.Assignment := fun source =>
  (if source < 2 then nominal 0 [.inl (.base .int)] else .base .int,Common.rowEmpty)

theorem finite_source_models : GeneralNominalState.Models source finiteModel := by
  apply base_models
  · intro slot small
    refine ⟨.base .int,subtype_refl _,subtype_refl _,?_⟩
    simp only [small]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · exact ⟨subtype_refl _,subtype_refl _⟩

theorem finite_private_models : GeneralNominalState.Models packet.privateContext.state finiteModel :=
  (private_models context registry root declaration 0 GeneralNominalIntervalExamples.descriptor rfl 0 rfl (2,3) rfl
    query finiteModel finite_source_models).1

private theorem int_not_nominal (arguments : List Argument) : ¬ Subtype (.base .int) (nominal 0 arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead 0 arguments.length) (by exact ⟨rfl,by simp⟩)

theorem finite_not_packet : ¬ packet.Holds finiteModel := by
  intro valid
  have material := valid.2.2
  change GeneralNominalMaterialization.Models source declaration _ _
    (generated registry context root declaration declaration_checked [(0,0)]) finiteModel at material
  rw [schema_exact] at material
  obtain ⟨arguments,_,equal⟩ := (material.1 (.source 2,.nominal 0 1) (by simp)).2 _ (.source 2)
  exact int_not_nominal arguments equal.1

theorem old_context_incomplete : ¬ ContextComplete oldInstalled := by
  intro complete
  have valid := complete finiteModel finite_private_models
  exact finite_not_packet (valid.2.1 packet (by simp [oldInstalled,GeneralNominalSaturationState.install]))

private theorem no_cycles (s : GeneralNominalState.State) (models : GeneralNominalState.Models s finiteModel)
    (structural : ∀ first last, ¬ GeneralSourceK2.Child s.view first last)
    (nominalOnly : ∀ slot descriptor, s.nominals slot = some descriptor →
      s.base.source slot < 2 ∧ descriptor.declaration.name = 0)
    (slot : Fin s.base.slots) : ¬ GeneralNominalCycleK2.Cycle s slot := by
  have bounds : ∀ first last, GeneralNominalCycleK2.Edge s first last → s.base.source first < 2 ∧ ¬ s.base.source last < 2 := by
    intro first last edge
    rcases edge with old | ⟨descriptor,recorded,index,observed⟩
    · exact False.elim (structural first last old)
    · obtain ⟨small,name⟩ := nominalOnly first descriptor recorded
      refine ⟨small,?_⟩
      intro lastSmall
      obtain ⟨actual,seen,equal⟩ := observed finiteModel models
      cases seen with
      | argument parent compared found =>
        cases parent
        change Equivalent (finiteModel (s.base.source first)).1 (nominal descriptor.declaration.name _) at compared
        simp only [small] at compared
        rw [name] at compared
        have invariant := (nominal_regular_invariant_exact _ _ _ _).mp compared.1
        have size := invariant.2.1
        have zero : index = 0 := by
          obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp found
          simp only [List.length_cons,List.length_nil] at size
          omega
        subst index
        have argument := invariant.2.2 0 (.inl (.base .int)) (.inl actual) rfl found
        simp only [lastSmall] at equal
        exact int_not_nominal _ (subtype_trans argument.1 equal.1)
  rintro ⟨next,edge,path⟩
  have bound := bounds slot next edge
  cases path with
  | nil => exact bound.2 bound.1
  | cons edge _ => exact bound.2 (bounds _ _ edge).1

theorem source_acyclic (slot : Fin source.base.slots) : ¬ GeneralNominalCycleK2.Cycle source slot := by
  apply no_cycles source finite_source_models
  · rintro _ _ ⟨kind,_,_,_,_⟩; exact Fin.elim0 kind
  · intro slot descriptor recorded
    by_cases small : slot.val < 2
    · have same : descriptor = GeneralNominalIntervalExamples.descriptor := by
        simpa [source,GeneralNominalIntervalExamples.source,small] using recorded.symm
      subst descriptor
      exact ⟨small,rfl⟩
    · simp [source,GeneralNominalIntervalExamples.source,small] at recorded

private theorem ready : ¬ GeneralNominalState.RootPending source root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨0,rfl,Or.inr ⟨GeneralNominalIntervalExamples.descriptor,rfl⟩⟩

theorem prepared : Prepared registry context root declaration declaration_checked := by
  refine ⟨GeneralNominalReadbackCounterexample.prepared.1,?_,initial_fresh source registry root.identity (by decide +kernel),
    [(0,0)],by decide +kernel,?_,?_,model,packet_models⟩
  · constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member
      have same := List.mem_singleton.mp member; subst output
      simp [GeneralNominalState.sources,List.ofFn_succ]
  · rw [report_exact]; exact ⟨rfl,rfl,rfl⟩
  · constructor
    · intro output member
      have same := List.mem_singleton.mp member; subst output
      exact ⟨⟨22,0,.app 0 [.var 0]⟩,by simp,rfl⟩
    · rw [schema_exact]

theorem survivor : Survivor registry context root 2 [child] :=
  ⟨ready,declaration,by simp,declaration_checked,rfl,rfl,[(0,0)],by decide +kernel,prepared,children_exact.symm⟩

private theorem legacy_clear (slot : Fin source.base.slots) : ¬ GeneralNominalMixedRecurrence.RecursAt source slot := by
  rintro ⟨⟨kind,_,_⟩,_⟩; exact Fin.elim0 kind

theorem old_selected : GeneralNominalCycleK2.Local registry context root (.selected 2 [child]) := by
  refine .selected ⟨ready,?_,?_,?_⟩ ⟨survivor,?_⟩
  · rintro ⟨_,_,_,slot,_,cycle⟩
    exact source_acyclic slot (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · rintro ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩
    exact source_acyclic visited.1 (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · rintro (pending | ⟨_,legacy⟩)
    · obtain ⟨_,d,visible,_,_,_,missing⟩ := pending
      have same := List.mem_singleton.mp visible; subst d
      exact missing prepared
    · rcases legacy with ⟨⟨_,_,_,slot,_,cycle⟩,_⟩ | ⟨⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩,_⟩
      · exact legacy_clear slot cycle
      · exact legacy_clear visited.1 cycle
  · intro key children found
    have copy := found
    obtain ⟨_,d,visible,_,identity,_⟩ := found
    have same := List.mem_singleton.mp visible; subst d
    have same : key = 2 := identity.symm; subst key
    exact ⟨rfl,survivor_children_functional registry checked context root 2 _ _ copy survivor⟩

theorem old_enabled : GeneralNominalCycleSteps.Installable registry initialState packet := by
  refine ⟨rfl,rfl,by simp [initialState,initial],by simp,rfl,by decide +kernel,prepared,?_,?_,?_,?_,?_⟩
  · change GeneralNominalCycleK2.Local registry context root (.selected 2 packet.children)
    rw [children_exact]; exact old_selected
  · intro prior member; cases member
  · intro other member _
    have same := List.mem_singleton.mp member; subst other; exact .refl _
  · exact ⟨model,(initial_models context root model).mpr source_models,packet_models⟩
  · exact GeneralNominalJointCandidates.initial_joint registry context root declaration (by simp) declaration_checked rfl [(0,0)]
      (by decide +kernel) prepared model packet_models

private theorem novel : ¬ GeneralNominalCycleSteps.Committed initialState packet := by
  intro committed
  have absent := committed.2 child (by rw [children_exact]; simp)
  cases absent

theorem old_step : GeneralNominalCycleSteps.Step registry root initialState oldInstalled :=
  ⟨root,.root,.install packet (pointEmitted packet) old_enabled novel⟩

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root := by
  refine ⟨rfl,prepared.1,prepared.2.1,(by intro m valid index; exact subtype_refl _),?_,rfl⟩
  intro identity member
  exact Nat.le_trans (GeneralNominalAllocation.member_le_max _ _ member) (by decide +kernel)

theorem old_formed : GeneralNominalSourceFormation.SourceFormed registry root oldInstalled :=
  .update (.initial context initial_source) old_step

theorem old_child_pending : GeneralNominalState.RootPending oldInstalled.context.state child.demand := by
  refine ⟨⟨0,by decide +kernel⟩,?_⟩
  rintro ⟨slot,source,head | nominal⟩
  · exact head rfl
  · have slotTwo : slot = (2 : Fin 4) := Fin.ext source
    subst slot
    obtain ⟨d,recorded⟩ := nominal
    cases recorded

end Yulang.GeneralNominalFeedbackObstruction
