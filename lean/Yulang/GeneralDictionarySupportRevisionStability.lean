import Yulang.GeneralDictionarySupportGeneratedChildrenRegression

/-! The reachable emission-gap state from cycle147 is not a stable endpoint.
A second model-equivalent point refinement at source slot1 remains available.
This rules out using that gap alone as a counterexample to the stable V5
GeneratedChildren obligation. No general Stable/selection theorem is asserted. -/
namespace Yulang.GeneralDictionarySupportRevisionStability
open GeneralNominalFeedbackObstruction GeneralNominalSaturationState
open GeneralNominalReobservationSteps GeneralNominalCommonBridge
open CommonNominalFullCarrier
open GeneralDictionaryCurrentRevisionObstruction
noncomputable def secondRevision : Revision revised where
  entries := fun slot => if slot.val = 1 then some point else revised.context.state.nominals slot
  catalogue := by
    intro slot descriptor found
    split at found
    · have eq := Option.some.inj found; subst descriptor; rfl
    · exact revised.context.state.catalogue slot descriptor found
  opaqueHeads := by intro _ _ _; rfl
  domain := by
    intro slot
    by_cases one : slot.val = 1
    · have eq : slot = (1 : Fin 4) := Fin.ext one
      subst slot; change (some point = none ↔ some GeneralNominalIntervalExamples.descriptor = none); simp
    · simp [one]

noncomputable abbrev twiceRevised := secondRevision.result

private theorem endpoints (m : Assignment)
    (ordinary : PresenceNormalForm.All CommonNominalFullCarrier.model m revised.context.state.ordinary) :
    Equivalent (m 2).1 (m 3).1 := by
  apply (GeneralNominalCaptureMerges.equations_exact m 2 (.var 3)).mp
  intro atom member
  apply ordinary atom
  simp only [revised,Revision.result,Revision.snapshot,revision,regenerate,installed,GeneralNominalFeedbackSites.install,Packet.privateContext,
    GeneralNominalRecursiveCandidates.privateState,GeneralNominalState.extend,
    GeneralNominalAllocation.propagate,source,List.mem_append]
  exact Or.inl (Or.inl member)

private theorem point_denotes_iff (m : Assignment)
    (equal : Equivalent (m 2).1 (m 3).1) :
    GeneralNominalState.Denotes source.base m (1 : Fin 4) point ↔
    GeneralNominalState.Denotes source.base m (1 : Fin 4) GeneralNominalIntervalExamples.descriptor := by
  constructor
  · rintro ⟨values,fits,denotes⟩
    change GeneralNominalState.FitsAll source.base m [.type (2,2)] values at fits
    cases fits with
    | @cons parameter value parameters values head tail =>
      cases tail
      cases value with
      | inr => cases head
      | inl value => exact ⟨[.inl value],.cons ⟨head.1,subtype_trans head.2 equal.1⟩ .nil,denotes⟩
  · rintro ⟨values,fits,denotes⟩
    change GeneralNominalState.FitsAll source.base m [.type (2,3)] values at fits
    cases fits with
    | @cons parameter value parameters values head tail =>
      cases tail
      cases value with
      | inr => cases head
      | inl value => exact ⟨[.inl value],.cons ⟨head.1,subtype_trans head.2 equal.2⟩ .nil,denotes⟩

theorem second_raw_models (m : Assignment) :
    GeneralNominalState.Models secondRevision.snapshot m ↔ GeneralNominalState.Models revised.context.state m := by
  constructor
  · intro valid
    refine ⟨valid.1,?_,valid.2.2⟩
    intro slot descriptor found
    by_cases one : slot.val = 1
    · have eq : slot = (1 : Fin 4) := Fin.ext one
      subst slot
      have eq : descriptor = GeneralNominalIntervalExamples.descriptor := Option.some.inj found.symm
      subst descriptor
      exact (point_denotes_iff m (endpoints m valid.2.2)).mp (valid.2.1 (1 : Fin 4) point (by rfl))
    · exact valid.2.1 slot descriptor (by simpa [Revision.snapshot,secondRevision,one] using found)
  · intro valid
    refine ⟨valid.1,?_,valid.2.2⟩
    intro slot descriptor found
    by_cases one : slot.val = 1
    · have eq : slot = (1 : Fin 4) := Fin.ext one
      subst slot
      have eq : descriptor = point := Option.some.inj found.symm
      subst descriptor
      exact (point_denotes_iff m (endpoints m valid.2.2)).mpr (valid.2.1 (1 : Fin 4) _ rfl)
    · exact valid.2.1 slot descriptor (by simpa [Revision.snapshot,secondRevision,one] using found)

theorem second_certified : Certified secondRevision where
  raw := fun m => (second_raw_models m).mp
  exact := by
    intro m
    change (_ ∧ _) ↔ (_ ∧ _)
    exact and_congr_left (fun _ => second_raw_models m)


theorem second_improves : Improves secondRevision := by
  constructor
  · rintro slot ⟨descriptor,found,pointed⟩
    by_cases one : slot.val = 1
    · refine ⟨point,?_,?_⟩
      · simp [Revision.snapshot,secondRevision,one]
      · intro parameter member
        have eq := List.mem_singleton.mp member
        subst parameter; rfl
    · exact ⟨descriptor,by simpa [Revision.snapshot,secondRevision,one] using found,pointed⟩
  · refine ⟨(1 : Fin 4),?_,point,rfl,?_⟩
    · rintro ⟨descriptor,found,pointed⟩
      have eq : descriptor = GeneralNominalIntervalExamples.descriptor := Option.some.inj found.symm
      subst descriptor
      have impossible := pointed (.type ((2 : Fin 4),(3 : Fin 4))) (List.mem_singleton_self _)
      exact (by decide +kernel : (2 : Fin 4) ≠ 3) impossible
    · intro parameter member
      have eq := List.mem_singleton.mp member
      subst parameter; rfl

/-- A genuine still-enabled administrative transition at the original root. -/
theorem remaining_update : GeneralNominalSupportSteps.At registry
    GeneralDictionarySupportRevisionObstruction.finish root
    { GeneralDictionarySupportRevisionObstruction.finish with current := twiceRevised } :=
  .administrative root twiceRevised (.reobserve root secondRevision second_certified second_improves)

/-- The previous syntactic emission gap does not meet the Stable premise. -/
theorem not_stable : ¬ GeneralNominalSupportSteps.Stable registry
    GeneralDictionarySupportRevisionObstruction.finish root := by
  intro stable
  exact stable root .root _ remaining_update

noncomputable abbrev pointFinish :=
  { GeneralDictionarySupportRevisionObstruction.finish with current := twiceRevised }

/-- Exact journal-model equivalence of the additional actual step. -/
theorem point_models_iff (m : Assignment) : Models pointFinish.current m ↔
    Models GeneralDictionarySupportRevisionObstruction.finish.current m :=
  second_certified.exact m

/-- Both original nominal observations now have point parameters. -/
theorem point_closed : PointClosed twiceRevised.context.state := by
  intro slot descriptor found
  change Fin 4 at slot
  change GeneralNominalState.Descriptor 4 at descriptor
  have splitCases : slot = (0 : Fin 4) ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
  rcases splitCases with same | same | same | same <;> subst slot
  · have same : descriptor = point := (Option.some.inj found).symm
    subst descriptor
    intro parameter member
    have same := List.mem_singleton.mp member
    subst parameter; rfl
  · have same : descriptor = point := (Option.some.inj found).symm
    subst descriptor
    intro parameter member
    have same := List.mem_singleton.mp member
    subst parameter; rfl
  · change none = some descriptor at found; cases found
  · change none = some descriptor at found; cases found

/-- Point closure closes this precision rule, not all support transitions. -/
theorem no_further_point_revision (next : Revision twiceRevised) : ¬ Improves next :=
  pointClosed_no_revision point_closed next

/-- The additional refinement preserves a concrete final model. -/
theorem point_models : Models pointFinish.current model :=
  (second_certified.exact model).mpr GeneralDictionarySupportRevisionObstruction.modeled_nonempty.1

/-- An actual third support step, rather than a fabricated closed snapshot. -/
theorem point_reachable : B4TargetV5.Reachable
    (GeneralNominalSupportBoundary.boundary GeneralDeclarationExamples.roles)
    registry root pointFinish := by
  obtain ⟨initial,started,path⟩ := GeneralDictionarySupportRevisionObstruction.reachable
  exact ⟨initial,started,.tail path ⟨root,.root,remaining_update⟩⟩

open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalUnaryCaptureFacts GeneralDeclarationPatterns GeneralDeclarations
theorem point_report : report twiceRevised.context declaration [((0 : Fin 4),(0 : Fin 4))] =
    captured twiceRevised.context.state (0 : Fin 4) 0 0 ((2 : Fin 4),(2 : Fin 4)) := by
  apply GeneralNominalUnaryCaptureFacts.report_exact twiceRevised.context declaration (0 : Fin 4) point rfl 0 ((2 : Fin 4),(2 : Fin 4)) rfl
  change GeneralNominalInspection.queries source context.interpretation declaration = _
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]

theorem point_children (check : DeclarationChecked registry.constructors GeneralDeclarationExamples.roles declaration) :
    GeneralNominalAllocation.children twiceRevised.context.state registry root declaration check
      (bindings twiceRevised.context.state (report twiceRevised.context declaration [((0 : Fin 4),(0 : Fin 4))])) = [newChild] := by
  rw [point_report]
  unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  simp [GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralDictionaryEmissionPlans.occurrence,
    GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,GeneralDeclarationDemands.outputTarget,
    GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,
    normalize,child,newChild,Declaration.outputNames,bindings,captured,GeneralNominalAllocation.allocation,output]
  exact ⟨rfl,rfl,rfl⟩

theorem point_generated_cases (focus : GeneralSourceDictionaries.Occurrence GeneralDeclarationExamples.roles)
    (generated : Generated pointFinish.current root focus) : focus = root ∨ focus = child := by
  induction generated with
  | root => exact Or.inl rfl
  | @child parent focus prior edge ih =>
    have edges : pointFinish.current.edges = [(root,child)] := by
      change [] ++ packet.children.map (fun c => (root,c)) = _
      rw [children_exact]; rfl
    rw [edges] at edge
    have same := List.mem_singleton.mp edge
    exact Or.inr (congrArg Prod.snd same)
  | @alias first last prior one two alias ih =>
    have sites : pointFinish.current.sites = [GeneralNominalDemandMerging.pointSite root,
        GeneralNominalFeedbackSites.childSite packet child] := by
      change [GeneralNominalDemandMerging.pointSite root] ++ _ = _
      simp [GeneralNominalFeedbackSites.emitted,children_exact]
    rw [sites] at two
    rcases List.mem_cons.mp two with same | same
    · subst last; exact Or.inl rfl
    · have same := List.mem_singleton.mp same
      subst last; exact Or.inr rfl

/-- The emitted current child is not among the old generated occurrences.
This is a source-supported, modeled reachable snapshot, not a raw journal. -/
theorem point_new_child_not_generated : ¬ Generated pointFinish.current root newChild := by
  intro generated
  rcases point_generated_cases newChild generated with same | same
  · have eq := congrArg (fun c => List.ofFn c.demand.arguments) same
    exact (by decide +kernel : ([(2,2)] : List GeneralSourceState.Interval) ≠ [(0,0)]) eq
  · have eq := congrArg (fun c => List.ofFn c.demand.arguments) same
    exact (by decide +kernel : ([(2,2)] : List GeneralSourceState.Interval) ≠ [(2,3)]) eq



/-- Even complete point-descriptor refinement does not repair the historical
child graph. This is still not a stable-selection counterexample. -/
theorem point_emission_gap :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary GeneralDeclarationExamples.roles)
      registry root pointFinish ∧
    Models pointFinish.current model ∧ PointClosed pointFinish.current.context.state ∧
    newChild ∈ GeneralNominalAllocation.children pointFinish.current.context.state registry root
      declaration declaration_checked
      (bindings pointFinish.current.context.state
        (report pointFinish.current.context declaration [((0 : Fin 4),(0 : Fin 4))])) ∧
    ¬ Generated pointFinish.current root newChild := by
  refine ⟨point_reachable,point_models,point_closed,?_,point_new_child_not_generated⟩
  rw [point_children]
  exact List.mem_singleton_self _

end Yulang.GeneralDictionarySupportRevisionStability
