import Yulang.GeneralDictionaryNonterminalCertifiedEvidence

/-! The certified fixture has no old recursive Evidence: its old child bounds
are private allocation IDs, not located source slots. This records the precise
obstruction rather than assuming old child evidence. -/
namespace Yulang.GeneralDictionaryNonterminalOldObstruction
open GeneralDictionaryNonterminalCertifiedEvidence (registry leaf)
open GeneralDictionaryNonterminalNonpointExample (declaration child outputRoot checked variable_clauses)
open GeneralDictionaryNonpointCertifiedOutput (context source bounds shape)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryRecursiveEvidence
noncomputable abbrev captures := bindings context.state (report context declaration bounds)
noncomputable abbrev frame := GeneralNominalAllocation.frame (roles := GeneralDictionaryNonpointStrict.roles)
 context.state registry outputRoot.identity captures
noncomputable abbrev occurrence := GeneralDictionaryEmissionPlans.occurrence frame
 (GeneralDeclarationDemands.emit outputRoot.identity declaration child
 (checked.signature.2.2.2 child (List.mem_singleton_self _))
 (frame.capture declaration.id) (frame.allocation declaration.id child))

theorem children_exact : GeneralNominalAllocation.children context.state registry outputRoot declaration checked captures = [occurrence] := by
 have canonical : GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration := by decide +kernel
 simp only [GeneralNominalAllocation.children,GeneralDictionaryEmissionPlans.children,
   GeneralCanonicalChildOrder.canonicalEmit,canonical]
 rfl

theorem captures_exact : captures = [(7,3,4),(7,4,4)] := by
 unfold captures
 rw [show report context declaration bounds = GeneralDictionarySemanticCollapseBranch.oldRootReport shape from
   (GeneralDictionarySemanticCollapseBranch.reports shape declaration GeneralDictionaryNonterminalCertifiedEvidence.queries).1]
 rfl

theorem child_unlocated : arguments context occurrence = none := by
 simp [arguments,GeneralNominalCandidates.arguments,occurrence,
   GeneralDictionaryEmissionPlans.occurrence,GeneralDeclarationDemands.emit,
   GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,
   frame,GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,captures_exact,
   GeneralNominalAllocation.occurrences,GeneralDeclarationPatterns.normalize,List.ofFn_succ]
 decide +kernel

theorem child_no_instance (valuation : GeneralNominalCommonBridge.Assignment)
    (key : Nat) (children : List (GeneralSourceDictionaries.Occurrence GeneralDictionaryNonpointStrict.roles)) :
    ¬ Instance registry context valuation occurrence key children := by
 rintro ⟨decl,visible,check,identity,role,intervals,located,rest⟩
 rw [child_unlocated] at located
 cases located

theorem child_no_evidence (valuation : GeneralNominalCommonBridge.Assignment)
    (payload : GeneralDictionaryReadback.Payload) :
    ¬ Evidence registry context valuation occurrence payload := by
 intro evidence
 cases payload with
 | node key dictionaries =>
   obtain ⟨children,rule,all⟩ := evidence_node_elim registry context valuation occurrence key dictionaries evidence
   exact child_no_instance valuation key children rule
theorem root_no_evidence (valuation : GeneralNominalCommonBridge.Assignment)
    (payload : GeneralDictionaryReadback.Payload) :
    ¬ Evidence registry context valuation outputRoot payload := by
 intro evidence
 cases payload with
 | node key dictionaries =>
   obtain ⟨emitted,rule,all⟩ := evidence_node_elim registry context valuation outputRoot key dictionaries evidence
   obtain ⟨decl,visible,check,identity,role,intervals,located,finished,ready,children,rest⟩ := rule
   simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
   rcases visible with rfl | rfl
   · have old_located : arguments context outputRoot = some bounds := by decide +kernel
     have same := Option.some.inj (located.symm.trans old_located)
     subst intervals
     rw [children,children_exact] at all
     cases all with
     | cons first tail => exact child_no_evidence valuation _ first
   · cases role

/-- The obstruction is present even at a formed inhabited initial source;
the certified revision subsequently produces a located child and full Evidence. -/
theorem old_absent_current_present :
    (∀ payload, ¬ Evidence registry context GeneralDictionaryNonpointStrict.model outputRoot payload) ∧
    Evidence registry GeneralDictionaryNonterminalCertifiedEvidence.after.current.context
      GeneralDictionaryNonpointStrict.model outputRoot (.node declaration.id [.node leaf.id []]) :=
 ⟨root_no_evidence GeneralDictionaryNonpointStrict.model,GeneralDictionaryNonterminalCertifiedEvidence.full_evidence⟩
end Yulang.GeneralDictionaryNonterminalOldObstruction
