import Yulang.GeneralNominalCaptureRefinement

/-! Simultaneous finite capture groups share one global refinement. Earlier
common presentations survive every subsequent replacement. -/
namespace Yulang.GeneralNominalCaptureFamilies
open GeneralNominalCaptureRefinement GeneralNominalCaptureComparison
open GeneralNominalOriginTerms GeneralNominalRecursiveInspection GeneralNominalHoleElimination
open GeneralNominalReadbackFunctionality GeneralNominalScopedRecipeLabels GeneralNominalFiniteMeaning
open GeneralNominalIndexedHoleReadback GeneralNominalSubtermOrder CommonNominalFullCarrier

variable {models : GeneralNominalCommonBridge.Assignment → Prop}
variable {identities : Nat → Nat} {keys : List Nat} {tests : List Test}

theorem transform_append (first last : List Operation) (term : Expr Nat) :
    transform (first ++ last) term = transform last (transform first term) := by
  induction first generalizing term with
  | nil => rfl
  | cons op rest ih => exact ih _

theorem transform_append_function (first last : List Operation) :
    transform (first ++ last) = fun term => transform last (transform first term) :=
  funext (transform_append first last)

theorem append
    (first : Refinement models context identities keys tests before middle one)
    (last : Refinement models context identities keys tests middle after two) :
    Refinement models context identities keys tests before after (one ++ two) := by
  induction first with
  | refl => exact last
  | next op present label readback allowed vocabulary bounded positive rest ih =>
    exact .next op present label readback allowed vocabulary bounded positive (ih last)

theorem replacement_meaning
    (known : Readback models (fun name => .source (identities name)) remaining
      (.source (identities hole)) tree) (canonical : Canonical tree) :
    EqualTerms models (fun model name => (model (identities name)).1) (.leaf hole) tree := by
  intro model valid
  have meaning := GeneralNominalFrontierValuations.indexed_meaning known canonical valid
    (source_unique model _) (fun name => (model (identities name)).1)
    (fun name _ => GeneralNominalUniformCaptureProduction.source_leaf_values identities model name)
  exact meaning.2 _ (.source _)

theorem canonical
    (refinement : Refinement models context identities keys tests before after operations)
    (known : Canonical term) : Canonical (transform operations term) := by
  induction refinement generalizing term with
  | refl => exact known
  | next op present label readback allowed vocabulary bounded positive rest ih =>
    exact ih (replacement_canonical known label.2.2)

theorem vocabulary
    (refinement : Refinement models context identities keys tests before after operations)
    (known : Vocabulary tests term) : Vocabulary tests (transform operations term) := by
  induction refinement generalizing term with
  | refl => exact known
  | next op present label readback allowed vocabulary bounded positive rest ih =>
    exact ih (replacement_vocabulary known vocabulary)

theorem closed
    (refinement : Refinement models context identities keys tests before after operations)
    (known : Closed before.holes term) : Closed after.holes (transform operations term) := by
  induction refinement generalizing term with
  | refl => exact known
  | next op present label readback allowed vocabulary bounded positive rest ih =>
    exact ih (replacement_closed known readback.2)

theorem meaning
    (refinement : Refinement models context identities keys tests before after operations) (term : Expr Nat) :
    EqualTerms models (fun model name => (model (identities name)).1) (transform operations term) term := by
  induction refinement generalizing term with
  | refl => exact fun _ _ => ⟨subtype_refl _,subtype_refl _⟩
  | next op present label readback allowed vocabulary bounded positive rest ih =>
    exact equal_trans (ih _) (replacement_equal (replacement_meaning readback label.2.2) term)

theorem equal
    (refinement : Refinement models context identities keys tests before after operations)
    (known : EqualTerms models (fun model name => (model (identities name)).1) first last) :
    EqualTerms models (fun model name => (model (identities name)).1)
      (transform operations first) (transform operations last) :=
  equal_trans (meaning refinement first) (equal_trans known (equal_symm (meaning refinement last)))

theorem below (operations : List Operation) (known : Below first last) :
    Below (transform operations first) (transform operations last) := by
  induction operations generalizing first last with
  | nil => exact known
  | cons op rest ih => exact ih (below_bind known (substitute op.hole op.tree))

theorem common
    (refinement : Refinement models context identities keys tests before after operations)
    (known : CommonMany models identities before.holes tests anchor terms) :
    CommonMany models identities after.holes tests (transform operations anchor) (terms.map (transform operations)) := by
  obtain ⟨term,shape,vocab,scope,one,others,same⟩ := known
  refine ⟨transform operations term,canonical refinement shape,vocabulary refinement vocab,
    closed refinement scope,below operations one,?_,equal refinement same⟩
  intro other member
  obtain ⟨prior,present,rfl⟩ := List.mem_map.mp member
  exact below operations (others prior present)

def transformLabels : List Operation →
    (GeneralSourceDictionaries.Occurrence roles → List GeneralDeclarationPatterns.Pattern) →
    GeneralSourceDictionaries.Occurrence roles → List GeneralDeclarationPatterns.Pattern
  | [], labels => labels
  | op :: rest, labels => transformLabels rest
      (GeneralNominalCanonicalPacketTransport.substituteLabels labels
        (GeneralNominalCanonicalHoleJournal.patternReplacement op.hole op.pattern))

theorem journal
    (refinement : Refinement models context identities keys tests before after operations)
    (prior : GeneralNominalCanonicalHoleJournal.Journal context root state before) :
    ∃ next : GeneralNominalCanonicalHoleJournal.Journal context root state after,
      next.labels = transformLabels operations prior.labels := by
  induction refinement with
  | refl => exact ⟨prior,rfl⟩
  | next op present label readback allowed vocabulary bounded positive rest ih =>
    exact ih (prior.replace label op.hole op.extra)

theorem trusted_inputs
    (refinement : Refinement (GeneralNominalSharedSupport.Models state facts)
      context identities keys tests before after operations)
    (prior : GeneralNominalSourceProducerHandoff.TrustedInputs state facts context
      (fun name => .source (identities name)) before.holes keys tests) :
    GeneralNominalSourceProducerHandoff.TrustedInputs state facts context
      (fun name => .source (identities name)) after.holes keys tests := by
  induction refinement with
  | refl => exact prior
  | next op present label readback allowed vocabulary bounded positive rest ih =>
    exact ih (GeneralNominalCommonTrustedLedger.inputs_replace prior
      ⟨op.pattern,op.tree,⟨label,readback⟩,allowed⟩ vocabulary)

structure Group where
  anchor : Expr Nat
  terms : List (Expr Nat)

def Group.transform (operations : List Operation) (group : Group) : Group :=
  ⟨GeneralNominalCaptureRefinement.transform operations group.anchor,
    group.terms.map (GeneralNominalCaptureRefinement.transform operations)⟩

def Group.Known (group : Group) (models : GeneralNominalCommonBridge.Assignment → Prop)
    (identities : Nat → Nat) (remaining : List Nat) (tests : List Test) : Prop :=
  Canonical group.anchor ∧ Vocabulary tests group.anchor ∧ Closed remaining group.anchor ∧
    ∀ term ∈ group.terms, Canonical term ∧ Vocabulary tests term ∧ Closed remaining term ∧
      EqualTerms models (fun model name => (model (identities name)).1) group.anchor term

theorem known
    (refinement : Refinement models context identities keys tests before after operations)
    (group : Group) (prior : group.Known models identities before.holes tests) :
    (group.transform operations).Known models identities after.holes tests := by
  refine ⟨canonical refinement prior.1,vocabulary refinement prior.2.1,closed refinement prior.2.2.1,?_⟩
  intro term member
  obtain ⟨old,present,rfl⟩ := List.mem_map.mp member
  have facts := prior.2.2.2 old present
  exact ⟨canonical refinement facts.1,vocabulary refinement facts.2.1,
    closed refinement facts.2.2.1,equal refinement facts.2.2.2⟩

theorem reconcile_groups
    (templates : NodeTemplates context keys tests) (inhabited : ∃ model, models model)
    (groups : List Group) (inventory : Inventory)
    (represented : ∀ group ∈ groups, group.Known models identities inventory.holes tests) :
    ∃ after operations, Refinement models context identities keys tests inventory after operations ∧
      ∀ group ∈ groups, CommonMany models identities after.holes tests
        (transform operations group.anchor) (group.terms.map (transform operations)) := by
  have all : ∀ length, ∀ groups : List Group, groups.length = length →
      ∀ inventory, (∀ group ∈ groups, group.Known models identities inventory.holes tests) →
      ∃ after operations, Refinement models context identities keys tests inventory after operations ∧
        ∀ group ∈ groups, CommonMany models identities after.holes tests
          (transform operations group.anchor) (group.terms.map (transform operations)) := by
    intro length
    induction length with
    | zero =>
      intro groups size inventory represented
      have empty := List.eq_nil_of_length_eq_zero size
      subst groups
      exact ⟨inventory,[],.refl _,by simp⟩
    | succ length ih =>
      intro groups size inventory represented
      cases groups with
      | nil => cases size
      | cons first rest =>
        have head := represented first (List.mem_cons_self ..)
        obtain ⟨middle,one,firstRefinement,firstCommon⟩ := reconcile templates inhabited inventory first.anchor first.terms
          head.1 head.2.1 head.2.2.1 head.2.2.2
        have tail : ∀ group ∈ rest.map (Group.transform one), group.Known models identities middle.holes tests := by
          intro group member
          obtain ⟨old,present,rfl⟩ := List.mem_map.mp member
          exact known firstRefinement old (represented old (List.mem_cons_of_mem _ present))
        have restLength : (rest.map (Group.transform one)).length = length := by
          simpa only [List.length_map] using Nat.succ.inj size
        obtain ⟨after,two,lastRefinement,lastCommon⟩ := ih _ restLength middle tail
        refine ⟨after,one ++ two,append firstRefinement lastRefinement,?_⟩
        intro group member
        rcases List.mem_cons.mp member with rfl | member
        · simpa only [transform_append_function,List.map_map,Function.comp_def] using common lastRefinement firstCommon
        · have result := lastCommon (group.transform one) (List.mem_map.mpr ⟨group,member,rfl⟩)
          simpa only [Group.transform,transform_append_function,List.map_map,Function.comp_def] using result
  exact all _ groups rfl inventory represented

theorem reconcile_journal
    (templates : NodeTemplates context keys tests) (inhabited : ∃ model, models model)
    (groups : List Group) (inventory : Inventory)
    (valid : Valid (GeneralNominalSourceLabelVocabulary.tests keys) inventory)
    (prior : GeneralNominalCanonicalHoleJournal.Journal context root state inventory)
    (represented : ∀ group ∈ groups, group.Known models identities inventory.holes tests) :
    ∃ after operations, Refinement models context identities keys tests inventory after operations ∧
      Valid (GeneralNominalSourceLabelVocabulary.tests keys) after ∧
      operations.length ≤ inventory.holes.length ∧
      (∃ growth, Trace (GeneralNominalSourceLabelVocabulary.tests keys) growth inventory after operations.length) ∧
      (∃ next : GeneralNominalCanonicalHoleJournal.Journal context root state after,
        next.labels = transformLabels operations prior.labels) ∧
      ∀ group ∈ groups, CommonMany models identities after.holes tests
        (transform operations group.anchor) (group.terms.map (transform operations)) := by
  obtain ⟨after,operations,refinement,common⟩ := reconcile_groups templates inhabited groups inventory represented
  obtain ⟨growth,trace⟩ := refinement.trace
  exact ⟨after,operations,refinement,trace_valid trace valid,refinement.count.2,
    ⟨growth,trace⟩,journal refinement prior,common⟩

end Yulang.GeneralNominalCaptureFamilies
