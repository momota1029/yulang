import Yulang.GeneralNominalGroundProduction
import Yulang.GeneralNominalPeelingSources

/-! A branching Show registry and the inhabited point source
Show (pair (list int) int). The remaining general factorization premise is
explicit in its accessibility theorem. -/
namespace Yulang.GeneralNominalGroundExamples
open GeneralDeclarations GeneralDeclarationPatterns
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalReadbackFunctionality GeneralNominalCompoundReadback
open GeneralNominalGroundAccessibility GeneralNominalGroundProduction
open CommonNominalFullCarrier

abbrev leftChild : Clause := ⟨180,0,[.var 0],[]⟩
abbrev rightChild : Clause := ⟨181,0,[.var 1],[]⟩
abbrev pairDecl : Declaration := ⟨180,0,[.app 5 [.var 0,.var 1]],[leftChild,rightChild],[],[]⟩
abbrev registry : Registry :=
  ⟨constructors,roles,[pairDecl,GeneralDeclarationExamples.display,GeneralNominalExamples.intDisplay]⟩

theorem pair_checked : DeclarationChecked constructors roles pairDecl := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,roles,GeneralDeclarationExamples.bareRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro clause member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨rfl,rfl⟩
    · cases List.mem_singleton.mp member; exact ⟨rfl,rfl⟩
  · intro clause member
    rcases List.mem_cons.mp member with rfl | member
    · exact (checkSmaller_exact _ _).mp (by decide +kernel)
    · cases List.mem_singleton.mp member; exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member
    rcases List.mem_cons.mp member with rfl | member
    · unfold ConservativeSmaller; decide +kernel
    · cases List.mem_singleton.mp member; unfold ConservativeSmaller; decide +kernel
  · intro clause member capture
    rcases List.mem_cons.mp member with rfl | member
    · constructor
      · simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,
          Roles.argsSize,Roles.Term.size]; omega
      · intro name
        simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,
          Roles.argsOccurrences,Roles.Term.occurrences]
    · cases List.mem_singleton.mp member
      constructor
      · simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,
          Roles.argsSize,Roles.Term.size]; omega
      · intro name
        simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,
          Roles.argsOccurrences,Roles.Term.occurrences]

theorem checked : Checked registry := by
  refine ⟨by decide +kernel,?_⟩
  intro declaration member
  rcases List.mem_cons.mp member with rfl | member
  · exact pair_checked
  rcases List.mem_cons.mp member with rfl | member
  · exact GeneralDeclarationExamples.display_checked
  · cases List.mem_singleton.mp member; exact GeneralNominalExamples.int_display_checked

abbrev original : GeneralNominalState.State := { GeneralNominalPeelingSources.source 0 with seed := 2 }
abbrev source : GeneralNominalState.State := GeneralNominalState.extend original [2]
  (GeneralNominalAllocation.equations 2 (.pair (.var 0) (.var 1)))
abbrev interpretation : GeneralNominalInspection.Interpretation where
  primitives := fun name => if name = 5 then some .pair else GeneralNominalExamples.interpretation.primitives name
  invariantNominal := GeneralNominalExamples.interpretation.invariantNominal
  disjoint := by intro name yes; simp_all
abbrev context : GeneralNominalCandidates.Context := ⟨source,interpretation⟩
abbrev root : GeneralSourceDictionaries.Occurrence roles :=
  ⟨180,⟨0,fun _ => (2,2),[],by intro _ impossible; cases impossible⟩⟩
abbrev labels : List Pattern := [.app 5 [.app 0 [.app 2 []],.app 2 []]]

abbrev intTerm : Expr Nat := .node (.scalar .int) Fin.elim0
abbrev listTerm : Expr Nat := .node (.nominal 0 1) (fun _ => intTerm)
abbrev pairTerm : Expr Nat := .node (.structural .pair) (fun index => if index.val = 0 then listTerm else intTerm)

theorem closed : ClosedTerm context labels[0] pairTerm := by
  refine ⟨?_,?_,?_⟩
  · change GeneralNominalInspection.translate constructors interpretation (normalize labels[0]) = quote pairTerm
    simp [labels,normalize,normalizeArgs,GeneralNominalInspection.translate,interpretation,
      quote,listTerm,intTerm,
      List.ofFn_succ,arity,GeneralNormalizedObservation.Shape.arity]
  · simp [listTerm,intTerm,Expr.leaves,List.ofFn_succ,arity,GeneralNormalizedObservation.Shape.arity]
  · refine ⟨trivial,?_⟩
    intro index
    change Canonical (if index.val = 0 then listTerm else intTerm)
    split
    · exact ⟨trivial,fun _ => ⟨trivial,fun index => Fin.elim0 index⟩⟩
    · exact ⟨trivial,fun index => Fin.elim0 index⟩

theorem models (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalState.Models source model ↔
      GeneralNominalState.Models (GeneralNominalPeelingSources.source 0) model ∧
      Equivalent (model 2).1 (pair (model 0).1 (model 1).1) := by
  rw [GeneralNominalState.extend_models,GeneralNominalCaptureMerges.equations_exact]
  rfl

theorem ground : GroundRoots context root labels := by
  refine ⟨rfl,?_⟩
  intro index
  have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
  refine ⟨pairTerm,?_,?_⟩
  · simpa only [zero] using closed
  · intro model valid
    have facts := (models model).mp valid
    have left := GeneralNominalPeelingSources.ground 0 model facts.1
    have right := (GeneralNominalPeelingSources.source_models 0 model).mp facts.1 |>.2
    have pairEqual : Equivalent (pair (model 0).1 (model 1).1)
        (pair (nominal 0 [.inl (.base .int)]) (.base .int)) :=
      ⟨(common_pair_iff ..).mpr ⟨left.1,right.1⟩,(common_pair_iff ..).mpr ⟨left.2,right.2⟩⟩
    have equal : Equivalent (model 2).1 (pair (nominal 0 [.inl (.base .int)]) (.base .int)) :=
      ⟨subtype_trans facts.2.1 pairEqual.1,subtype_trans pairEqual.2 facts.2.2⟩
    simpa [denote,build,pairTerm,listTerm,intTerm,shapeValue,GeneralNormalizedObservation.Shape.term,
      GeneralNormalizedObservation.Shape.arity,List.ofFn_succ,arity,Core.PresenceGeneration.TyTerm.eval,
      CommonNominalFullCarrier.model] using equal

theorem source_support : GeneralNominalState.sources source ⊆ [0,1,2] := by
  apply GeneralNominalAllocationSupport.extend_sources original [2] _ ?_ (by simp) ?_
  · intro identity member
    have below := (GeneralNominalPeelingSources.initial_source 0).below_seed identity member
    have bound : identity ≤ 1 := below
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    omega
  · intro atom member
    exact GeneralNominalAllocationSupport.equation_sources 2 (.pair (.var 0) (.var 1)) (by simp)
      (by simp [GeneralNominalState.typeSources]) atom member

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root := by
  refine ⟨rfl,⟨rfl,?_⟩,?_,(by intro _ _ _; exact subtype_refl _),?_,rfl⟩
  · intro name primitive found
    by_cases five : name = 5
    · subst name
      have same : primitive = .pair := Option.some.inj found |>.symm
      subst primitive
      exact ⟨⟨[.type,.type],5⟩,rfl,rfl⟩
    · have old : GeneralNominalExamples.interpretation.primitives name = some primitive := by
        simpa only [interpretation,five,ite_false] using found
      exact (GeneralNominalPeelingSources.initial_source 0).metadata.2 name primitive old
  · constructor
    · intro index
      have member : 2 ∈ GeneralNominalState.sources source := by
        simp [GeneralNominalState.sources,GeneralNominalState.extend]
      exact ⟨member,member⟩
    · intro output impossible; cases impossible
  · intro identity member
    have present := source_support member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    change identity ≤ 2
    omega

theorem point_source : GeneralNominalActualBudget.PointSource context root :=
  ⟨(GeneralNominalPeelingSources.point_source 0).intervals,
    (GeneralNominalPeelingSources.point_source 0).nominalTypes,
    (GeneralNominalPeelingSources.point_source 0).nominalRows,by intro index; rfl⟩

abbrev witness : GeneralNominalCommonBridge.Assignment := fun identity =>
  (if identity = 0 then nominal 0 [.inl (.base .int)]
   else if identity = 1 then .base .int
   else pair (nominal 0 [.inl (.base .int)]) (.base .int),Common.rowEmpty)

theorem inhabited : GeneralNominalState.Models source witness := by
  apply (models witness).mpr
  constructor
  · apply (GeneralNominalPeelingSources.source_models 0 witness).mpr
    constructor
    · intro index bound
      have zero : index = 0 := by omega
      subst index
      exact ⟨subtype_refl _,subtype_refl _⟩
    · exact ⟨subtype_refl _,subtype_refl _⟩
  · exact ⟨subtype_refl _,subtype_refl _⟩

theorem accessible (factorization : GroundCaptureFactorization roles registry context) :
    Acc (fun next current => GeneralNominalActualInspectionSteps.Step registry root current next)
      (GeneralNominalSupport.initial context root) :=
  ground_accessible_of_capture_factorization checked initial_source point_source ground factorization

theorem both_positions (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models source model) :
    At model .actual (.structural (.source 2) .pair 0) (denote (fun _ => .bottom) listTerm) ∧
    At model .actual (.structural (.source 2) .pair 1) (.base .int) := by
  have facts := (models model).mp valid
  have left := GeneralNominalPeelingSources.ground 0 model facts.1
  have right := (GeneralNominalPeelingSources.source_models 0 model).mp facts.1 |>.2
  let values : Fin 2 → Ty := fun index => if index.val = 0 then nominal 0 [.inl (.base .int)] else .base .int
  have pairEqual : Equivalent (pair (model 0).1 (model 1).1)
      (pair (nominal 0 [.inl (.base .int)]) (.base .int)) :=
    ⟨(common_pair_iff ..).mpr ⟨left.1,right.1⟩,(common_pair_iff ..).mpr ⟨left.2,right.2⟩⟩
  have rootMeaning : At model .actual (.source 2) (build (.structural .pair) values) := by
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual observed
    cases observed
    exact ⟨subtype_trans facts.2.1 pairEqual.1,subtype_trans pairEqual.2 facts.2.2⟩
  constructor
  · have result := project_value (.structural .pair) trivial values rootMeaning ⟨0,by decide +kernel⟩
    change At model .actual (.structural (.source 2) .pair 0) (nominal 0 [.inl (.base .int)]) at result
    simpa only [listTerm,intTerm,denote,build,List.ofFn_succ,arity,List.ofFn_zero] using result
  · exact project_value (.structural .pair) trivial values rootMeaning ⟨1,by decide +kernel⟩

end Yulang.GeneralNominalGroundExamples
