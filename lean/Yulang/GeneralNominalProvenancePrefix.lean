import Yulang.GeneralNominalProvenanceSource
import Yulang.GeneralNominalValueSteps
import Yulang.GeneralNominalSpineFacts
import Yulang.GeneralNominalMaterializedHeadRecovery

/-! The first real installation for the six-role captured-value fixture. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalProvenancePrefix
open GeneralNominalProvenanceDeclarations GeneralNominalProvenanceSource
open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationDemands
open GeneralSourceDictionaries GeneralNominalSaturationState GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveInspection CommonNominalFullCarrier

abbrev packet : Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,p,p_checked,pBounds⟩
abbrev outer (slot : Nat) : Origin := .nominal (.source slot) 0 0
abbrev inner (slot : Nat) : Origin := .nominal (outer slot) 0 0
abbrev reportP : Report state where
  captures := [⟨0,(2,2),some (inner 0)⟩,⟨1,(5,5),some (inner 3)⟩,⟨2,(6,6),none⟩]
  inspected := [(0,0),(1,1),(3,3),(4,4)]
  checked := [(0,0),(3,3),(6,6),(0,0),(1,1),(2,2),(3,3),(4,4),(5,5),(6,6)]
  anchors := [(outer 0,(1,1)),(inner 0,(2,2)),(outer 3,(4,4)),(inner 3,(5,5))]
  tests := [(outer 0,.nominal 0 1),(outer 3,.nominal 0 1)]

theorem report_exact : report context p pBounds = reportP := by
  unfold report
  rw [p_queries]
  simp [inspectMany.eq_1,inspectMany.eq_2,inspect.eq_1,inspect.eq_3,inspect.eq_5,
    Report.visit,Report.append,typeArguments,pBounds,context,state,entries,listDescriptor,boxDescriptor]
  repeat first
    | rw [inspectMany.eq_def]
    | rw [inspect.eq_def]
    | simp [Report.visit,Report.append,typeArguments,block,context,state,entries,listDescriptor,boxDescriptor,bindings,reportP,outer,inner]
  all_goals decide +kernel

theorem packet_bindings : packet.bindings = [(0,(2,2)),(1,(5,5)),(2,(6,6))] := p_bindings

abbrev allocated (purpose owner position : Nat) : Nat := GeneralNominalAllocation.source state registry root.identity
  (GeneralNominalAllocation.origin root.identity p.id purpose owner position)
abbrev argumentLo (clause position : Nat) := allocated 3 clause position
abbrev argumentHi (clause position : Nat) := allocated 4 clause position
abbrev output (name : Nat) := allocated 2 name 0
abbrev inputUse (target name : Nat) : GeneralNominalMaterialization.Use := ⟨name,.nominal (.source target) 0 0,.actual⟩
abbrev outputUse (name : Nat) : GeneralNominalMaterialization.Use := ⟨name,.source (output name),.actual⟩
abbrev inputUses (clause position name : Nat) := [inputUse (argumentLo clause position) name,inputUse (argumentHi clause position) name]
abbrev inputTests (clause position : Nat) : List (Origin × Test) :=
  [(.source (argumentLo clause position),.nominal 0 1),(.source (argumentHi clause position),.nominal 0 1)]
abbrev schema : GeneralNominalMaterialization.Schema :=
  ⟨inputUses 10 0 0 ++ [outputUse 3] ++ inputUses 11 0 0 ++ inputUses 11 1 1 ++ [outputUse 3] ++
    inputUses 12 0 1 ++ [outputUse 4] ++ inputUses 13 0 1 ++ inputUses 13 1 0 ++ [outputUse 4] ++
    inputUses 14 0 0 ++ inputUses 14 1 1,
    inputTests 10 0 ++ inputTests 11 0 ++ inputTests 11 1 ++ inputTests 12 0 ++
    inputTests 13 0 ++ inputTests 13 1 ++ inputTests 14 0 ++ inputTests 14 1,false⟩

theorem sorted : GeneralCanonicalChildOrder.canonicalDeclaration p = p := by
  change {p with requirements := GeneralCanonicalChildOrder.canonicalRequirements p.requirements} = p
  have order : GeneralCanonicalChildOrder.canonicalRequirements p.requirements = p.requirements :=
    List.mergeSort_of_pairwise (by decide +kernel)
  rw [order]

theorem schema_exact : generated registry context root p p_checked pBounds = schema := by
  unfold generated GeneralNominalMaterialization.requests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,sorted]
  rw [p_bindings]
  simp [GeneralNominalMaterialization.rootRequests,root,p,extractA,childW,extractB,childG,childP,
    GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralNominalMaterialization.emissionRequests,
    GeneralNominalMaterialization.inputRequests,List.ofFn_succ,normalize,normalizeArgs,
    GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,GeneralNominalMaterialization.schemas,
    GeneralNominalMaterialization.Schema.append,GeneralNominalInspection.translate,interpretation,constructors,
    GeneralDeclarationExamples.constructors,GeneralDeclarationDemands.outputTarget,GeneralDeclarationDemands.inputInterval,
    GeneralDeclarationDemands.childDemand,Declaration.outputNames,GeneralNominalAllocation.capture,
    GeneralNominalAllocation.allocation,GeneralNominalAllocation.occurrences,schema,inputUses,inputTests,inputUse,outputUse,
    argumentLo,argumentHi,output,allocated,context,state]


abbrev intValue : Ty := .base .int
abbrev listValue : Ty := nominal 0 [.inl intValue]
def witness : GeneralNominalCommonBridge.Assignment := fun source =>
  if source ≤ 7 then model intValue intValue intValue source else (listValue,Common.rowEmpty)

theorem witness_small (source : Nat) (bound : source ≤ 7) :
    witness source = model intValue intValue intValue source := by simp [witness,bound]

theorem witness_allocated (purpose owner position : Nat) : (witness (allocated purpose owner position)).1 = listValue := by
  have large := GeneralNominalIdentities.source_above_seed state.seed
    (GeneralNominalAllocation.origin root.identity p.id purpose owner position)
  have notSmall : ¬ allocated purpose owner position ≤ 7 := by
    change 7 < allocated purpose owner position at large
    omega
  simp [witness,notSmall]
  rfl

theorem witness_source : GeneralNominalState.Models state witness := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · intro _ _ impossible; cases impossible
  · intro _ member; cases member
  · intro slot descriptor recorded
    change entries slot = some descriptor at recorded
    unfold entries at recorded
    split at recorded
    · rename_i same; subst slot
      cases Option.some.inj recorded
      apply (GeneralNominalState.denotes_singleton_exact base _ 0 1 (listDescriptor 1) rfl).mpr
      exact ⟨subtype_refl _,subtype_refl _⟩
    · split at recorded
      · rename_i same; subst slot
        cases Option.some.inj recorded
        apply (GeneralNominalState.denotes_singleton_exact base _ 1 2 (listDescriptor 2) rfl).mpr
        exact ⟨subtype_refl _,subtype_refl _⟩
      · split at recorded
        · rename_i same; subst slot
          cases Option.some.inj recorded
          apply (GeneralNominalState.denotes_singleton_exact base _ 3 4 (listDescriptor 4) rfl).mpr
          exact ⟨subtype_refl _,subtype_refl _⟩
        · split at recorded
          · rename_i same; subst slot
            cases Option.some.inj recorded
            apply (GeneralNominalState.denotes_singleton_exact base _ 4 5 (listDescriptor 5) rfl).mpr
            exact ⟨subtype_refl _,subtype_refl _⟩
          · split at recorded
            · rename_i same; subst slot
              cases Option.some.inj recorded
              apply (GeneralNominalState.denotes_singleton_exact base _ 6 7 boxDescriptor rfl).mpr
              exact ⟨subtype_refl _,subtype_refl _⟩
            · cases recorded

private theorem fixed {ref : GeneralNominalProjections.Ref} {value actual : Ty}
    (one : Observes witness (embed ref) value) (two : Observes witness (embed ref) actual) : Equivalent actual value :=
  nominal_observation_unique witness ref actual value two one

private theorem seen_outer_zero : Observes witness (outer 0) listValue :=
  .nominal (.source 0) ⟨subtype_refl _,subtype_refl _⟩ rfl
private theorem seen_outer_three : Observes witness (outer 3) listValue :=
  .nominal (.source 3) ⟨subtype_refl _,subtype_refl _⟩ rfl
private theorem seen_inner_zero : Observes witness (inner 0) intValue :=
  .nominal seen_outer_zero ⟨subtype_refl _,subtype_refl _⟩ rfl
private theorem seen_inner_three : Observes witness (inner 3) intValue :=
  .nominal seen_outer_three ⟨subtype_refl _,subtype_refl _⟩ rfl

private theorem outer_zero (actual : Ty) (seen : Observes witness (outer 0) actual) : Equivalent actual listValue :=
  fixed (ref := .argument (.source 0) 0 0) seen_outer_zero seen
private theorem outer_three (actual : Ty) (seen : Observes witness (outer 3) actual) : Equivalent actual listValue :=
  fixed (ref := .argument (.source 3) 0 0) seen_outer_three seen
private theorem inner_zero (actual : Ty) (seen : Observes witness (inner 0) actual) : Equivalent actual intValue :=
  fixed (ref := .argument (.argument (.source 0) 0 0) 0 0) seen_inner_zero seen
private theorem inner_three (actual : Ty) (seen : Observes witness (inner 3) actual) : Equivalent actual intValue :=
  fixed (ref := .argument (.argument (.source 3) 0 0) 0 0) seen_inner_three seen

theorem projection_models : ProjectionModels state reportP witness := by
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    simp only [reportP,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨⟨_,seen_outer_zero⟩,fun actual seen => ⟨(outer_zero actual seen).2,(outer_zero actual seen).1⟩⟩
    · exact ⟨⟨_,seen_inner_zero⟩,fun actual seen => ⟨(inner_zero actual seen).2,(inner_zero actual seen).1⟩⟩
    · exact ⟨⟨_,seen_outer_three⟩,fun actual seen => ⟨(outer_three actual seen).2,(outer_three actual seen).1⟩⟩
    · exact ⟨⟨_,seen_inner_three⟩,fun actual seen => ⟨(inner_three actual seen).2,(inner_three actual seen).1⟩⟩
  · intro test member actual seen
    simp only [reportP,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact ⟨[.inl intValue],rfl,outer_zero actual seen⟩
    · exact ⟨[.inl intValue],rfl,outer_three actual seen⟩
  · intro first one last two same origin recorded actual seen
    simp only [reportP,List.mem_cons,List.not_mem_nil,or_false] at one two
    rcases one with rfl | rfl | rfl <;> rcases two with rfl | rfl | rfl
    all_goals cases same
    all_goals cases recorded
    all_goals first
      | exact ⟨(inner_zero actual seen).2,(inner_zero actual seen).1⟩
      | exact ⟨(inner_three actual seen).2,(inner_three actual seen).1⟩
  · intro first one last two same a b ha hb x y hx hy
    simp only [reportP,List.mem_cons,List.not_mem_nil,or_false] at one two
    rcases one with rfl | rfl | rfl <;> rcases two with rfl | rfl | rfl
    all_goals cases same
    all_goals cases ha
    all_goals cases hb
    · exact nominal_observation_unique witness (.argument (.argument (.source 0) 0 0) 0 0) x y hx hy
    · exact nominal_observation_unique witness (.argument (.argument (.source 3) 0 0) 0 0) x y hx hy


private def binderValue (name : Nat) : Ty := if name = 0 ∨ name = 1 then intValue else listValue

private theorem use_shapes (entry : GeneralNominalMaterialization.Use) (member : entry ∈ schema.variables) :
    (∃ purpose owner position name, (name = 0 ∨ name = 1) ∧
      entry = inputUse (allocated purpose owner position) name) ∨ entry = outputUse 3 ∨ entry = outputUse 4 := by
  simp only [schema,inputUses,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr rfl)
    | exact Or.inl ⟨_,_,_,_,Or.inl rfl,rfl⟩
    | exact Or.inl ⟨_,_,_,_,Or.inr rfl,rfl⟩

private theorem use_value (entry : GeneralNominalMaterialization.Use) (member : entry ∈ schema.variables) :
    (∃ actual, Observes witness entry.origin actual) ∧
      ∀ actual, Observes witness entry.origin actual → Equivalent actual (binderValue entry.name) := by
  rcases use_shapes entry member with ⟨purpose,owner,position,name,names,rfl⟩ | rfl | rfl
  · have seen : Observes witness (inputUse (allocated purpose owner position) name).origin intValue := by
      apply Observes.nominal (.source _)
      · rw [witness_allocated]; exact ⟨subtype_refl _,subtype_refl _⟩
      · rfl
    refine ⟨⟨_,seen⟩,?_⟩
    intro actual observed
    have equal := fixed (ref := .argument (.source (allocated purpose owner position)) 0 0) seen observed
    simpa [inputUse,binderValue,names] using equal
  · refine ⟨⟨_,.source _⟩,?_⟩
    intro actual observed
    cases observed
    change Equivalent (witness (allocated 2 3 0)).1 listValue
    rw [witness_allocated]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · refine ⟨⟨_,.source _⟩,?_⟩
    intro actual observed
    cases observed
    change Equivalent (witness (allocated 2 4 0)).1 listValue
    rw [witness_allocated]
    exact ⟨subtype_refl _,subtype_refl _⟩

private theorem use_variable (entry : GeneralNominalMaterialization.Use) (member : entry ∈ schema.variables)
    (actual : Ty) (seen : Observes witness entry.origin actual) :
    GeneralNominalMaterialization.VariableHolds p
      (GeneralNominalAllocation.capture state registry root.identity p.id packet.bindings)
      witness entry.name entry.mode actual := by
  have equal := (use_value entry member).2 actual seen
  rcases use_shapes entry member with ⟨purpose,owner,position,name,names,rfl⟩ | rfl | rfl
  · rcases names with rfl | rfl
    · change GeneralNominalCaptureMerges.Fits witness
        ((GeneralNominalAllocation.capture state registry root.identity p.id packet.bindings).inputs 0) actual
      rw [packet_bindings]
      change GeneralNominalCaptureMerges.Fits witness (2,2) actual
      exact ⟨equal.2,equal.1⟩
    · change GeneralNominalCaptureMerges.Fits witness
        ((GeneralNominalAllocation.capture state registry root.identity p.id packet.bindings).inputs 1) actual
      rw [packet_bindings]
      change GeneralNominalCaptureMerges.Fits witness (5,5) actual
      exact ⟨equal.2,equal.1⟩
  · change Equivalent actual (witness (allocated 2 3 0)).1
    rw [witness_allocated]
    exact equal
  · change Equivalent actual (witness (allocated 2 4 0)).1
    rw [witness_allocated]
    exact equal

private theorem test_value (test : Origin × Test) (member : test ∈ schema.tests) :
    (∃ actual, Observes witness test.1 actual) ∧ ∀ actual, Observes witness test.1 actual → test.2.Holds actual := by
  have shape : ∃ purpose owner position, test = (.source (allocated purpose owner position),.nominal 0 1) := by
    simp only [schema,inputTests,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨_,_,_,rfl⟩
  obtain ⟨purpose,owner,position,rfl⟩ := shape
  refine ⟨⟨_,.source _⟩,?_⟩
  intro actual observed
  cases observed
  rw [witness_allocated]
  exact ⟨[.inl intValue],rfl,subtype_refl _,subtype_refl _⟩

theorem material_models : GeneralNominalMaterialization.Models state p
    (GeneralNominalAllocation.capture state registry root.identity p.id packet.bindings)
    reportP schema witness := by
  refine ⟨test_value,?_,?_,?_⟩
  · intro entry member
    exact ⟨(use_value entry member).1,fun actual seen => use_variable entry member actual seen⟩
  · intro first one last two same _ _ a b ha hb
    have left := (use_value first one).2 a ha
    have right := (use_value last two).2 b hb
    rw [same] at left
    exact ⟨subtype_trans left.1 right.2,subtype_trans right.1 left.2⟩
  · intro entry member captured present same _ origin recorded a b ha hb
    have left := (use_value entry member).2 a ha
    rw [same] at left
    simp only [reportP,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl | rfl
    all_goals cases recorded
    · have right := inner_zero b hb
      exact ⟨subtype_trans left.1 right.2,subtype_trans right.1 left.2⟩
    · have right := inner_three b hb
      exact ⟨subtype_trans left.1 right.2,subtype_trans right.1 left.2⟩

theorem branch : packet.Holds witness := by
  refine ⟨?_,?_,?_⟩
  · change GeneralNominalState.Models (privateState registry context root p pBounds) witness
    unfold privateState
    rw [p_bindings,report_exact]
    apply (GeneralNominalState.extend_models ..).mpr
    constructor
    · apply (GeneralNominalAllocation.propagate_models ..).mpr
      refine ⟨witness_source,?_,?_⟩
      · intro first one last two same
        simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
        rcases one with rfl | rfl | rfl <;> rcases two with rfl | rfl | rfl
        all_goals cases same
        all_goals exact subtype_refl _
      · simp [GeneralNominalAllocation.merges,Declaration.inputNames,p,normalizeArgs,normalize,
          variablesArgs,Pattern.variables,GeneralNominalAllocation.occurrences,PresenceNormalForm.All]
    · intro atom member
      simp only [selfChecks,reportP,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact subtype_refl _
  · change ProjectionModels state (report context p pBounds) witness
    rw [report_exact]
    exact projection_models
  · change GeneralNominalMaterialization.Models state p _ (report context p pBounds)
      (generated registry context root p p_checked pBounds) witness
    rw [report_exact,schema_exact]
    simpa only [Packet.bindings,report_exact,GeneralNominalDemandMerging.pointSite] using material_models


private def chain : List Nat → Ty
  | [] => intValue
  | name :: rest => nominal name [.inl (chain rest)]
private def names (identity : Nat) : List Nat :=
  if identity ≤ 7 then
    match identity with
    | 0 | 3 => [0,0]
    | 1 | 4 => [0]
    | 6 => [1]
    | _ => []
  else [0]

private theorem witness_chain (identity : Nat) : (witness identity).1 = chain (names identity) := by
  unfold witness names
  split
  · rename_i small
    have possibilities : identity = 0 ∨ identity = 1 ∨ identity = 2 ∨ identity = 3 ∨
        identity = 4 ∨ identity = 5 ∨ identity = 6 ∨ identity = 7 := by omega
    rcases possibilities with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · rfl

private theorem int_not_nominal (name : Nat) (arguments : List Argument) :
    ¬ Subtype intValue (nominal name arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead name arguments.length) ⟨rfl,by simp⟩

private theorem chain_length (first last : List Nat) (equal : Equivalent (chain first) (chain last)) :
    first.length = last.length := by
  induction first generalizing last with
  | nil =>
    cases last with
    | nil => rfl
    | cons name rest => exact False.elim (int_not_nominal name _ equal.1)
  | cons name rest ih =>
    cases last with
    | nil => exact False.elim (int_not_nominal name _ equal.2)
    | cons other tail =>
      have invariant := (nominal_regular_invariant_exact _ _ _ _).mp equal.1
      have children := invariant.2.2 0 (.inl (chain rest)) (.inl (chain tail)) rfl rfl
      exact congrArg Nat.succ (ih tail children)

private theorem observation_decreases (first last name index : Nat) (actual : Ty)
    (observed : GeneralNominalProjections.Observes witness (.argument (.source first) name index) (.inl actual))
    (same : Equivalent actual (witness last).1) : (names last).length < (names first).length := by
  cases observed with
  | argument parent compared found =>
    cases parent
    rw [witness_chain first] at compared
    rw [witness_chain last] at same
    cases equation : names first with
    | nil =>
      rw [equation] at compared
      exact False.elim (int_not_nominal _ _ compared.1)
    | cons head rest =>
      rw [equation] at compared
      have invariant := (nominal_regular_invariant_exact _ _ _ _).mp compared.1
      have length := invariant.2.1
      have zero : index = 0 := by
        obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp found
        simp only [List.length_cons,List.length_nil] at length
        omega
      subst index
      have child := invariant.2.2 0 (.inl (chain rest)) (.inl actual) rfl found
      have equal := chain_length rest (names last)
        ⟨subtype_trans child.1 same.1,subtype_trans same.2 child.2⟩
      simp only [List.length_cons]
      omega

theorem no_feedback (identity : Nat) : ¬ GeneralNominalFeedbackK2.Cycle start.current identity := by
  have valid : Models start.current witness := (GeneralNominalSaturationState.initial_models ..).mpr witness_source
  have decreasing : ∀ first last, GeneralNominalFeedbackK2.Edge start.current first last →
      (names last).length < (names first).length := by
    intro first last edge
    rcases edge.2.2 with ⟨_,_,⟨kind,_,_,_⟩,_,_⟩ | argument
    · exact Fin.elim0 kind
    · obtain ⟨name,index,actual,seen,same⟩ := GeneralNominalFeedbackK2.argument_sound argument witness valid
      exact observation_decreases first last name index actual seen same
  have paths : ∀ first last, GeneralNominalFeedbackK2.Path start.current first last →
      (names last).length ≤ (names first).length := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreasing _ _ edge))
  rintro ⟨next,edge,path⟩
  have one := decreasing _ _ edge
  have two := paths _ _ path
  omega

theorem raw_acyclic (slot : Fin state.base.slots) : ¬ GeneralNominalCycleK2.Cycle state slot := by
  have decreasing : ∀ first last, GeneralNominalMixedRecurrence.Edge state first last →
      (names last.val).length < (names first.val).length := by
    intro first last edge
    rcases edge with ⟨kind,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
        GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument witness witness_source
      exact observation_decreases _ _ _ _ actual seen same
  have paths : ∀ first last, GeneralNominalMixedRecurrence.Path state first last →
      (names last.val).length ≤ (names first.val).length := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreasing _ _ edge))
  rintro ⟨next,edge,path⟩
  have smaller := decreasing _ _ edge
  have larger := paths _ _ path
  omega

theorem no_root : ¬ GeneralNominalFeedbackK2.RootK2 start.current root := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,_,cycle,_⟩)
  · exact raw_acyclic slot (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact no_feedback _ cycle

theorem no_candidate : ¬ GeneralNominalFeedbackK2.CandidateK2 registry start.current root := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact raw_acyclic visited.1 (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact no_feedback _ cycle


theorem located : arguments context root = some pBounds := by decide +kernel

theorem prepared : Prepared registry context root p p_checked := by
  refine ⟨metadata,initial_source.linked,GeneralNominalSourceFormation.initial_fresh context initial_source root.identity,
    pBounds,located,p_finished,?_,witness,branch⟩
  exact ⟨(by intro output member; cases member),(by rw [schema_exact])⟩

theorem ready : ¬ GeneralNominalState.RootPending state root.demand := by
  rintro ⟨index,unknown⟩
  apply unknown
  change GeneralNominalState.Known state
    (if index.val = 0 then (0,0) else if index.val = 1 then (3,3) else (6,6)).1
  split
  · exact ⟨0,rfl,Or.inr ⟨listDescriptor 1,rfl⟩⟩
  · split
    · exact ⟨3,rfl,Or.inr ⟨listDescriptor 4,rfl⟩⟩
    · exact ⟨6,rfl,Or.inr ⟨boxDescriptor,rfl⟩⟩

theorem survivor : Survivor registry context root p.id packet.children :=
  ⟨ready,p,by simp [registry],p_checked,rfl,rfl,pBounds,located,prepared,rfl⟩

theorem p_only (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (role : declaration.role = root.demand.role) : declaration = p := by
  simp only [registry,List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | cases role

theorem selected : GeneralNominalFeedbackK2.Local registry start.current root (.selected p.id packet.children) := by
  refine .selected ⟨ready,no_root,no_candidate,?_⟩ ⟨survivor,?_⟩
  · rintro (pending | ⟨_,legacy⟩)
    · obtain ⟨_,declaration,visible,certified,role,failed,missing⟩ := pending
      have same := p_only declaration visible role
      subst declaration
      exact missing prepared
    · rcases legacy with ⟨⟨_,_,_,slot,_,cycle⟩,_⟩ | ⟨⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩,_⟩
      · obtain ⟨⟨kind,_,_⟩,_⟩ := cycle
        exact Fin.elim0 kind
      · obtain ⟨⟨kind,_,_⟩,_⟩ := cycle
        exact Fin.elim0 kind
  · intro key kids found
    have copy := found
    obtain ⟨_,declaration,visible,certified,identity,role,_⟩ := found
    have same := p_only declaration visible role
    subst declaration
    subst key
    exact ⟨rfl,survivor_children_functional registry checked context root p.id kids packet.children copy survivor⟩

abbrev kidExtractA : Occurrence roles := GeneralNominalFeedbackSites.clauseChild packet extractA
  (p_checked.signature.2.2.2 extractA (by simp [p]))
abbrev kidW : Occurrence roles := GeneralNominalFeedbackSites.clauseChild packet childW
  (p_checked.signature.2.2.2 childW (by simp [p]))
abbrev kidExtractB : Occurrence roles := GeneralNominalFeedbackSites.clauseChild packet extractB
  (p_checked.signature.2.2.2 extractB (by simp [p]))
abbrev kidG : Occurrence roles := GeneralNominalFeedbackSites.clauseChild packet childG
  (p_checked.signature.2.2.2 childG (by simp [p]))
abbrev kidP : Occurrence roles := GeneralNominalFeedbackSites.clauseChild packet childP
  (p_checked.signature.2.2.2 childP (by simp [p]))

theorem children : packet.children = [kidExtractA,kidW,kidExtractB,kidG,kidP] := by
  unfold Packet.children GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children
  simp only [GeneralCanonicalChildOrder.canonicalEmit,sorted]
  simp [GeneralDeclarationDemands.emitAll,GeneralNominalFeedbackSites.clauseChild,
    GeneralNominalFeedbackSites.frame,packet,GeneralDictionaryEmissionPlans.occurrence,
    kidExtractA,kidW,kidExtractB,kidG,kidP]

theorem enabled : GeneralNominalFeedbackSteps.Installable registry start.current packet := by
  refine ⟨⟨rfl,rfl,by simp [start,GeneralNominalSupport.initial,GeneralNominalSaturationState.initial,packet],
    by simp [registry],rfl,located,prepared,GeneralNominalFeedbackK2.selected_legacy selected,?_,?_,?_,?_⟩,selected,?_⟩
  · intro prior member; cases member
  · intro other member same
    have equal := List.mem_singleton.mp member
    subst other
    exact .refl _
  · exact ⟨witness,(GeneralNominalSaturationState.initial_models ..).mpr witness_source,branch⟩
  · exact GeneralNominalJointCandidates.initial_joint registry context root p (by simp [registry]) p_checked rfl
      pBounds located prepared witness branch
  · intro other member same
    have equal := List.mem_singleton.mp member
    subst other
    exact .refl _

theorem source_guard : GeneralNominalSupportChoices.PacketGuard start packet [] := by
  have headZero : GeneralNominalSupport.ReadyAt start [] 0 :=
    GeneralNominalSupport.source_ready start 0 (.nominal 0 1) _ _
      (GeneralNominalSupport.Head.nominal (snapshot := state) 0 (listDescriptor 1) rfl)
      (GeneralNominalSupport.Head.nominal (snapshot := state) 0 (listDescriptor 1) rfl) []
  have headOne : GeneralNominalSupport.ReadyAt start [] 1 :=
    GeneralNominalSupport.source_ready start 1 (.nominal 0 1) _ _
      (GeneralNominalSupport.Head.nominal (snapshot := state) 1 (listDescriptor 2) rfl)
      (GeneralNominalSupport.Head.nominal (snapshot := state) 1 (listDescriptor 2) rfl) []
  have headThree : GeneralNominalSupport.ReadyAt start [] 3 :=
    GeneralNominalSupport.source_ready start 3 (.nominal 0 1) _ _
      (GeneralNominalSupport.Head.nominal (snapshot := state) 3 (listDescriptor 4) rfl)
      (GeneralNominalSupport.Head.nominal (snapshot := state) 3 (listDescriptor 4) rfl) []
  have headFour : GeneralNominalSupport.ReadyAt start [] 4 :=
    GeneralNominalSupport.source_ready start 4 (.nominal 0 1) _ _
      (GeneralNominalSupport.Head.nominal (snapshot := state) 4 (listDescriptor 5) rfl)
      (GeneralNominalSupport.Head.nominal (snapshot := state) 4 (listDescriptor 5) rfl) []
  have headSix : GeneralNominalSupport.ReadyAt start [] 6 :=
    GeneralNominalSupport.source_ready start 6 (.nominal 1 1) _ _
      (GeneralNominalSupport.Head.nominal (snapshot := state) 6 boxDescriptor rfl)
      (GeneralNominalSupport.Head.nominal (snapshot := state) 6 boxDescriptor rfl) []
  have roots : GeneralNominalSupport.Roots start [] root := by
    intro index
    change GeneralNominalSupport.ReadyAt start []
      (if index.val = 0 then (0,0) else if index.val = 1 then (3,3) else (6,6)).1
    split <;> try split
    all_goals first | exact headZero | exact headThree | exact headSix
  have inspection : GeneralNominalSupport.Inspection start [] p pBounds := by
    intro slot present
    have member : slot ∈ GeneralNominalSupport.readsMany state (GeneralNominalInspection.queries state interpretation p) pBounds := present
    rw [p_reads] at member
    rcases List.mem_cons.mp member with zero | rest
    · subst slot; exact headZero
    · rcases List.mem_cons.mp rest with one | rest
      · subst slot; exact headOne
      · rcases List.mem_cons.mp rest with three | rest
        · subst slot; exact headThree
        · have four := List.mem_singleton.mp rest
          subst slot; exact headFour

  refine ⟨⟨(by intro _ impossible; cases impossible),roots,inspection⟩,
    (by intro _ impossible; cases impossible),roots,?_⟩
  intro declaration visible role bounds found slot present
  have same := p_only declaration visible role
  subst declaration
  have equal := Option.some.inj (located.symm.trans found)
  subst bounds
  exact inspection slot present

noncomputable def afterP : GeneralNominalSupport.Tracked roles := GeneralNominalValueSteps.install start packet []

theorem first_step : GeneralNominalValueSteps.Step registry root start afterP := by
  apply GeneralNominalValueSteps.source_install start packet .root enabled ?_ source_guard
  intro done
  have bad := done.2 kidExtractA (by rw [children]; simp)
  cases bad

theorem first_formed : GeneralNominalValueSteps.SourceFormed registry root afterP :=
  .update (.initial context initial_source) first_step

theorem generated_children (child : Occurrence roles) (member : child ∈ packet.children) :
    Generated afterP.current root child := by
  apply Generated.child .root
  change (root,child) ∈ [] ++ packet.children.map (fun child => (packet.site.occurrence,child))
  exact List.mem_append_right _ (List.mem_map.mpr ⟨child,member,rfl⟩)


/-- Every compound emitted input is equated with the corresponding existing
list source by the installed packet, in every journal model. -/
theorem materialized_endpoint (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : packet.Holds assignment) (target binder : Nat) (names : binder = 0 ∨ binder = 1)
    (entryMember : inputUse target binder ∈ schema.variables)
    (test : (.source target,.nominal 0 1) ∈ schema.tests) :
    Equivalent (assignment target).1 (assignment (if binder = 0 then 1 else 4)).1 := by
  have original := (GeneralNominalRecursiveCandidates.branch_interval_sound registry context root p p_checked pBounds assignment valid).1
  have material := valid.2.2
  change GeneralNominalMaterialization.Models state p _ (report context p pBounds)
    (generated registry context root p p_checked pBounds) assignment at material
  rw [schema_exact] at material
  have entry := material.2.1 (inputUse target binder) entryMember
  have fit : ∀ a, Observes assignment (inputUse target binder).origin a →
      GeneralNominalCaptureMerges.Fits assignment (if binder = 0 then (2,2) else (5,5)) a := by
    intro a seen
    have fact := entry.2 a seen
    rcases names with rfl | rfl
    · change GeneralNominalCaptureMerges.Fits assignment
        ((GeneralNominalAllocation.capture state registry root.identity p.id packet.bindings).inputs 0) a at fact
      rw [packet_bindings] at fact
      exact fact
    · change GeneralNominalCaptureMerges.Fits assignment
        ((GeneralNominalAllocation.capture state registry root.identity p.id packet.bindings).inputs 1) a at fact
      rw [packet_bindings] at fact
      exact fact
  have targetTest : (Test.nominal 0 1).Holds (assignment target).1 :=
    (material.1 (.source target,.nominal 0 1) test).2 _ (.source target)
  rcases names with rfl | rfl
  · apply GeneralNominalMaterializedHeadRecovery.heads_equivalent assignment target 1 0 1 targetTest
    · obtain ⟨arguments,fits,equal⟩ := original.2.1 1 (listDescriptor 2) rfl
      exact ⟨arguments,GeneralNominalLinearMaterializationFacts.fitsAll_length base assignment _ _ fits,equal⟩
    · intro i
      have zero : i.val = 0 := by have bound := i.isLt; omega
      obtain ⟨a,ha⟩ := entry.1
      have bounds := nominal_argument_bounds state assignment original 1 (listDescriptor 2) rfl 0 (2,2) rfl
      obtain ⟨b,hb⟩ := bounds.1
      refine ⟨a,b,?_,?_,?_⟩
      · simpa only [zero,inputUse] using ha
      · have sourceOne : state.base.source (1 : Fin state.base.slots) = 1 := by decide +kernel
        simpa [zero,sourceOne] using hb
      · have one := fit a ha
        have two := bounds.2 b hb
        exact ⟨subtype_trans one.2 two.1,subtype_trans two.2 one.1⟩
  · apply GeneralNominalMaterializedHeadRecovery.heads_equivalent assignment target 4 0 1 targetTest
    · obtain ⟨arguments,fits,equal⟩ := original.2.1 4 (listDescriptor 5) rfl
      exact ⟨arguments,GeneralNominalLinearMaterializationFacts.fitsAll_length base assignment _ _ fits,equal⟩
    · intro i
      have zero : i.val = 0 := by have bound := i.isLt; omega
      obtain ⟨a,ha⟩ := entry.1
      have bounds := nominal_argument_bounds state assignment original 4 (listDescriptor 5) rfl 0 (5,5) rfl
      obtain ⟨b,hb⟩ := bounds.1
      refine ⟨a,b,?_,?_,?_⟩
      · simpa only [zero,inputUse] using ha
      · rw [zero]
        change Observes assignment (.nominal (.source (4 : Fin 8).val) 0 0) b at hb
        have four : (4 : Fin 8).val = 4 := by decide +kernel
        rw [four] at hb
        exact hb
      · have one := fit a ha
        have two := bounds.2 b hb
        exact ⟨subtype_trans one.2 two.1,subtype_trans two.2 one.1⟩

theorem endpoint_equal (target binder : Nat) (names : binder = 0 ∨ binder = 1)
    (entryMember : inputUse target binder ∈ schema.variables)
    (test : (.source target,.nominal 0 1) ∈ schema.tests) :
    GeneralNominalFeedbackK2.Equal afterP.current target (if binder = 0 then 1 else 4) := by
  intro assignment valid
  have packetValid := valid.2.1 packet (by simp [afterP,GeneralNominalValueSteps.install,
    GeneralNominalSupportSteps.install,GeneralNominalFeedbackSites.install])
  exact materialized_endpoint assignment packetValid target binder names entryMember test

theorem extractA_endpoints : GeneralNominalFeedbackK2.Equal afterP.current (argumentLo 10 0) 1 ∧
    GeneralNominalFeedbackK2.Equal afterP.current (argumentHi 10 0) 1 := by
  constructor
  all_goals apply endpoint_equal _ 0 (Or.inl rfl)
  all_goals simp [schema,inputUses,inputTests]

theorem w_endpoints : GeneralNominalFeedbackK2.Equal afterP.current (argumentLo 11 0) 1 ∧
    GeneralNominalFeedbackK2.Equal afterP.current (argumentHi 11 0) 1 ∧
    GeneralNominalFeedbackK2.Equal afterP.current (argumentLo 11 1) 4 ∧
    GeneralNominalFeedbackK2.Equal afterP.current (argumentHi 11 1) 4 := by
  refine ⟨?_,?_,?_,?_⟩
  · apply endpoint_equal _ 0 (Or.inl rfl) <;> simp [schema,inputUses,inputTests]
  · apply endpoint_equal _ 0 (Or.inl rfl) <;> simp [schema,inputUses,inputTests]
  · apply endpoint_equal _ 1 (Or.inr rfl) <;> simp [schema,inputUses,inputTests]
  · apply endpoint_equal _ 1 (Or.inr rfl) <;> simp [schema,inputUses,inputTests]

theorem extractB_endpoints : GeneralNominalFeedbackK2.Equal afterP.current (argumentLo 12 0) 4 ∧
    GeneralNominalFeedbackK2.Equal afterP.current (argumentHi 12 0) 4 := by
  constructor
  all_goals apply endpoint_equal _ 1 (Or.inr rfl)
  all_goals simp [schema,inputUses,inputTests]

theorem g_endpoints : GeneralNominalFeedbackK2.Equal afterP.current (argumentLo 13 0) 4 ∧
    GeneralNominalFeedbackK2.Equal afterP.current (argumentHi 13 0) 4 ∧
    GeneralNominalFeedbackK2.Equal afterP.current (argumentLo 13 1) 1 ∧
    GeneralNominalFeedbackK2.Equal afterP.current (argumentHi 13 1) 1 := by
  refine ⟨?_,?_,?_,?_⟩
  · apply endpoint_equal _ 1 (Or.inr rfl) <;> simp [schema,inputUses,inputTests]
  · apply endpoint_equal _ 1 (Or.inr rfl) <;> simp [schema,inputUses,inputTests]
  · apply endpoint_equal _ 0 (Or.inl rfl) <;> simp [schema,inputUses,inputTests]
  · apply endpoint_equal _ 0 (Or.inl rfl) <;> simp [schema,inputUses,inputTests]

theorem p_endpoints : GeneralNominalFeedbackK2.Equal afterP.current (argumentLo 14 0) 1 ∧
    GeneralNominalFeedbackK2.Equal afterP.current (argumentHi 14 0) 1 ∧
    GeneralNominalFeedbackK2.Equal afterP.current (argumentLo 14 1) 4 ∧
    GeneralNominalFeedbackK2.Equal afterP.current (argumentHi 14 1) 4 := by
  refine ⟨?_,?_,?_,?_⟩
  · apply endpoint_equal _ 0 (Or.inl rfl) <;> simp [schema,inputUses,inputTests]
  · apply endpoint_equal _ 0 (Or.inl rfl) <;> simp [schema,inputUses,inputTests]
  · apply endpoint_equal _ 1 (Or.inr rfl) <;> simp [schema,inputUses,inputTests]
  · apply endpoint_equal _ 1 (Or.inr rfl) <;> simp [schema,inputUses,inputTests]


/-- The finite separating assignment also excludes journal cycles after any
model-preserving observation change that retains this assignment. -/
theorem witness_feedback_acyclic (journal : GeneralNominalSaturationState.State roleDecls)
    (valid : Models journal witness)
    (noStructural : ∀ first last, ¬ GeneralNominalFeedbackK2.Structural journal first last)
    (identity : Nat) : ¬ GeneralNominalFeedbackK2.Cycle journal identity := by
  have decreasing : ∀ first last, GeneralNominalFeedbackK2.Edge journal first last →
      (names last).length < (names first).length := by
    intro first last edge
    rcases edge.2.2 with structural | argument
    · exact False.elim (noStructural first last structural)
    · obtain ⟨name,index,actual,seen,same⟩ := GeneralNominalFeedbackK2.argument_sound argument witness valid
      exact observation_decreases first last name index actual seen same
  have paths : ∀ first last, GeneralNominalFeedbackK2.Path journal first last →
      (names last).length ≤ (names first).length := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreasing _ _ edge))
  rintro ⟨next,edge,path⟩
  have one := decreasing _ _ edge
  have two := paths _ _ path
  omega

theorem witness_raw_acyclic (snapshot : GeneralNominalState.State)
    (valid : GeneralNominalState.Models snapshot witness)
    (noStructural : ∀ first last, ¬ GeneralSourceK2.Child snapshot.view first last)
    (slot : Fin snapshot.base.slots) : ¬ GeneralNominalCycleK2.Cycle snapshot slot := by
  have decreasing : ∀ first last, GeneralNominalMixedRecurrence.Edge snapshot first last →
      (names (snapshot.base.source last)).length < (names (snapshot.base.source first)).length := by
    intro first last edge
    rcases edge with structural | argument
    · exact False.elim (noStructural first last structural)
    · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
        GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument witness valid
      exact observation_decreases _ _ _ _ actual seen same
  have paths : ∀ first last, GeneralNominalMixedRecurrence.Path snapshot first last →
      (names (snapshot.base.source last)).length ≤ (names (snapshot.base.source first)).length := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreasing _ _ edge))
  rintro ⟨next,edge,path⟩
  have smaller := decreasing _ _ edge
  have larger := paths _ _ path
  omega

end Yulang.GeneralNominalProvenancePrefix
