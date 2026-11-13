import Yulang.GeneralNominalProvenanceDeclarations
import Yulang.GeneralNominalDownstreamSteps
import Yulang.GeneralNominalOutputGrowthModels

/-! Source data and exact inspection reports for the six-role provenance
stress test. Three independent unknown leaves remain in the shared source
state. No later installation or refresh is asserted by this module. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalProvenanceSource
open GeneralNominalProvenanceDeclarations
open GeneralDeclarationPatterns GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveInspection CommonNominalFullCarrier

abbrev base := GeneralNominalOutputGrowthModels.base 6
abbrev view := GeneralNominalOutputGrowthModels.view 6
abbrev listDescriptor (child : Fin 8) : GeneralNominalState.Descriptor 8 :=
  ⟨0,⟨[.type],0⟩,[.type (child,child)],rfl⟩
abbrev boxDescriptor : GeneralNominalState.Descriptor 8 :=
  ⟨1,⟨[.type],1⟩,[.type (7,7)],rfl⟩
abbrev entries (slot : Fin 8) : Option (GeneralNominalState.Descriptor 8) :=
  if slot = 0 then some (listDescriptor 1)
  else if slot = 1 then some (listDescriptor 2)
  else if slot = 3 then some (listDescriptor 4)
  else if slot = 4 then some (listDescriptor 5)
  else if slot = 6 then some boxDescriptor else none

abbrev state : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := entries
  catalogue := by
    intro slot descriptor recorded
    unfold entries at recorded
    split at recorded
    · cases Option.some.inj recorded; rfl
    · split at recorded
      · cases Option.some.inj recorded; rfl
      · split at recorded
        · cases Option.some.inj recorded; rfl
        · split at recorded
          · cases Option.some.inj recorded; rfl
          · split at recorded
            · cases Option.some.inj recorded; rfl
            · cases recorded
  bodies_opaque := by intro _ _ _; rfl
  seed := 7

abbrev interpretation : GeneralNominalInspection.Interpretation where
  primitives := fun name => if name = 2 then some (.scalar .int) else none
  invariantNominal := fun name => name == 0 || name == 1
  disjoint := by
    intro name yes
    simp only [Bool.or_eq_true,beq_iff_eq] at yes
    rcases yes with rfl | rfl <;> rfl

abbrev context : GeneralNominalCandidates.Context := ⟨state,interpretation⟩
abbrev root : Occurrence roles :=
  ⟨8,⟨0,fun index => if index.val = 0 then (0,0) else if index.val = 1 then (3,3) else (6,6),
    [],by intro _ impossible; cases impossible⟩⟩
abbrev start : GeneralNominalSupport.Tracked roles := GeneralNominalSupport.initial context root

/-- Every choice of the three unknown values gives a source model. -/
def model (a b u : Ty) : GeneralNominalCommonBridge.Assignment := fun source =>
  (match source with
    | 0 => nominal 0 [.inl (nominal 0 [.inl a])]
    | 1 => nominal 0 [.inl a]
    | 2 => a
    | 3 => nominal 0 [.inl (nominal 0 [.inl b])]
    | 4 => nominal 0 [.inl b]
    | 5 => b
    | 6 => nominal 1 [.inl u]
    | 7 => u
    | _ => .base .int,
    Common.rowEmpty)

theorem source_models (a b u : Ty) : GeneralNominalState.Models state (model a b u) := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · intro _ _ impossible; cases impossible
  · intro _ member; cases member
  · intro slot descriptor recorded
    change entries slot = some descriptor at recorded
    unfold entries at recorded
    split at recorded
    · rename_i same; subst slot
      cases Option.some.inj recorded
      exact (GeneralNominalState.denotes_singleton_exact base _ 0 1 (listDescriptor 1) rfl).mpr
        ⟨subtype_refl _,subtype_refl _⟩
    · split at recorded
      · rename_i same; subst slot
        cases Option.some.inj recorded
        exact (GeneralNominalState.denotes_singleton_exact base _ 1 2 (listDescriptor 2) rfl).mpr
          ⟨subtype_refl _,subtype_refl _⟩
      · split at recorded
        · rename_i same; subst slot
          cases Option.some.inj recorded
          exact (GeneralNominalState.denotes_singleton_exact base _ 3 4 (listDescriptor 4) rfl).mpr
            ⟨subtype_refl _,subtype_refl _⟩
        · split at recorded
          · rename_i same; subst slot
            cases Option.some.inj recorded
            exact (GeneralNominalState.denotes_singleton_exact base _ 4 5 (listDescriptor 5) rfl).mpr
              ⟨subtype_refl _,subtype_refl _⟩
          · split at recorded
            · rename_i same; subst slot
              cases Option.some.inj recorded
              exact (GeneralNominalState.denotes_singleton_exact base _ 6 7 boxDescriptor rfl).mpr
                ⟨subtype_refl _,subtype_refl _⟩
            · cases recorded

theorem metadata : GeneralNominalRecursiveCandidates.Metadata registry context := by
  refine ⟨rfl,?_⟩
  intro name primitive found
  change (if name = 2 then some (.scalar .int) else none) = some primitive at found
  split at found
  · rename_i same
    subst name
    cases Option.some.inj found
    exact ⟨⟨[],2⟩,rfl,rfl⟩
  · cases found

theorem source_member (slot : Fin 8) : slot.val ∈ GeneralNominalState.sources state :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩)))

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root := by
  refine ⟨rfl,metadata,?_,?_,?_,rfl⟩
  · constructor
    · intro index
      change (if index.val = 0 then (0,0) else if index.val = 1 then (3,3) else (6,6)).1 ∈ _ ∧
        (if index.val = 0 then (0,0) else if index.val = 1 then (3,3) else (6,6)).2 ∈ _
      by_cases zero : index.val = 0
      · simp only [zero,ite_true]
        exact ⟨source_member 0,source_member 0⟩
      · by_cases one : index.val = 1
        · simp only [zero,one,ite_true,ite_false]
          exact ⟨source_member 3,source_member 3⟩
        · simp only [zero,one,ite_false]
          exact ⟨source_member 6,source_member 6⟩
    · intro output member; cases member
  · intro assignment valid index
    change Subtype (assignment (if index.val = 0 then (0,0) else if index.val = 1 then (3,3) else (6,6)).1).1
      (assignment (if index.val = 0 then (0,0) else if index.val = 1 then (3,3) else (6,6)).2).1
    split <;> try split
    all_goals exact subtype_refl _
  · intro identity member
    change identity ≤ 7
    simp only [GeneralNominalState.sources,state,List.mem_append,List.not_mem_nil,List.flatMap_nil,or_false] at member
    rcases member with first | last
    all_goals obtain ⟨slot,equal⟩ := List.mem_ofFn.mp ‹_›
    all_goals have bound := slot.isLt
    all_goals change slot.val < 8 at bound
    all_goals change slot.val = identity at equal
    all_goals omega

theorem formed : GeneralNominalDownstreamSteps.SourceFormed registry root start := .initial context initial_source

theorem initial_models (a b u : Ty) : Models start.current (model a b u) :=
  (GeneralNominalSaturationState.initial_models context root _).mpr (source_models a b u)

theorem leaves_unknown : ¬ GeneralNominalState.Known state 2 ∧
    ¬ GeneralNominalState.Known state 5 ∧ ¬ GeneralNominalState.Known state 7 := by
  constructor
  · rintro ⟨slot,equal,known⟩
    have same : slot = (2 : Fin 8) := Fin.ext equal
    subst slot
    rcases known with impossible | ⟨descriptor,recorded⟩
    · exact impossible rfl
    · cases recorded
  · constructor
    · rintro ⟨slot,equal,known⟩
      have same : slot = (5 : Fin 8) := Fin.ext equal
      subst slot
      rcases known with impossible | ⟨descriptor,recorded⟩
      · exact impossible rfl
      · cases recorded
    · rintro ⟨slot,equal,known⟩
      have same : slot = (7 : Fin 8) := Fin.ext equal
      subst slot
      rcases known with impossible | ⟨descriptor,recorded⟩
      · exact impossible rfl
      · cases recorded

abbrev pBounds : List (GeneralNominalInspection.Bounds state) := [(0,0),(3,3),(6,6)]
abbrev wBounds : List (GeneralNominalInspection.Bounds state) := [(1,1),(4,4),(6,6)]
abbrev gBounds : List (GeneralNominalInspection.Bounds state) := [(4,4),(1,1),(6,6)]
abbrev cBounds : List (GeneralNominalInspection.Bounds state) := [(4,4),(6,6)]
abbrev dBounds : List (GeneralNominalInspection.Bounds state) := [(1,1),(6,6)]

theorem p_queries : GeneralNominalInspection.queries state interpretation p =
    [.nominal 0 [.nominal 0 [.variables [0]]],.nominal 0 [.nominal 0 [.variables [1]]],.variables [2]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation,constructors,GeneralDeclarationExamples.constructors]

theorem w_queries : GeneralNominalInspection.queries state interpretation w =
    [.nominal 0 [.variables [0]],.variables [1],.variables [2]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation,constructors,GeneralDeclarationExamples.constructors]

theorem g_queries : GeneralNominalInspection.queries state interpretation g =
    [.nominal 0 [.variables [0]],.variables [1],.variables [2]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation,constructors,GeneralDeclarationExamples.constructors]

theorem c_queries : GeneralNominalInspection.queries state interpretation c =
    [.nominal 0 [.variables [0]],.nominal 1 [.scalar .int]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation,constructors,GeneralDeclarationExamples.constructors]

theorem d_queries : GeneralNominalInspection.queries state interpretation d =
    [.nominal 0 [.variables [0]],.nominal 1 [.scalar .int]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation,constructors,GeneralDeclarationExamples.constructors]

theorem p_reads : GeneralNominalSupport.readsMany state
    (GeneralNominalInspection.queries state interpretation p) pBounds = [0,1,3,4] := by
  rw [p_queries]
  simp [GeneralNominalSupport.readsMany.eq_1,GeneralNominalSupport.readsMany.eq_2,GeneralNominalSupport.reads.eq_1,GeneralNominalSupport.reads.eq_3,GeneralNominalSupport.reads.eq_5,pBounds,state,entries,
    GeneralNominalRecursiveInspection.typeArguments,listDescriptor,boxDescriptor]
  repeat first
    | rw [GeneralNominalSupport.readsMany.eq_def]
    | rw [GeneralNominalSupport.reads.eq_def]
    | simp [state,entries,typeArguments,listDescriptor,boxDescriptor]

theorem w_reads : GeneralNominalSupport.readsMany state
    (GeneralNominalInspection.queries state interpretation w) wBounds = [1] := by
  rw [w_queries]
  simp [GeneralNominalSupport.readsMany.eq_1,GeneralNominalSupport.readsMany.eq_2,GeneralNominalSupport.reads.eq_1,GeneralNominalSupport.reads.eq_3,GeneralNominalSupport.reads.eq_5,wBounds,state,entries,
    GeneralNominalRecursiveInspection.typeArguments,listDescriptor,boxDescriptor]
  repeat first
    | rw [GeneralNominalSupport.readsMany.eq_def]
    | rw [GeneralNominalSupport.reads.eq_def]
    | simp [state,entries,typeArguments,listDescriptor,boxDescriptor]

theorem g_reads : GeneralNominalSupport.readsMany state
    (GeneralNominalInspection.queries state interpretation g) gBounds = [4] := by
  rw [g_queries]
  simp [GeneralNominalSupport.readsMany.eq_1,GeneralNominalSupport.readsMany.eq_2,GeneralNominalSupport.reads.eq_1,GeneralNominalSupport.reads.eq_3,GeneralNominalSupport.reads.eq_5,gBounds,state,entries,
    GeneralNominalRecursiveInspection.typeArguments,listDescriptor,boxDescriptor]
  repeat first
    | rw [GeneralNominalSupport.readsMany.eq_def]
    | rw [GeneralNominalSupport.reads.eq_def]
    | simp [state,entries,typeArguments,listDescriptor,boxDescriptor]

theorem c_reads : GeneralNominalSupport.readsMany state
    (GeneralNominalInspection.queries state interpretation c) cBounds = [4,6,7] := by
  rw [c_queries]
  simp [GeneralNominalSupport.readsMany.eq_1,GeneralNominalSupport.readsMany.eq_2,GeneralNominalSupport.reads.eq_1,GeneralNominalSupport.reads.eq_3,GeneralNominalSupport.reads.eq_5,cBounds,state,entries,
    GeneralNominalRecursiveInspection.typeArguments,listDescriptor,boxDescriptor]
  repeat first
    | rw [GeneralNominalSupport.readsMany.eq_def]
    | rw [GeneralNominalSupport.reads.eq_def]
    | simp [state,entries,typeArguments,listDescriptor,boxDescriptor]

theorem d_reads : GeneralNominalSupport.readsMany state
    (GeneralNominalInspection.queries state interpretation d) dBounds = [1,6,7] := by
  rw [d_queries]
  simp [GeneralNominalSupport.readsMany.eq_1,GeneralNominalSupport.readsMany.eq_2,GeneralNominalSupport.reads.eq_1,GeneralNominalSupport.reads.eq_3,GeneralNominalSupport.reads.eq_5,dBounds,state,entries,
    GeneralNominalRecursiveInspection.typeArguments,listDescriptor,boxDescriptor]
  repeat first
    | rw [GeneralNominalSupport.readsMany.eq_def]
    | rw [GeneralNominalSupport.reads.eq_def]
    | simp [state,entries,typeArguments,listDescriptor,boxDescriptor]

theorem p_finished : Finished (GeneralNominalRecursiveCandidates.report context p pBounds) := by
  unfold GeneralNominalRecursiveCandidates.report
  rw [p_queries]
  simp [Finished,inspectMany.eq_1,inspectMany.eq_2,inspect.eq_1,inspect.eq_3,inspect.eq_5,Report.visit,Report.append,typeArguments,pBounds,context,state,entries,listDescriptor,boxDescriptor]
  repeat first
    | rw [inspectMany.eq_def]
    | rw [inspect.eq_def]
    | simp [Report.visit,Report.append,typeArguments,block,context,state,entries,listDescriptor,boxDescriptor,bindings]
theorem w_finished : Finished (GeneralNominalRecursiveCandidates.report context w wBounds) := by
  unfold GeneralNominalRecursiveCandidates.report
  rw [w_queries]
  simp [Finished,inspectMany.eq_1,inspectMany.eq_2,inspect.eq_1,inspect.eq_3,inspect.eq_5,Report.visit,Report.append,typeArguments,wBounds,context,state,entries,listDescriptor,boxDescriptor]
  repeat first
    | rw [inspectMany.eq_def]
    | rw [inspect.eq_def]
    | simp [Report.visit,Report.append,typeArguments,block,context,state,entries,listDescriptor,boxDescriptor,bindings]
theorem g_finished : Finished (GeneralNominalRecursiveCandidates.report context g gBounds) := by
  unfold GeneralNominalRecursiveCandidates.report
  rw [g_queries]
  simp [Finished,inspectMany.eq_1,inspectMany.eq_2,inspect.eq_1,inspect.eq_3,inspect.eq_5,Report.visit,Report.append,typeArguments,gBounds,context,state,entries,listDescriptor,boxDescriptor]
  repeat first
    | rw [inspectMany.eq_def]
    | rw [inspect.eq_def]
    | simp [Report.visit,Report.append,typeArguments,block,context,state,entries,listDescriptor,boxDescriptor,bindings]
theorem c_blocked : (GeneralNominalRecursiveCandidates.report context c cBounds).blocked = [(7,7)] := by
  unfold GeneralNominalRecursiveCandidates.report
  rw [c_queries]
  simp [bindings,inspectMany.eq_1,inspectMany.eq_2,inspect.eq_1,inspect.eq_3,inspect.eq_5,Report.visit,Report.append,typeArguments,block,cBounds,context,state,entries,listDescriptor,boxDescriptor]
  repeat first
    | rw [inspectMany.eq_def]
    | rw [inspect.eq_def]
    | simp [Report.visit,Report.append,typeArguments,block,context,state,entries,listDescriptor,boxDescriptor,bindings]
theorem d_blocked : (GeneralNominalRecursiveCandidates.report context d dBounds).blocked = [(7,7)] := by
  unfold GeneralNominalRecursiveCandidates.report
  rw [d_queries]
  simp [bindings,inspectMany.eq_1,inspectMany.eq_2,inspect.eq_1,inspect.eq_3,inspect.eq_5,Report.visit,Report.append,typeArguments,block,dBounds,context,state,entries,listDescriptor,boxDescriptor]
  repeat first
    | rw [inspectMany.eq_def]
    | rw [inspect.eq_def]
    | simp [Report.visit,Report.append,typeArguments,block,context,state,entries,listDescriptor,boxDescriptor,bindings]

theorem p_bindings : bindings state (GeneralNominalRecursiveCandidates.report context p pBounds) =
    [(0,(2,2)),(1,(5,5)),(2,(6,6))] := by
  unfold GeneralNominalRecursiveCandidates.report
  rw [p_queries]
  simp [bindings,inspectMany.eq_1,inspectMany.eq_2,inspect.eq_1,inspect.eq_3,inspect.eq_5,Report.visit,Report.append,typeArguments,block,pBounds,context,state,entries,listDescriptor,boxDescriptor]
  repeat first
    | rw [inspectMany.eq_def]
    | rw [inspect.eq_def]
    | simp [Report.visit,Report.append,typeArguments,block,context,state,entries,listDescriptor,boxDescriptor,bindings]
  all_goals decide +kernel

theorem w_bindings : bindings state (GeneralNominalRecursiveCandidates.report context w wBounds) =
    [(0,(2,2)),(1,(4,4)),(2,(6,6))] := by
  unfold GeneralNominalRecursiveCandidates.report
  rw [w_queries]
  simp [bindings,inspectMany.eq_1,inspectMany.eq_2,inspect.eq_1,inspect.eq_3,inspect.eq_5,Report.visit,Report.append,typeArguments,block,wBounds,context,state,entries,listDescriptor,boxDescriptor]
  repeat first
    | rw [inspectMany.eq_def]
    | rw [inspect.eq_def]
    | simp [Report.visit,Report.append,typeArguments,block,context,state,entries,listDescriptor,boxDescriptor,bindings]
  all_goals decide +kernel

theorem g_bindings : bindings state (GeneralNominalRecursiveCandidates.report context g gBounds) =
    [(0,(5,5)),(1,(1,1)),(2,(6,6))] := by
  unfold GeneralNominalRecursiveCandidates.report
  rw [g_queries]
  simp [bindings,inspectMany.eq_1,inspectMany.eq_2,inspect.eq_1,inspect.eq_3,inspect.eq_5,Report.visit,Report.append,typeArguments,block,gBounds,context,state,entries,listDescriptor,boxDescriptor]
  repeat first
    | rw [inspectMany.eq_def]
    | rw [inspect.eq_def]
    | simp [Report.visit,Report.append,typeArguments,block,context,state,entries,listDescriptor,boxDescriptor,bindings]
  all_goals decide +kernel

/-- A standalone source invocation of W with the named target A. It is
separate from the not-yet-constructed P transition prefix. -/
abbrev wRoot : Occurrence roles :=
  ⟨9,⟨1,fun index => if index.val = 0 then (1,1) else if index.val = 1 then (4,4) else (6,6),
    [⟨0,2⟩],by intro output member; have same := List.mem_singleton.mp member; subst output; exact ⟨none,rfl⟩⟩⟩
abbrev wStart : GeneralNominalSupport.Tracked roles := GeneralNominalSupport.initial context wRoot
abbrev wPacket : Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite wRoot,w,w_checked,wBounds⟩

theorem w_initial_source : GeneralNominalSourceFormation.InitialSource registry context wRoot := by
  refine ⟨rfl,metadata,?_,?_,initial_source.below_seed,rfl⟩
  · constructor
    · intro index
      change (if index.val = 0 then (1,1) else if index.val = 1 then (4,4) else (6,6)).1 ∈ _ ∧
        (if index.val = 0 then (1,1) else if index.val = 1 then (4,4) else (6,6)).2 ∈ _
      by_cases zero : index.val = 0
      · simp only [zero,ite_true]; exact ⟨source_member 1,source_member 1⟩
      · by_cases one : index.val = 1
        · simp only [zero,one,ite_true,ite_false]; exact ⟨source_member 4,source_member 4⟩
        · simp only [zero,one,ite_false]; exact ⟨source_member 6,source_member 6⟩
    · intro output member
      have same := List.mem_singleton.mp member; subst output
      exact source_member 2
  · intro assignment valid index
    change Subtype (assignment (if index.val = 0 then (1,1) else if index.val = 1 then (4,4) else (6,6)).1).1
      (assignment (if index.val = 0 then (1,1) else if index.val = 1 then (4,4) else (6,6)).2).1
    split <;> try split
    all_goals exact subtype_refl _

theorem w_located : GeneralNominalRecursiveCandidates.arguments context wRoot = some wBounds := by decide +kernel

theorem w_source_guard : GeneralNominalSupportChoices.PacketGuard wStart wPacket [] := by
  have headOne : GeneralNominalSupport.ReadyAt wStart [] 1 :=
    GeneralNominalSupport.source_ready wStart 1 (.nominal 0 1) _ _
      (GeneralNominalSupport.Head.nominal (snapshot := state) 1 (listDescriptor 2) rfl)
      (GeneralNominalSupport.Head.nominal (snapshot := state) 1 (listDescriptor 2) rfl) []
  have headFour : GeneralNominalSupport.ReadyAt wStart [] 4 :=
    GeneralNominalSupport.source_ready wStart 4 (.nominal 0 1) _ _
      (GeneralNominalSupport.Head.nominal (snapshot := state) 4 (listDescriptor 5) rfl)
      (GeneralNominalSupport.Head.nominal (snapshot := state) 4 (listDescriptor 5) rfl) []
  have headSix : GeneralNominalSupport.ReadyAt wStart [] 6 :=
    GeneralNominalSupport.source_ready wStart 6 (.nominal 1 1) _ _
      (GeneralNominalSupport.Head.nominal (snapshot := state) 6 boxDescriptor rfl)
      (GeneralNominalSupport.Head.nominal (snapshot := state) 6 boxDescriptor rfl) []
  have roots : GeneralNominalSupport.Roots wStart [] wRoot := by
    intro index
    change GeneralNominalSupport.ReadyAt wStart []
      (if index.val = 0 then (1,1) else if index.val = 1 then (4,4) else (6,6)).1
    split <;> try split
    all_goals first | exact headOne | exact headFour | exact headSix
  have inspection : GeneralNominalSupport.Inspection wStart [] w wBounds := by
    intro slot present
    have member : slot ∈ GeneralNominalSupport.readsMany state (GeneralNominalInspection.queries state interpretation w) wBounds := present
    rw [w_reads] at member
    have same := List.mem_singleton.mp member; subst slot
    exact headOne
  refine ⟨⟨(by intro _ impossible; cases impossible),roots,inspection⟩,
    (by intro _ impossible; cases impossible),roots,?_⟩
  intro declaration visible role bounds located slot present
  simp only [registry,List.mem_cons,List.not_mem_nil,or_false] at visible
  have equal : declaration = w := by
    rcases visible with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | cases role
  subst declaration
  have same : bounds = wBounds := Option.some.inj (located.symm.trans w_located)
  subst bounds
  exact inspection slot present

end Yulang.GeneralNominalProvenanceSource
