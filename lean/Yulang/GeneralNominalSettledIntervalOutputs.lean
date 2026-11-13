import Yulang.GeneralNominalSettledIntervalSource

/-! Exact leaf materialization exposes a fresh interior value of a fixed
strict interval. This is a schema/model result, not an operational trace. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalSettledIntervalOutputs
open GeneralNominalSettledIntervalDeclarations GeneralNominalSettledIntervalSource
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open CommonNominalFullCarrier

abbrev leafRoot : Occurrence roles :=
  ⟨10,⟨1,fun index => if index.val = 0 then (1,1) else (3,5),
    [⟨0,2⟩,⟨1,7⟩,⟨2,8⟩],by
      intro output present
      simp only [List.mem_cons,List.not_mem_nil,or_false] at present
      rcases present with rfl | rfl | rfl <;> exact ⟨none,rfl⟩⟩⟩
abbrev bounds : List (GeneralNominalInspection.Bounds source) := [(1,1),(3,5)]
abbrev packet : Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite leafRoot,w,w_checked,bounds⟩

abbrev leafReport : Report source where
  captures := [⟨0,(2,2),none⟩,⟨1,(3,5),none⟩]
  inspected := [(1,1)]
  checked := [(1,1),(3,5),(1,1),(2,2),(3,5)]

theorem queries : GeneralNominalInspection.queries source interpretation w =
    [.node (.variant 0) [.variables [0]],.variables [1]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,w,tick,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,GeneralCandidateInspection.plainNames]

theorem report_exact : GeneralNominalPacketSupport.report packet = leafReport := by
  unfold GeneralNominalPacketSupport.report GeneralNominalRecursiveCandidates.report
  rw [queries]
  simp [inspectMany,inspect,Report.visit,Report.append,bounds,source,view,views,leafReport]
  repeat first
    | rw [inspectMany.eq_def]
    | rw [inspect.eq_def]
    | simp [Report.visit,Report.append,leafReport,GeneralNormalizedObservation.Shape.arity]

theorem packet_bindings : packet.bindings = [(0,(2,2)),(1,(3,5))] := by
  change bindings source (GeneralNominalPacketSupport.report packet) = _
  rw [report_exact]
  rfl

abbrev capture : GeneralDeclarationDemands.Capture := ⟨fun name => if name = 0 then (2,2) else (3,5),fun _ => 0⟩
abbrev body : Schema :=
  ⟨[⟨0,.source 2,.actual⟩,⟨1,.structural (.source 7) (.variant 0) 0,.actual⟩,
    ⟨1,.source 8,.actual⟩],[(.source 7,.structural (.variant 0))],false⟩

theorem schema_exact : GeneralNominalPacketSupport.namedSchema packet = body := by
  unfold GeneralNominalPacketSupport.namedSchema GeneralNominalRecursiveCandidates.generated
  unfold GeneralNominalMaterialization.requests
  have sorted : GeneralCanonicalChildOrder.canonicalDeclaration w = w := by
    simp only [GeneralCanonicalChildOrder.canonicalDeclaration,
      GeneralCanonicalChildOrder.canonicalRequirements,w,List.mergeSort_nil]
  unfold GeneralCanonicalChildOrder.canonicalEmit
  simp only [sorted]
  simp [GeneralNominalMaterialization.rootRequests,GeneralCanonicalChildOrder.canonicalEmit,
    GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
    GeneralDeclarationDemands.emitAll,GeneralNominalMaterialization.generated,
    GeneralNominalInspection.translate,GeneralDeclarationPatterns.normalize,
    schema,schemas,Schema.append,packet,leafRoot,w,tick,body,interpretation,
    GeneralNominalDemandMerging.pointSite,List.mergeSort_nil,GeneralCandidateInspection.plainNames]

theorem input_not_output : (0 : Nat) ∉ w.outputNames ∧ (1 : Nat) ∉ w.outputNames := by simp [Declaration.outputNames,w]

theorem actual_capture_inputs (name : Nat) (member : name = 0 ∨ name = 1) :
    (GeneralNominalPacketSupport.capture packet).inputs name = capture.inputs name := by
  rcases member with rfl | rfl
  all_goals
    unfold GeneralNominalPacketSupport.capture
    rw [packet_bindings]
    rfl

private theorem payload_seen (assignment : GeneralNominalCommonBridge.Assignment) (identity : Nat) (value : Ty)
    (equal : (assignment identity).1 = V value) :
    Observes assignment (.structural (.source identity) (.variant 0) 0) value := by
  apply Observes.structural (values := [value]) (.source identity) rfl ?_ rfl
  rw [equal]
  exact ⟨subtype_refl _,subtype_refl _⟩

private theorem payload_unique (assignment : GeneralNominalCommonBridge.Assignment) (identity : Nat) (value actual : Ty)
    (equal : (assignment identity).1 = V value)
    (seen : Observes assignment (.structural (.source identity) (.variant 0) 0) actual) : Equivalent actual value := by
  cases seen with
  | structural seen length same found =>
    cases seen
    rename_i values
    cases values with
    | nil => cases found
    | cons head rest =>
      have empty : rest = [] := by cases rest <;> simp_all [GeneralNormalizedObservation.Shape.arity]
      subst rest
      cases Option.some.inj found
      rw [equal] at same
      exact ⟨(common_variant_iff 0 _ _).mp same.2,(common_variant_iff 0 _ _).mp same.1⟩

theorem interval_contains (value : Common.Ty) :
    Subtype (V .bottom) (V (CommonNominalFullModelMap.value value)) ∧
    Subtype (V (CommonNominalFullModelMap.value value)) (V .top) :=
  ⟨(CommonNominalFullModelMap.subtype_exact (Common.variant 0 .bottom) (Common.variant 0 value)).mpr
      ((Common.common_variant_iff 0 _ _).mpr (CommonBoundCoalescing.bottom_le _)),
    (CommonNominalFullModelMap.subtype_exact (Common.variant 0 value) (Common.variant 0 .top)).mpr
      ((Common.common_variant_iff 0 _ _).mpr (CommonBoundCoalescing.le_top _))⟩

abbrev family (a : Ty) (value : Common.Ty) :=
  GeneralNominalSettledIntervalSource.model a (V (V (CommonNominalFullModelMap.value value)))
    (V (CommonNominalFullModelMap.value value))

/-- Both unnamed intervals are fixed as value varies; the two actual-mode
uses of b share only the new tail/output within this one schema. -/
theorem materialized_family (a : Ty) (value : Common.Ty) :
    GeneralNominalMaterialization.Models source w capture leafReport body (family a value) := by
  let u := V (CommonNominalFullModelMap.value value)
  have observed := payload_seen (family a value) 7 u rfl
  have unique := payload_unique (family a value) 7 u
  have fitted := interval_contains value
  refine ⟨?_,?_,?_,?_⟩
  · intro test member
    cases List.mem_singleton.mp member
    refine ⟨⟨_,.source 7⟩,?_⟩
    intro actual seen
    cases seen
    exact ⟨[u],rfl,subtype_refl _,subtype_refl _⟩
  · intro entry member
    simp only [body,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · refine ⟨⟨_,.source 2⟩,?_⟩
      intro actual seen; cases seen
      exact ⟨subtype_refl _,subtype_refl _⟩
    · refine ⟨⟨u,observed⟩,?_⟩
      intro actual seen
      have same := unique actual rfl seen
      exact ⟨subtype_trans fitted.1 same.2,subtype_trans same.1 fitted.2⟩
    · refine ⟨⟨_,.source 8⟩,?_⟩
      intro actual seen; cases seen
      exact fitted
  · intro first one last two same _ _ x y hx hy
    simp only [body,List.mem_cons,List.not_mem_nil,or_false] at one two
    rcases one with rfl | rfl | rfl <;> rcases two with rfl | rfl | rfl
    all_goals try (cases same)
    all_goals try (cases hx; cases hy; exact ⟨subtype_refl _,subtype_refl _⟩)
    all_goals first
      | (cases hy; exact unique x rfl hx)
      | (cases hx; exact ⟨(unique y rfl hy).2,(unique y rfl hy).1⟩)
      | exact ⟨subtype_trans (unique x rfl hx).1 (unique y rfl hy).2,
          subtype_trans (unique y rfl hy).1 (unique x rfl hx).2⟩
  · intro entry _ captured present _ _ origin recorded
    simp only [leafReport,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl <;> cases recorded

theorem packet_outputs (a : Ty) (value : Common.Ty) :
    GeneralNominalPacketSupport.Outputs packet (family a value) := by
  change GeneralNominalMaterialization.Models source w (GeneralNominalPacketSupport.capture packet)
    (GeneralNominalPacketSupport.report packet) (GeneralNominalPacketSupport.namedSchema packet) _
  rw [report_exact,schema_exact]
  have given := materialized_family a value
  refine ⟨given.1,?_,given.2.2⟩
  intro entry member
  have holds := given.2.1 entry member
  refine ⟨holds.1,?_⟩
  intro actual seen
  have names : entry.name = 0 ∨ entry.name = 1 := by
    simp only [body,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> simp
  simpa only [VariableHolds,Declaration.outputNames,w,List.map_nil,List.not_mem_nil,ite_false,
    actual_capture_inputs entry.name names] using holds.2 actual seen

theorem same_input_endpoints (a : Ty) (first last : Common.Ty) (index : Fin 2) :
    (family a first (leafRoot.demand.arguments index).1).1 = (family a last (leafRoot.demand.arguments index).1).1 ∧
    (family a first (leafRoot.demand.arguments index).2).1 = (family a last (leafRoot.demand.arguments index).2).1 := by
  have args : leafRoot.demand.arguments index =
      (if index.val = 0 then (1,1) else (3,5)) := rfl
  rw [args]
  by_cases zero : index.val = 0
  all_goals simp only [zero,ite_eq_left,ite_eq_right]
  all_goals exact ⟨rfl,rfl⟩

end Yulang.GeneralNominalSettledIntervalOutputs
