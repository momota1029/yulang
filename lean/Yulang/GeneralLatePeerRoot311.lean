import Yulang.GeneralLatePeerSource311
import Yulang.GeneralNominalNamedArgumentReadback

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralLatePeerRoot311
open GeneralLatePeerSource311
open GeneralGeneratedNestedSource299 (snapshot context model listDescriptor)
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalExamples (interpretation)
open GeneralNominalCenters
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedFrame231 (binder capture childSite children)
open GeneralNominalVersionedPlans231
open GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

theorem parentCode_checked : DeclarationChecked constructors roles parentCode :=
  GeneralNominalCenteredHeadAllocEncoding.declaration_checked parent_checked

abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨compiled,context,GeneralNominalDemandMerging.pointSite root,parentCode,parentCode_checked,[(0,0),(1,1)]⟩
abbrev plan : Plan roles := ⟨packet,rootSite snapshot.seed root,rfl⟩
abbrev leftSig : leftCode.Signature roles := parentCode_checked.signature.2.2.2 _ List.mem_cons_self
abbrev routeSig : routeCode.Signature roles := parentCode_checked.signature.2.2.2 _
  (List.mem_cons_of_mem _ (List.mem_singleton_self _))
abbrev direct := childSite plan leftCode leftSig
abbrev branch := childSite plan routeCode routeSig
abbrev kids := [direct.occurrence,branch.occurrence]
abbrev z := binder plan 5
abbrev o0 : Origin := .nominal (.source 0) 0 0
abbrev o1 : Origin := .nominal (.source 1) 0 0

theorem query : GeneralNominalInspection.queries snapshot interpretation parentCode =
    [.nominal 0 [.variables [0]],.nominal 0 [.variables [1]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
    GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,interpretation,parentCode,
    GeneralNominalCenteredHeadAllocEncoding.declaration]

private theorem read_inner (start : Nat) (stop : Fin 3) (name : Nat) :
    inspectMany snapshot [.variables [name]] [(stop,stop)]
      (fun i => some (.nominal (.source start) 0 i)) 0 =
        { captures := [⟨name,(stop,stop),some (.nominal (.source start) 0 0)⟩],
          checked := [(stop,stop)], anchors := [(.nominal (.source start) 0 0,(stop,stop))] } := by
  rw [inspectMany.eq_2,inspectMany.eq_1]
  simp [inspect,Report.append]

theorem report : GeneralNominalPacketSupport.report packet =
    {captures := [⟨0,(1,1),some o0⟩,⟨1,(2,2),some o1⟩],
      inspected := [(0,0),(1,1)],
      checked := [(0,0),(1,1),(0,0),(1,1),(1,1),(2,2)],
      anchors := [(o0,(1,1)),(o1,(2,2))]} := by
  unfold GeneralNominalPacketSupport.report GeneralNominalRecursiveCandidates.report
  rw [show GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration = _ from query]
  simp [inspectMany.eq_2,inspectMany.eq_1,inspect,typeArguments,listDescriptor,Report.visit,Report.append,o0,o1]
  erw [read_inner 0 1 0,read_inner 1 2 1]
  simp

theorem bindings_exact : packet.bindings = [(0,(1,1)),(1,(2,2))] := by
  change bindings snapshot (GeneralNominalPacketSupport.report packet) = _
  rw [report]
  rfl

theorem input_binders : binder plan 0 = 1 ∧ binder plan 1 = 2 := by
  unfold binder capture GeneralNominalVersionedFrame231.frame
  rw [bindings_exact]
  exact ⟨rfl,rfl⟩

theorem capture_inputs : (capture packet).inputs 0 = (1,1) ∧ (capture packet).inputs 1 = (2,2) := by
  unfold capture GeneralNominalVersionedFrame231.frame
  rw [bindings_exact]
  exact ⟨rfl,rfl⟩

theorem canonical : GeneralCanonicalChildOrder.canonicalRequirements parentCode.requirements =
    [leftCode,routeCode] := by
  change ([leftCode,routeCode].mergeSort fun a b => decide (a.id ≤ b.id)) = _
  simp only [List.mergeSort_pair,show decide (leftCode.id ≤ routeCode.id) = true from by decide +kernel,ite_true]

theorem emitted : GeneralNominalVersionedChildren232.emitted plan = [direct,branch] := by
  unfold GeneralNominalVersionedChildren232.emitted
  let pick : Clause → Site roles := fun c => if c.id = 10 then direct else branch
  calc
    _ = (GeneralCanonicalChildOrder.canonicalRequirements parentCode.requirements).attach.map
        (fun c => pick c.val) := by
      apply List.map_congr_left
      intro c _
      have hit := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr c.property
      change c.val ∈ [leftCode,routeCode] at hit
      rcases c with ⟨c,mem⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hit
      rcases hit with rfl|rfl <;> rfl
    _ = _ := by rw [List.attach_map_val,canonical]; rfl

theorem children_exact : children packet = kids := by
  rw [← GeneralNominalVersionedChildren232.emitted_occurrences plan,emitted]
  rfl

theorem direct_args (i : Fin (roles direct.occurrence.demand.role).arity) :
    direct.occurrence.demand.arguments i = (2,2) := by
  have e : i.val=0 := by have h := i.isLt; change i.val<1 at h; omega
  have same : i = ⟨0,by decide⟩ := Fin.ext e
  subst i
  change (capture packet).inputs 1 = _
  exact capture_inputs.2

theorem route_args (i : Fin (roles branch.occurrence.demand.role).arity) :
    branch.occurrence.demand.arguments i = (1,1) := by
  have e : i.val=0 := by have h := i.isLt; change i.val<1 at h; omega
  have same : i = ⟨0,by decide⟩ := Fin.ext e
  subst i
  exact capture_inputs.1

theorem direct_center (i : Fin (roles direct.occurrence.demand.role).arity) : direct.center i = 2 := by
  have e : i.val=0 := by have h := i.isLt; change i.val<1 at h; omega
  have same : i = ⟨0,by decide⟩ := Fin.ext e
  subst i
  exact input_binders.2

theorem route_center (i : Fin (roles branch.occurrence.demand.role).arity) : branch.center i = 1 := by
  have e : i.val=0 := by have h := i.isLt; change i.val<1 at h; omega
  have same : i = ⟨0,by decide⟩ := Fin.ext e
  subst i
  exact input_binders.1

theorem direct_output : direct.occurrence.demand.outputs = [⟨1,z⟩] := by
  rfl

theorem route_output : branch.occurrence.demand.outputs = [] := rfl

theorem vars0 (m : Assignment) (mode) : variables plan m mode 0 = (m 1).1 := by
  unfold variables
  simp only [show ¬ 0 ∈ parentCode.outputNames from by decide +kernel,ite_false]
  cases mode <;> simp only [input_binders.1,capture_inputs.1]

theorem vars1 (m : Assignment) (mode) : variables plan m mode 1 = (m 2).1 := by
  unfold variables
  simp only [show ¬ 1 ∈ parentCode.outputNames from by decide +kernel,ite_false]
  cases mode <;> simp only [input_binders.2,capture_inputs.2]

theorem vars5 (m : Assignment) (mode) : variables plan m mode 5 = (m z).1 := by
  simp only [variables,show 5 ∈ parentCode.outputNames from by decide +kernel,ite_true]

theorem emitted_schema : emittedSchema plan =
    ⟨[⟨2,.lower,.variable 1⟩,⟨2,.upper,.variable 1⟩,⟨z,.actual,.variable 5⟩,
      ⟨1,.lower,.variable 0⟩,⟨1,.upper,.variable 0⟩],false⟩ := by
  unfold emittedSchema emittedRequests GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,canonical]
  unfold capture GeneralNominalVersionedFrame231.frame
  rw [bindings_exact]
  rfl

theorem head_schema : plan.headSchema =
    ⟨[⟨0,o0,.actual⟩,⟨1,o1,.actual⟩],[(.source 0,.nominal 0 1),(.source 1,.nominal 0 1)],false⟩ := by
  unfold Plan.headSchema
  rw [show GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration = _ from query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,rootSite,List.ofFn_succ,o0,o1]

theorem known_head (m : Assignment) (valid : GeneralNominalState.Models snapshot m)
    (i : Fin 3) (j : Fin 3) (obs : snapshot.nominals i = some (listDescriptor j)) :
    GeneralNominalOriginTerms.Head m (.source i.val) (.nominal 0 1) :=
  GeneralNominalNamedArgumentReadback.nominal_head snapshot
    (models := GeneralNominalState.Models snapshot) (fun _ h => h) i (listDescriptor j) obs [(j,j)] rfl m valid

theorem projected (m : Assignment) (valid : GeneralNominalState.Models snapshot m)
    (i : Fin 3) (j : Fin 3) (obs : snapshot.nominals i = some (listDescriptor j)) :
    (∃ actual, Observes m (.nominal (.source i.val) 0 0) actual) ∧
      ∀ actual, Observes m (.nominal (.source i.val) 0 0) actual →
      Fits snapshot m (j,j) actual :=
  nominal_argument_bounds snapshot m valid i (listDescriptor j) obs 0 (j,j) rfl

theorem projected_equal (m : Assignment) (valid : GeneralNominalState.Models snapshot m)
    (i j : Fin 3) (obs : snapshot.nominals i = some (listDescriptor j)) :
    GeneralNominalOriginTerms.Same m (.nominal (.source i.val) 0 0) (.source j.val) := by
  have h := projected m valid i j obs
  refine ⟨h.1,⟨_,.source _⟩,?_⟩
  intro a b left right
  cases right
  exact ⟨(h.2 a left).2,(h.2 a left).1⟩

theorem projections (m : Assignment) (valid : GeneralNominalState.Models snapshot m) :
    ProjectionModels snapshot (GeneralNominalPacketSupport.report packet) m := by
  rw [report]
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact projected m valid 0 1 rfl
    · exact projected m valid 1 2 rfl
  · intro _ h; cases h
  · intro a aMem b bMem same ref refEq actual seen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at aMem bMem
    rcases aMem with rfl|rfl <;> rcases bMem with rfl|rfl
    all_goals try cases same
    all_goals
      cases Option.some.inj refEq
      first | exact (projected m valid 0 1 rfl).2 actual seen | exact (projected m valid 1 2 rfl).2 actual seen
  · intro a aMem b bMem same x y xEq yEq first last aSeen bSeen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at aMem bMem
    rcases aMem with rfl|rfl <;> rcases bMem with rfl|rfl
    all_goals try cases same
    all_goals
      cases Option.some.inj xEq
      cases Option.some.inj yEq
      first
      | exact nominal_observation_unique m (.argument (.source 0) 0 0) first last aSeen bSeen
      | exact nominal_observation_unique m (.argument (.source 1) 0 0) first last aSeen bSeen

theorem ordinary (m : Assignment) : Ordinary packet m := by
  refine ⟨?_,?_,?_⟩
  · intro a aMem b bMem same
    rw [bindings_exact] at aMem bMem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at aMem bMem
    rcases aMem with rfl|rfl <;> rcases bMem with rfl|rfl
    all_goals first | exact subtype_refl _ | cases same
  · change PresenceNormalForm.All CommonNominalFullCarrier.model m
      (GeneralNominalVersionedAllocation231.merges snapshot compiled root.identity parentCode packet.bindings)
    rw [bindings_exact]
    exact PresenceNormalForm.all_nil _ _
  · rw [report]
    intro atom member
    change atom ∈ [.tyLe (.var 0) (.var 0),.tyLe (.var 1) (.var 1),.tyLe (.var 0) (.var 0),
      .tyLe (.var 1) (.var 1),.tyLe (.var 1) (.var 1),.tyLe (.var 2) (.var 2)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> exact subtype_refl _

theorem holds (m : Assignment) (valid : GeneralNominalState.Models snapshot m) : Holds plan m := by
  have output : Outputs plan m := by
    unfold Outputs
    rw [emitted_schema]
    intro e member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl
    all_goals
      first
      | change Equivalent (m 2).1 (variables plan m _ 1)
        rw [vars1]; exact ⟨subtype_refl _,subtype_refl _⟩
      | change Equivalent (m 1).1 (variables plan m _ 0)
        rw [vars0]; exact ⟨subtype_refl _,subtype_refl _⟩
      | change Equivalent (m z).1 (variables plan m _ 5)
        rw [vars5]; exact ⟨subtype_refl _,subtype_refl _⟩
  refine ⟨valid,⟨ordinary m,projections m valid,point_root_holds _ root (fun _ => rfl) m,?_,?_,
    (fun e seen _ => output e seen),?_⟩,output⟩
  · intro name used
    have h : name = 0 ∨ name = 1 := by
      rcases used with head|⟨clause,present,input⟩
      · change name ∈ [0,1] at head
        simpa using head
      · change clause ∈ [leftCode,routeCode] at present
        simp only [List.mem_cons,List.not_mem_nil,or_false] at present
        rcases present with rfl|rfl
        · right; simpa [GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
            GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables] using
            (show name ∈ GeneralDeclarationPatterns.variablesArgs
               (GeneralDeclarationPatterns.normalizeArgs [.var 1]) from input)
        · left; simpa [GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
            GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables] using
            (show name ∈ GeneralDeclarationPatterns.variablesArgs
               (GeneralDeclarationPatterns.normalizeArgs [.var 0]) from input)
    rcases h with rfl|rfl
    · rw [input_binders.1,capture_inputs.1]; exact ⟨subtype_refl _,subtype_refl _⟩
    · rw [input_binders.2,capture_inputs.2]; exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [head_schema]
    constructor
    · intro test seen
      simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
      rcases seen with rfl|rfl
      · exact known_head m valid 0 1 rfl
      · exact known_head m valid 1 2 rfl
    · intro entry seen
      simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
      rcases seen with rfl|rfl
      · exact input_binders.1.symm ▸ projected_equal m valid 0 1 rfl
      · exact input_binders.2.symm ▸ projected_equal m valid 1 2 rfl
  · intro clause found sig
    change clause ∈ [leftCode,routeCode] at found
    simp only [List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with rfl|rfl
    · refine ⟨?_,?_⟩
      · intro i
        rw [direct_args,direct_center]
        exact ⟨subtype_refl _,subtype_refl _⟩
      · have schema : childSchema plan leftCode sig = ⟨[⟨2,.actual,.variable 1⟩],false⟩ := by
          unfold childSchema childRequests
          simp only [List.ofFn_succ,List.ofFn_zero]
          change GeneralNominalCenteredHeadMatSchemas.generated _ _ [⟨.var 1,direct.center _,.actual⟩] = _
          rw [direct_center]
          rfl
        rw [schema]; intro a seen; cases List.mem_singleton.mp seen
        change Equivalent (m 2).1 (variables plan m .actual 1)
        rw [vars1]; exact ⟨subtype_refl _,subtype_refl _⟩
    · refine ⟨?_,?_⟩
      · intro i
        rw [route_args,route_center]
        exact ⟨subtype_refl _,subtype_refl _⟩
      · have schema : childSchema plan routeCode sig = ⟨[⟨1,.actual,.variable 0⟩],false⟩ := by
          unfold childSchema childRequests
          simp only [List.ofFn_succ,List.ofFn_zero]
          change GeneralNominalCenteredHeadMatSchemas.generated _ _ [⟨.var 0,branch.center _,.actual⟩] = _
          rw [route_center]
          rfl
        rw [schema]; intro a seen; cases List.mem_singleton.mp seen
        change Equivalent (m 1).1 (variables plan m .actual 0)
        rw [vars0]; exact ⟨subtype_refl _,subtype_refl _⟩

end Yulang.GeneralLatePeerRoot311
