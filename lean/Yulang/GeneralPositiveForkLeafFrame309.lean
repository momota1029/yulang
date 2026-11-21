import Yulang.GeneralPositiveForkLeaf309

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralPositiveForkLeafFrame309
open GeneralPositiveForkSource309 (root compiled registry checked parent init_source)
open GeneralPositiveForkPlan309 (loSite hiSite)
open GeneralPositiveForkInstall309 (after reachable centers raw_sites)
open GeneralPositiveForkLeaf309
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (state)
open GeneralNominalVersionedCandidates231 (inputs Prepared Survivor Unique)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalRecursiveCandidates (arguments)
open GeneralNominalVersionedFrame231 (children)
open GeneralNominalState (sources Known)
open GeneralNominalIdentities (Origin source source_identity source_above_seed)
open GeneralNominalVersionedAllocation231 (Fresh keys)
open GeneralNominalVersionedInstallation231 (reserved atoms)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations

abbrev parentPacket := GeneralPositiveForkPlan309.packet

theorem invocations (side : Side) : (site side).occurrence.identity ≠ root.identity := by
  cases side <;> decide +kernel

theorem atom_bound : ∀ id ∈ (atoms parentPacket).flatMap GeneralNominalState.atomSources, id ≤ 1 := by
  unfold atoms
  rw [GeneralPositiveForkPlan309.bindings,GeneralPositiveForkPlan309.report]
  decide +kernel

theorem support (id : Nat) (h : id ∈ sources ctx.state) :
    id ≤ 1 ∨ id ∈ reserved parentPacket := by
  change id ∈ List.ofFn (state true).base.source ++ List.ofFn (state true).base.rowSource ++
    ([] ++ reserved parentPacket) ++ ([] ++ atoms parentPacket).flatMap GeneralNominalState.atomSources at h
  simp only [List.nil_append,List.mem_append] at h
  rcases h with ((term|row)|reserve)|atom
  · obtain ⟨i,e⟩ := List.mem_ofFn.mp term
    change i.val = id at e
    have b := i.isLt
    exact Or.inl (by omega)
  · obtain ⟨i,e⟩ := List.mem_ofFn.mp row
    change i.val = id at e
    have b := i.isLt
    exact Or.inl (by omega)
  · exact Or.inr reserve
  · exact Or.inl (atom_bound id atom)

theorem fresh (side : Side) (bs : GeneralNominalAllocation.Bindings) :
    Fresh ctx.state compiled (site side).occurrence.identity bs := by
  intro key recorded collision
  rcases support _ collision with small|prior
  · have bigger : 1 < source ctx.state.seed key := source_above_seed _ _
    omega
  · obtain ⟨old,member,equal⟩ := List.mem_map.mp prior
    have rootKey := GeneralRebaseDisplayChildFresh276.keys_root member
    have childKey := GeneralRebaseDisplayChildFresh276.keys_root recorded
    have same : old = key := (source_identity ctx.state.seed _ _).mp equal
    exact False.elim (invocations side (childKey.symm.trans ((congrArg Prod.fst same).symm.trans rootKey)))

theorem located (side : Side) : arguments ctx (inputs (site side).occurrence) = some [(one,one)] := by
  cases side <;> decide +kernel

theorem known (side : Side) : ¬ GeneralNominalState.RootPending ctx.state (inputs (site side).occurrence).demand := by
  rintro ⟨i,no⟩
  have oneKnown : Known ctx.state 1 := ⟨one,rfl,Or.inl (by decide +kernel)⟩
  exact no ((congrArg Prod.fst (args side i)).symm ▸ oneKnown)

theorem linked (side : Side) : GeneralNominalState.Linked ctx.state (inputs (site side).occurrence).demand := by
  refine ⟨?_,fun _ absent => nomatch absent⟩
  intro i
  change ((site side).occurrence.demand.arguments i).1 ∈ sources ctx.state ∧
    ((site side).occurrence.demand.arguments i).2 ∈ sources ctx.state
  rw [args]
  exact ⟨GeneralNominalAllocationSupport.slot_source ctx.state one,GeneralNominalAllocationSupport.slot_source ctx.state one⟩

theorem prepared (side : Side) (m : Assignment) (valid : Models after m) :
    Prepared compiled ctx (site side).occurrence (decl side) := by
  refine ⟨⟨rfl,init_source.metadata.2⟩,linked side,[(one,one)],located side,fresh side _,?_,m,?_⟩
  · change GeneralNominalRecursiveInspection.Finished (GeneralNominalPacketSupport.report (packet side))
    rw [report]; exact ⟨rfl,rfl,rfl⟩
  · exact GeneralNominalVersionedPlans231.head_models (plan := plan side) (holds side m valid)

theorem declaration_eq (side : Side) (d : Declaration) (seen : d ∈ compiled.declarations)
    (role : d.role = (site side).occurrence.demand.role) : d = decl side := by
  change d ∈ [GeneralPositiveForkSource309.right,parent,GeneralPositiveForkSource309.left] at seen
  simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
  cases side <;> rcases seen with rfl|rfl|rfl <;> first | rfl | cases role

theorem frame (side : Side) (m : Assignment) (valid : Models after m) :
    Frame compiled after.core (site side).occurrence (decl side).id (plan side) := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,?_,?_,located side,prepared side m valid⟩
  · rw [raw_sites]; cases side
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  · rw [centers]; cases side
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  · cases side
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    · exact List.mem_cons_self
  · cases side <;> rfl

theorem unique (side : Side) (m : Assignment) (valid : Models after m) :
    Unique compiled ctx (site side).occurrence (decl side).id [] := by
  let f := frame side m valid
  have survivor : Survivor compiled ctx (site side).occurrence (decl side).id [] :=
    ⟨known side,decl side,f.visible,sideChecked side,rfl,f.role_eq,[(one,one)],located side,
      prepared side m valid,(no_children side).symm⟩
  refine ⟨survivor,?_⟩
  intro key kids other
  have copy := other
  obtain ⟨_,d,seen,_,keyeq,role,_⟩ := copy
  cases declaration_eq side d seen role
  subst key
  exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional GeneralPositiveForkPreinstall309.compiled_checked other survivor⟩

end Yulang.GeneralPositiveForkLeafFrame309
