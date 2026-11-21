import Yulang.GeneralVersionedJointWrites312
import Yulang.GeneralDictionaryMatTerminalAssembly200

set_option backward.isDefEq.respectTransparency false
/-! Root materialization is already supported by the real live class.
Only internal where/child writes continue to need an additional check. -/
namespace Yulang.GeneralVersionedRootWrites312
open GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedPlans231 (variables emittedRequests emittedSchema)
open GeneralNominalCenteredHeadMatSchemas (Equation generated materialize)
open GeneralNominalCenteredHeadOutputs (requests request_retained)
open GeneralNominalMaterialization (rootRequests)
open GeneralDictionaryAssociatedProvenance (lookup)
open GeneralNominalCommonBridge (Assignment)
open GeneralFiniteTypedWrites312 (Holds Protected Coherent transitive symmetric reflexive)
open GeneralVersionedJointWrites312 (rows rhs protect inputNames equations)
open GeneralDictionaryDefault214ActualBodyFrame (classSources)

def outer (p : Plan roles) : List Equation :=
  (generated p.packet.registry.constructors p.packet.context.interpretation
    (rootRequests p.packet.declaration p.packet.site.occurrence)).equations

def whereRequests (p : Plan roles) : List GeneralNominalMaterialization.Request :=
  (GeneralCanonicalChildOrder.canonicalEmit p.packet.site.occurrence.identity p.packet.declaration p.packet.checked
    (GeneralNominalVersionedFrame231.capture p.packet)
    ((GeneralNominalVersionedFrame231.frame p.packet).allocation p.packet.declaration.id)).flatMap
    GeneralNominalCenteredHeadMatSchemas.emissionRequests

def inner (p : Plan roles) : List Equation :=
  (generated p.packet.registry.constructors p.packet.context.interpretation (whereRequests p)).equations ++
    p.packet.declaration.requirements.attach.flatMap fun clause =>
      (GeneralNominalVersionedPlans231.childSchema p clause.val
        (p.packet.checked.signature.2.2.2 clause.val clause.property)).equations

theorem generated_append (c) (i) (as bs : List GeneralNominalMaterialization.Request) :
    (generated c i (as ++ bs)).equations = (generated c i as).equations ++ (generated c i bs).equations := by
  induction as with
  | nil => rfl
  | cons first rest ih =>
    simpa only [List.cons_append,generated,GeneralNominalCenteredHeadMatSchemas.Schema.append,List.append_assoc]
      using congrArg (fun tail => (materialize c i first).equations ++ tail) ih

theorem separates (p : Plan roles) : equations p = outer p ++ inner p := by
  unfold equations emittedSchema emittedRequests outer inner whereRequests
  rw [generated_append,List.append_assoc]

theorem from_request {c i rs e} (member : e ∈ (generated c i rs).equations) :
    ∃ request ∈ rs, e ∈ (materialize c i request).equations := by
  induction rs with
  | nil => cases member
  | cons first rest ih =>
    change e ∈ (materialize c i first).equations ++ (generated c i rest).equations at member
    rcases List.mem_append.mp member with own|later
    · exact ⟨first,List.mem_cons_self,own⟩
    · obtain ⟨r,h,belongs⟩ := ih later
      exact ⟨r,List.mem_cons_of_mem _ h,belongs⟩

theorem materialize_target {c i rq e} (member : e ∈ (materialize c i rq).equations) :
    e.target = rq.target := by
  unfold materialize at member
  split at member
  · cases List.mem_singleton.mp member
    rfl
  · cases member

theorem outer_live {s : State roles} {e : Effect roles} {m : Assignment}
    (snapshot : e.snapshot = s.core)
    (live : e.Live s.core m) {eq : Equation} (member : eq ∈ outer e.plan) :
    eq.Holds (variables e.plan m) m ∧
      eq.target ∈ classSources s.core e.plan.packet.site.occurrence e.plan := by
  obtain ⟨request,requested,materialized⟩ := from_request member
  obtain ⟨output,localRequest,within⟩ := List.mem_flatMap.mp requested
  obtain ⟨rule,found,rfl⟩ := List.mem_map.mp within
  have found := Option.mem_toList.mp found
  have seen := request_retained e.plan.packet.site (snapshot ▸ e.frame.raw_recorded) (.refl _) localRequest
  have picked : lookup roles e.plan.packet.declaration output.name = some (.explicit rule) := by
    simp [lookup,found]
  have body := live.1 output seen (.explicit rule) picked
  have value := body eq materialized
  have target : eq.target = output.target := materialize_target materialized
  exact ⟨value,target ▸ List.mem_flatMap.mpr ⟨output,seen,List.mem_cons_self⟩⟩

def internalRows (p : Plan roles) (m : Assignment) :
    List GeneralFiniteTypedWrites312.Write :=
  (inner p).map fun q => (q.target,rhs p m q)

def FreeCoherent (r : List GeneralFiniteTypedWrites312.Write) (pool : List Nat) : Prop :=
  ∀ a ∈ r, ∀ b ∈ r, a.1 = b.1 → a.1 ∉ pool →
    CommonNominalFullCarrier.Equivalent a.2 b.2

theorem lift_table {s : State roles} {e : Effect roles} {m : Assignment} {names : List Nat}
    (snapshot : e.snapshot = s.core) (live : e.Live s.core m)
    (new : FreeCoherent (internalRows e.plan m) (protect s e names))
    (fixed : Protected (internalRows e.plan m) (protect s e names) m) :
    Coherent (rows e.plan m) ∧ Protected (rows e.plan m) (protect s e names) m := by
  have splitRows : rows e.plan m =
      ((outer e.plan).map (fun eq => (eq.target,rhs e.plan m eq))) ++ internalRows e.plan m := by
    unfold rows internalRows
    rw [separates,List.map_append]
  rw [splitRows]
  have outerFixed : ∀ row ∈ (outer e.plan).map (fun eq => (eq.target,rhs e.plan m eq)),
      Holds m row ∧ row.1 ∈ protect s e names := by
    intro row found
    obtain ⟨eq,member,rfl⟩ := List.mem_map.mp found
    have actual := outer_live snapshot live member
    exact ⟨actual.1,by simp [protect,actual.2]⟩
  have allFixed : Protected ((outer e.plan).map (fun eq => (eq.target,rhs e.plan m eq)) ++ internalRows e.plan m)
      (protect s e names) m := by
    intro row found h
    rcases List.mem_append.mp found with outer|inner
    · exact (outerFixed row outer).1
    · exact fixed row inner h
  refine ⟨?_,allFixed⟩
  intro a am b bm target
  by_cases supported : a.1 ∈ protect s e names
  · have held := allFixed a am supported
    have last := allFixed b bm (target ▸ supported)
    unfold Holds at held last
    rw [target] at held
    exact transitive (symmetric held) last
  · rcases List.mem_append.mp am with outside|aHere
    · exact False.elim (supported (outerFixed a outside).2)
    · rcases List.mem_append.mp bm with outside|bHere
      · exact False.elim (supported (target.symm ▸ (outerFixed b outside).2))
      · exact new a aHere b bHere target supported

end Yulang.GeneralVersionedRootWrites312
