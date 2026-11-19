import Yulang.GeneralRebaseClosedChildShape279

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 9900000
namespace Yulang.GeneralRebaseClosedChildIdentity279
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralRebaseClosedChildShape279 (Canonical ClosedArguments argList)
open GeneralNominalCenteredHeadMatCompletionRequests (Formed same_outputs)
open GeneralRebaseOccurrenceCode279 (occurrenceCode occurrenceCode_injective DemandCode OccurrenceCode demandCode)
open GeneralNominalCenteredHeadAllocEncoding (registry)

private theorem list_unique {α : Type} (key : α → Nat) (xs : List α) (unique : (xs.map key).Nodup)
    {a b : α} (one : a ∈ xs) (two : b ∈ xs) (eq : key a = key b) : a = b := by
  induction xs with
  | nil => cases one
  | cons head rest ih =>
    have sep := List.nodup_cons.mp unique
    rcases List.mem_cons.mp one with rfl | tailA
    · rcases List.mem_cons.mp two with rfl|tailB
      · rfl
      · exact False.elim (sep.1 (List.mem_map.mpr ⟨b,tailB,eq.symm⟩))
    · rcases List.mem_cons.mp two with rfl|tailB
      · exact False.elim (sep.1 (List.mem_map.mpr ⟨a,tailA,eq⟩))
      · exact ih sep.2 tailA tailB

theorem same_shape {r : Registry} {root a b : Occurrence roles} {seed : Nat}
    (checked : Checked r) (one : Canonical r seed root a) (two : Canonical r seed root b)
    (same : a.identity = b.identity) :
    a.demand.role = b.demand.role ∧ List.ofFn a.demand.arguments = List.ofFn b.demand.arguments := by
  rcases one with rfl | ⟨p,d,visible,c,mem,above,id,role,args⟩
  · rcases two with rfl | ⟨p,d,_,c,_,above,id,_,_⟩
    · exact ⟨rfl,rfl⟩
    · have grow := GeneralNominalIdentities.source_above_invocation seed
        (GeneralNominalAllocation.origin p d.id 6 c.id 0)
      change p < _ at grow
      omega
  · rcases two with rfl | ⟨q,e,visible',f,mem',above',id',role',args'⟩
    · have grow := GeneralNominalIdentities.source_above_invocation seed
        (GeneralNominalAllocation.origin p d.id 6 c.id 0)
      change p < _ at grow
      omega
    · have keys := (GeneralNominalIdentities.source_identity seed _ _).mp (id.symm.trans (same.trans id'))
      have dp : d.id = e.id := congrArg (fun k : GeneralNominalIdentities.Origin => k.2.1) keys
      have de := GeneralDictionaryEmissionPlans.declaration_key_unique r checked d e visible visible' dp
      subst e
      have parent : p = q := congrArg (fun k : GeneralNominalIdentities.Origin => k.1) keys
      have clause : c.id = f.id := congrArg (fun k : GeneralNominalIdentities.Origin => k.2.2.2.1) keys
      have cf := list_unique Clause.id d.requirements (checked.2 d visible).identified.1 mem mem' clause
      subst q
      subst f
      exact ⟨role.trans role'.symm,args.trans args'.symm⟩

theorem exact {r : Registry} {root a b : Occurrence roles} {seed : Nat}
    (checked : Checked r) (one : Canonical r seed root a) (two : Canonical r seed root b)
    (outOne : Formed r seed root a) (outTwo : Formed r seed root b) (same : a.identity = b.identity) :
    a = b := by
  obtain ⟨role,args⟩ := same_shape checked one two same
  have outs := same_outputs checked outOne outTwo same
  apply occurrenceCode_injective
  simp only [occurrenceCode,demandCode,OccurrenceCode.mk.injEq,DemandCode.mk.injEq]
  exact ⟨same,role,args,congrArg _ outs⟩

theorem cross_trace {r : Registry} {root : Occurrence roles} {start first last : State roles}
    (source : (boundary roles).Initial r root start)
    (checked : (boundary roles).Checked r) (closed : ClosedArguments (registry r))
    (firstPath : B4Target.Steps ((boundary roles).Step r root) start first)
    (lastPath : B4Target.Steps ((boundary roles).Step r root) start last)
    {a b : GeneralNominalDemandMerging.Site roles}
    (firstRecorded : a ∈ first.core.erased.current.sites)
    (lastRecorded : b ∈ last.core.erased.current.sites)
    (same : a.occurrence.identity = b.occurrence.identity) : a.occurrence = b.occurrence := by
  obtain ⟨legacy,⟨context,_,_,_,_,_,rfl⟩,rfl⟩ := source
  exact exact ((GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked).2)
    (GeneralRebaseClosedChildShape279.trace closed firstPath a firstRecorded)
    (GeneralRebaseClosedChildShape279.trace closed lastPath b lastRecorded)
    ((GeneralNominalVersionedMixedCompletionRequests235.trace firstPath).raw a firstRecorded)
    ((GeneralNominalVersionedMixedCompletionRequests235.trace lastPath).raw b lastRecorded) same

end Yulang.GeneralRebaseClosedChildIdentity279
