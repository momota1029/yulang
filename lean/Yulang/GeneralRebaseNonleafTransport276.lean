import Yulang.GeneralRebaseNonleafPrepared276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 9200000
namespace Yulang.GeneralRebaseNonleafTransport276
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Frame Evidence Instance)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedMixedKernel234 (Committed)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseRetarget275 (Observed)
open GeneralRebaseNonleafCommitted276 (result refinement interpretation)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)

variable {roles : Roles.RoleDecls} {state : State roles} {ctx : GeneralNominalCandidates.Context}
variable {registry : Registry}

def ReadyRule (registry : Registry) (state : State roles) : LocalInstance roles :=
 fun goal key children => ∃ p : Plan roles,
   Frame registry state.core goal key p ∧
   Observed p ∧
   Committed state p ∧
   Ready state.core goal p ∧
   children = GeneralNominalVersionedFrame231.children p.packet

theorem leaf_or_node {goal : Occurrence roles} {key : Nat} {children : List (Occurrence roles)}
 (m : Assignment) (valid : Models state m) (proof : ReadyRule registry state goal key children) :
 Instance registry state.core m goal key children := by
 obtain ⟨p,frame,_,committed,ready,order⟩ := proof
 have held := committed.1 m valid
 have effects : GeneralNominalVersionedEffects231.ClassEffects state.core goal p m :=
   frame.occurrence_eq ▸ held.2
 exact ⟨p,GeneralNominalVersionedEvidence231.certificate_of_semantics frame order held.1 ready effects⟩

theorem rule_refresh (cert : Refresh state ctx)
 (m : Assignment) (valid : Models (refresh state ctx) m)
 {goal : Occurrence roles} {key : Nat} {children : List (Occurrence roles)}
 (source : ReadyRule registry state goal key children) : ReadyRule registry (refresh state ctx) goal key children := by
 obtain ⟨p,frame,seen,committed,ready,order⟩ := source
 have real := GeneralRebaseNonleafPrepared276.frame frame cert seen committed m valid
 refine ⟨result frame cert,real,GeneralRebaseNonleafCommitted276.observed frame cert seen,
   GeneralRebaseNonleafCommitted276.committed frame cert seen committed,
   GeneralRebaseNonleafCommitted276.ready frame cert ready,?_⟩
 exact order.trans (GeneralRebaseNonleafRetarget276.children_eq p (refinement frame cert)
   (interpretation frame cert) seen).symm

theorem indexed_refresh (cert : Refresh state ctx)
 (m : Assignment) (valid : Models (refresh state ctx) m) (tree : Dictionary roles)
 (source : GeneralSourceDictionaries.Evidence (ReadyRule registry state) tree) :
 GeneralSourceDictionaries.Evidence (ReadyRule registry (refresh state ctx)) tree :=
 GeneralSourceDictionaries.evidence_mono _ _ (fun _ _ _ node => rule_refresh cert m valid node) source

theorem erase_refresh {goal : Occurrence roles} {payload : Payload} (cert : Refresh state ctx)
 (m : Assignment) (valid : Models (refresh state ctx) m)
 (source : ErasedEvidence (ReadyRule registry state) goal payload) :
 Evidence registry (refresh state ctx).core m goal payload := by
 obtain ⟨tree,readback,given⟩ := source
 have after := indexed_refresh cert m valid tree given
 exact ⟨tree,readback,GeneralSourceDictionaries.evidence_mono _ _ (fun _ _ _ success =>
   leaf_or_node m valid success) after⟩

end Yulang.GeneralRebaseNonleafTransport276
