import Yulang.GeneralPresenceSnapshotBlock250
/-! Every old target remains reserved, even when this update supplies no RHS
for it. Missing entries retain their old snapshot value. Raw targets outside
the reserved domain are not silently certified by the coverage theorem. -/
namespace Yulang.GeneralPresencePersistentSnapshot250
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedSubstitution247
open GeneralPresenceOrderedDependence247 GeneralPresenceOrderedSyntax247
open GeneralPresenceUsedSupport245
variable {Name : Type} [DecidableEq Name]

def overlay (old raw : List (Entry Name)) : List (Entry Name) :=
 old.map (fun entry => (entry.1,(lookup raw entry.1).getD (.var entry.1)))

def refresh (old raw : List (Entry Name)) : List (Entry Name) := transform (mapping old) (overlay old raw)

theorem target_list (old raw : List (Entry Name)) : (refresh old raw).map Prod.fst = old.map Prod.fst := by
 simp only [refresh,targets_preserved,overlay,List.map_map]
 rfl

theorem overlay_within (old raw : List (Entry Name)) : TargetsWithin (overlay old raw) old := by
 intro entry member
 obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
 exact ⟨original,present,rfl⟩

theorem refresh_within (old raw : List (Entry Name)) : TargetsWithin (refresh old raw) old :=
 GeneralPresenceSnapshotBlock250.transformed_within _ _ (overlay_within old raw)

theorem old_within (old raw : List (Entry Name)) : TargetsWithin old (refresh old raw) := by
 intro entry member
 refine ⟨(entry.1,((lookup raw entry.1).getD (.var entry.1)).subst (mapping old)),?_,rfl⟩
 exact List.mem_map.mpr ⟨(entry.1,(lookup raw entry.1).getD (.var entry.1)),
   List.mem_map.mpr ⟨entry,member,rfl⟩,rfl⟩

omit [DecidableEq Name] in
theorem safe_nodup (old : List (Entry Name)) (safe : SafeOrder old) : (old.map Prod.fst).Nodup := by
 induction old with
 | nil => simp
 | cons head rest ih =>
   apply List.nodup_cons.mpr
   constructor
   · intro member
     obtain ⟨entry,present,equal⟩ := List.mem_map.mp member
     exact safe.2.1 entry present equal
   · exact ih safe.2.2.2

theorem refresh_safe (old raw : List (Entry Name)) (safe : SafeOrder old) : SafeOrder (refresh old raw) := by
 apply GeneralPresenceOrderedSupport247.safe_independent
 · rw [target_list]; exact safe_nodup old safe
 · intro target member rhs present read
   obtain ⟨original,found,equal⟩ := refresh_within old raw target member
   exact GeneralPresenceSnapshotBlock250.transformed_closed old (overlay old raw) safe rhs present _ read original found equal

theorem lookup_coherent (raw : List (Entry Name)) (coherent : Coherent raw)
 (entry : Entry Name) (member : entry ∈ raw) : lookup raw entry.1 = some entry.2 := by
 induction raw with
 | nil => simp at member
 | cons head rest ih =>
   by_cases same : head.1 = entry.1
   · have rhs := coherent head (by simp) entry member same
     simp [lookup,same,rhs]
   · rw [lookup,ite_eq_right same]
     apply ih
     · intro a am b bm equal
       exact coherent a (List.mem_cons_of_mem _ am) b (List.mem_cons_of_mem _ bm) equal
     · rcases List.mem_cons.mp member with equal | present
       · exact False.elim (same (congrArg Prod.fst equal.symm))
       · exact present

theorem covers (old raw : List (Entry Name)) (within : TargetsWithin raw old) (coherent : Coherent raw)
 (entry : Entry Name) (member : entry ∈ raw) :
 (entry.1,entry.2.subst (mapping old)) ∈ refresh old raw := by
 obtain ⟨original,present,equal⟩ := within entry member
 have found : lookup raw original.1 = some entry.2 := equal ▸ lookup_coherent raw coherent entry member
 apply List.mem_map.mpr
 refine ⟨(original.1,entry.2),?_,?_⟩
 · apply List.mem_map.mpr
   exact ⟨original,present,by simp [found]⟩
 · exact Prod.ext equal rfl

theorem retains_missing (old raw : List (Entry Name)) (entry : Entry Name) (member : entry ∈ old)
 (absent : lookup raw entry.1 = none) :
 (entry.1,(mapping old entry.1).ty) ∈ refresh old raw := by
 apply List.mem_map.mpr
 refine ⟨(entry.1,.var entry.1),?_,rfl⟩
 exact List.mem_map.mpr ⟨entry,member,by simp [absent]⟩

theorem raw_equations (old raw : List (Entry Name)) (within : TargetsWithin raw old) (coherent : Coherent raw)
 (model : Model) (assignment : Name → Comp model) (valid : All model assignment (block (refresh old raw))) :
 All model assignment (block (transform (mapping old) raw)) := by
 intro atom member
 obtain ⟨entry,present,contained⟩ := List.mem_flatMap.mp member
 obtain ⟨original,found,rfl⟩ := List.mem_map.mp present
 exact valid atom (List.mem_flatMap.mpr ⟨_,covers old raw within coherent original found,contained⟩)
end Yulang.GeneralPresencePersistentSnapshot250
