import Yulang.GeneralRebaseCompoundOwnerBlock273

set_option maxRecDepth 24000
set_option maxHeartbeats 6300000
namespace Yulang.GeneralRebaseCompoundOwnerCapture273
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedPlans231 (Holds SchemaHolds)
open GeneralNominalAllocation (equations)
open PresenceNormalForm (All all_append)
open GeneralNominalVersionedFrame231 (capture binder)
open GeneralDictionaryCompoundObstruction238 (oldPlan currentPlan)
open GeneralDictionaryJournalRefinement228Source (roles foo snapshot width_two root_fixed)
open GeneralRebaseCompoundOwnerBlock273 (normalized_lo normalized_hi)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)
open GeneralNominalRecursiveInspection (Observes)
open GeneralNominalMaterialization (Use)

abbrev low (p : Plan roles) := ((capture p.packet).inputs 0).1
abbrev high (p : Plan roles) := ((capture p.packet).inputs 0).2

def PairFacts (m : Assignment) (low high a b : Nat) : Prop :=
 All model m (equations low (.union (.var a) (.var a)) ++ equations high (.inter (.var b) (.var b)))

theorem read_pair (m : Assignment) (l h a b : Nat) (held : PairFacts m l h a b) :
 Equivalent (m l).1 (m a).1 ∧ Equivalent (m h).1 (m b).1 := by
 have ⟨lo,hi⟩ := (all_append ..).mp held
 have lowEq := (GeneralNominalCaptureMerges.equations_exact ..).mp lo
 have highEq := (GeneralNominalCaptureMerges.equations_exact ..).mp hi
 exact ⟨equivalent_trans lowEq (normalized_lo _),equivalent_trans highEq (normalized_hi _)⟩

theorem old_pair (m : Assignment) (held : Holds oldPlan m) : PairFacts m (low oldPlan) (high oldPlan) 4 2 := by
 have agg := held.2.1.1.2.1
 rw [GeneralDictionaryCompoundPacket238.bindings_exact] at agg
 have lo : low oldPlan = GeneralDictionaryCompoundVersionedModel238.names 0 := by decide +kernel
 have hi : high oldPlan = GeneralDictionaryCompoundVersionedModel238.names 1 := by decide +kernel
 rw [lo,hi]
 exact ((all_append ..).mp agg).1

theorem current_pair (m : Assignment) (held : Holds currentPlan m) : PairFacts m (low currentPlan) (high currentPlan) 2 2 := by
 have agg := held.2.1.1.2.1
 rw [GeneralDictionaryCompoundCurrent238.bindings_exact] at agg
 have aligned := GeneralDictionaryCompoundPointHead238.capture_exact
   GeneralDictionaryCompoundPoint238.allocated GeneralDictionaryCompoundPoint238.reserved GeneralDictionaryCompoundPoint238.ordinary
 have lo : low currentPlan = GeneralDictionaryCompoundPointHead238.freshName 0 := congrArg Prod.fst aligned
 have hi : high currentPlan = GeneralDictionaryCompoundPointHead238.freshName 1 := congrArg Prod.snd aligned
 rw [lo,hi]
 exact ((all_append ..).mp agg).1

abbrev origin := GeneralDictionaryCompoundPacket238.origin0

theorem actual_is_width (m : Assignment) (p : Plan roles) (source : GeneralNominalState.Models snapshot m)
 (layout : p.headSchema = oldPlan.headSchema) (schema : SchemaHolds p p.headSchema m) :
 Equivalent (m (binder p 0)).1 (m 2).1 := by
 have extracted : (⟨0,origin,.actual⟩ : Use) ∈ p.headSchema.variables := by
   rw [layout,GeneralDictionaryCompoundPacket238.head_schema]
   exact List.mem_cons_self
 have same : GeneralNominalOriginTerms.Same m origin (.source (binder p 0)) := schema.2 _ extracted
 have actual : Observes m origin .emptyRecord :=
   .nominal (arguments := [.inl .emptyRecord,.inl .emptyRecord]) (.source 0) (root_fixed m source) rfl
 have exact := same.2.2 _ _ actual (.source _)
 have width := width_two m source
 exact equivalent_trans ⟨exact.2,exact.1⟩ ⟨width.2,width.1⟩

theorem historical_center (m : Assignment) (held : Holds oldPlan m) : Equivalent (m (binder oldPlan 0)).1 (m 2).1 :=
 actual_is_width m oldPlan held.1 rfl held.2.1.2.2.2.2.1

theorem current_center (m : Assignment) (held : Holds currentPlan m) : Equivalent (m (binder currentPlan 0)).1 (m 2).1 :=
 actual_is_width m currentPlan ((GeneralRebaseCompoundReplacementFrame273.snapshot_exact m).mp held.1).1
   GeneralDictionaryCompoundReplay238.head_schema held.2.1.2.2.2.2.1

end Yulang.GeneralRebaseCompoundOwnerCapture273
