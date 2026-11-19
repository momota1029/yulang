import Yulang.GeneralRebaseChartDelta281
import Yulang.GeneralRebaseTerminalFirstSupport274

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebasePhasePrivate281
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryVersionedPointStage233 (point)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralDictionaryVersionedSecondRaw233 (newLo newHi)
open GeneralRebaseTerminalPublic274 (first)
open GeneralRebaseTerminalPointExact274 (NewFacts)
open GeneralRebaseTerminalFirstSupport274 (pool)
open GeneralRebasePortCopy280 (Write Apart Isolated Unambiguous Copy copy_agrees)
open GeneralRebasePortProjection280 (Respects Project)
open GeneralRebaseChartFixtures281 (outputChart)
open GeneralRebaseChartDelta281 (LocalDelta delta_exact)
open GeneralRebaseChartStep281 (Public)
open GeneralNominalVersionedModelSupport237 (Support)

def writes : List Write := [(newLo,2),(newHi,2)]

theorem unique : Unambiguous writes := by
  intro a wroteA b wroteB _
  simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at wroteA wroteB
  rcases wroteA with rfl|rfl <;> rcases wroteB with rfl|rfl <;> rfl

theorem private_to_first : Apart writes pool := by
  intro row listed
  simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at listed
  rcases listed with rfl|rfl <;> decide +kernel

theorem isolated : Isolated writes := by
  intro row listed
  simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at listed
  rcases listed with rfl|rfl <;> decide +kernel

theorem private_to_public : Apart writes [0,1,2,3,4] := by
  intro row listed
  simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at listed
  rcases listed with rfl|rfl <;> decide +kernel

theorem supported : Support point pool :=
  GeneralNominalVersionedModelSupport237.transport
    (fun m => GeneralDictionaryVersionedPointStage233.models_iff m)
    (GeneralNominalVersionedModelSupport237.weaken
      (GeneralNominalVersionedModelSupport237.current first) GeneralRebaseTerminalFirstSupport274.complete)

theorem keeps_value (m v : Assignment) (old : outputChart.agrees m v) :
    outputChart.agrees (Copy writes m) v := by
  intro id small
  have listed : id ∈ ([0,1,2,3,4] : List Nat) := by
    have bins : id = 0 ∨ id = 1 ∨ id = 2 ∨ id = 3 ∨ id = 4 := by omega
    rcases bins with rfl|rfl|rfl|rfl|rfl <;> decide
  have kept := copy_agrees private_to_public m id listed
  exact (congrArg Prod.fst kept).symm.trans (old id small)

theorem port_equations (m : Assignment) : Respects writes m ↔ NewFacts m := by
  constructor
  · intro valid
    exact ⟨valid _ List.mem_cons_self,valid _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩
  · rintro ⟨lo,hi⟩ row h
    simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl
    · exact lo
    · exact hi

noncomputable def localDelta : LocalDelta outputChart point installed where
  obligations := []
  contained := List.nil_subset _
  privateDefs := writes
  protectedNames := pool
  wellDefined := unique
  isolated := isolated
  oldSupport := supported
  privateOld := private_to_first
  retained := keeps_value
  atom := fun _ _ => True
  invariant := fun _ _ _ _ absent => nomatch absent
  exact := fun m => by
    rw [GeneralRebaseTerminalPointExact274.exact,port_equations]
    constructor
    · rintro ⟨h,eq⟩; exact ⟨h,eq,fun _ no => nomatch no⟩
    · rintro ⟨h,eq,_⟩; exact ⟨h,eq⟩

theorem local_public_exact (m : Assignment) : Public outputChart installed m ↔ Public outputChart point m :=
  GeneralRebaseChartDelta281.repeated_is_public_silent localDelta (fun _ no => nomatch no) m

end Yulang.GeneralRebasePhasePrivate281
