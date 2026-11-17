import Yulang.GeneralDictionaryVersionLoopFamilyBack238
/-! The lower-equation premise of uniform raw-back is supplied by the actual
versioned private-installation transformer, not assumed as semantic validity.
This does not yet supply the mixed trusted cache or indexed journal path. -/
namespace Yulang.GeneralDictionaryVersionLoopFamilyInstallation238
open GeneralDictionaryVersionLoopFamilyPacket238 GeneralDictionaryVersionLoopFamilyBack238
open GeneralDictionaryVersionLoopNames238
variable (n : Nat) (allocated : List GeneralNominalIdentities.Origin)
 (reserved : List Nat) (ordinary : List (PresenceNormalForm.Atom Nat))

theorem lower_in_merges :
 GeneralNominalAllocation.equations (lower (n+1)) (.union (.var (lower n)) (.var (lower n))) ⊆
 GeneralNominalVersionedAllocation231.merges
   (GeneralDictionaryVersionLoopFamilySnapshot238.snapshot n allocated reserved ordinary)
   GeneralDictionaryVersionLoopSource237.registry 0 GeneralDictionaryVersionLoopSource237.declaration
   (packet n allocated reserved ordinary).bindings := by
 rw [bindings_exact]
 intro atom member
 change atom ∈ ((GeneralNominalAllocation.equations (lower (n+1)) (.union (.var (lower n)) (.var (lower n))) ++
   GeneralNominalAllocation.equations (upper n) (.inter (.var (lower n)) (.var (lower n)))) ++
   (GeneralNominalAllocation.equations (lower (n+1)) (.union (.var (lower n)) (.var (lower n))) ++
   GeneralNominalAllocation.equations (upper n) (.inter (.var (lower n)) (.var (lower n)))))
 exact List.mem_append_left _ (List.mem_append_left _ member)

theorem replay_lower : HasLowerEquation n
 (GeneralNominalVersionedInstallation231.replayPlan (plan n allocated reserved ordinary)).packet.context.state.ordinary := by
 intro atom member
 change atom ∈ ordinary ++ GeneralNominalVersionedInstallation231.atoms (packet n allocated reserved ordinary)
 apply List.mem_append_right
 apply List.mem_append_left
 apply List.mem_append_right
 exact lower_in_merges n allocated reserved ordinary member
end Yulang.GeneralDictionaryVersionLoopFamilyInstallation238
