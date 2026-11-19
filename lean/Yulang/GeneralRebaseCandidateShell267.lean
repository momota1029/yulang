import Yulang.GeneralRebaseExecutableGenerated267
import Yulang.GeneralNominalVersionedMixedKernel234

namespace Yulang.GeneralRebaseCandidateShell267
open GeneralDeclarations (Registry Declaration DeclarationChecked)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalSaturationState (Generated)
open GeneralRebaseExecutableGenerated267 (discover discover_exact)

def declarations (registry : Registry) (focus : Occurrence roles) : List Declaration :=
 registry.declarations.filter fun declaration => declaration.role == focus.demand.role

theorem declarations_exact (registry : Registry) (focus : Occurrence roles) (declaration : Declaration) :
 declaration ∈ declarations registry focus ↔ declaration ∈ registry.declarations ∧ declaration.role = focus.demand.role := by
 simp [declarations]

def candidates (registry : Registry) (state : State roles) (root : Occurrence roles) :
 List (Occurrence roles × Declaration) :=
 (discover state.core.erased.current root).flatMap fun focus =>
   (declarations registry focus).map fun declaration => (focus,declaration)

theorem candidates_exact (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (declaration : Declaration) : (focus,declaration) ∈ candidates registry state root ↔
 Generated state.core.erased.current root focus ∧ declaration ∈ registry.declarations ∧
 declaration.role = focus.demand.role := by
 constructor
 · intro present
   obtain ⟨other,seen,located⟩ := List.mem_flatMap.mp present
   obtain ⟨decl,matched,equal⟩ := List.mem_map.mp located
   cases equal
   exact ⟨(discover_exact ..).mp seen,(declarations_exact ..).mp matched⟩
 · rintro ⟨generated,inside,role⟩
   exact List.mem_flatMap.mpr ⟨focus,(discover_exact ..).mpr generated,
     List.mem_map.mpr ⟨declaration,(declarations_exact ..).mpr ⟨inside,role⟩,rfl⟩⟩

/-- No installation guard is decided here. Its proof gives inversion:
the complete structural list contains every real install candidate. -/
theorem covers_install (registry : Registry) (state : State roles) (root : Occurrence roles)
 (effect : Effect roles)
 (generated : Generated state.core.erased.current root effect.plan.packet.site.occurrence)
 (guard : GeneralNominalVersionedMixedKernel234.Installable registry state effect) :
 (effect.plan.packet.site.occurrence,effect.plan.packet.declaration) ∈ candidates registry state root := by
 apply (candidates_exact ..).mpr
 exact ⟨generated,guard.registry_eq ▸ effect.frame.visible,effect.frame.role_eq⟩

end Yulang.GeneralRebaseCandidateShell267
