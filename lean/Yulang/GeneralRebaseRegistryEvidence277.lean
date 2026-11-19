import Yulang.GeneralRebaseRegistrySurface277

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRegistryEvidence277
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedEvidence231 (Frame Certificate Instance Evidence)
open GeneralRebaseCompiledRetag277 (retag children_eq holds)
open GeneralRebaseRegistrySurface277 (Surface prepared symmetric)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralNominalCenteredHeadMatEffects (compileBody bodySchema bodyVariables BodyHolds)

theorem compile_body (p : Plan roles) (b : Registry) (ctors) (body : Body) :
    compileBody (retag p b ctors) body = compileBody p body := by
  cases body with
  | explicit equation =>
    change GeneralNominalCenteredHeadMatExpressions.translate b.constructors _ _ =
      GeneralNominalCenteredHeadMatExpressions.translate p.packet.registry.constructors _ _
    rw [ctors]
    rfl
  | default _ _ term =>
    change GeneralNominalCenteredHeadMatExpressions.translateDefault b.constructors _ _ =
      GeneralNominalCenteredHeadMatExpressions.translateDefault p.packet.registry.constructors _ _
    rw [ctors]
    rfl

theorem body_schema (p : Plan roles) (b : Registry) (ctors) (target : Nat) (body : Body) :
    bodySchema (retag p b ctors) target body = bodySchema p target body := by
  unfold bodySchema
  rw [compile_body]

theorem body_variables (p : Plan roles) (b : Registry) (ctors) (m : Assignment) (body : Body) :
    bodyVariables (retag p b ctors) m body = bodyVariables p m body := by
  cases body <;> rfl

theorem body_holds (p : Plan roles) (b : Registry) (ctors) (target : Nat) (m : Assignment) (body : Body) :
    BodyHolds (retag p b ctors) target m body ↔ BodyHolds p target m body := by
  unfold BodyHolds
  rw [body_schema,body_variables]

theorem output (p : Plan roles) (b : Registry) (ctors) (m : Assignment)
    (request : GeneralSourceState.Output) :
    GeneralDictionaryDefaultEvidence204.OutputWitness (retag p b ctors) m request ↔
      GeneralDictionaryDefaultEvidence204.OutputWitness p m request := by
  unfold GeneralDictionaryDefaultEvidence204.OutputWitness
  simp only [compile_body,body_holds]
  rfl

theorem frame {p : Plan roles} (s : Surface a b state.erased.current.context root)
    (one : Frame a state root key p) :
    Frame b state root key (retag p b (s.constructors.symm.trans (congrArg Registry.constructors one.registry_eq).symm)) := by
  exact ⟨rfl,one.context_eq,one.occurrence_eq,one.key_eq,one.raw_recorded,one.center_recorded,
    (s.visible _ one.role_eq).mp one.visible,one.role_eq,one.located,(prepared s one.role_eq).mp one.prepared⟩

theorem certificate {p : Plan roles} (s : Surface a b state.erased.current.context root)
    (one : Certificate a state m root key kids p) :
    Certificate b state m root key kids
      (retag p b (s.constructors.symm.trans (congrArg Registry.constructors one.frame.registry_eq).symm)) := by
  have ct : b.constructors = p.packet.registry.constructors :=
    s.constructors.symm.trans (congrArg Registry.constructors one.frame.registry_eq).symm
  refine ⟨frame s one.frame,one.children_eq.trans (children_eq p.packet b ct).symm,
    (holds p b ct m).mpr one.packet,?_⟩
  intro req member
  exact (output p b ct m req).mpr (one.outputs req member)

theorem instance_forward (s : Surface a b state.erased.current.context root)
    (one : Instance a state m root key kids) : Instance b state m root key kids := by
  obtain ⟨p,valid⟩ := one
  exact ⟨_,certificate s valid⟩

theorem instance_iff (s : Surface a b state.erased.current.context root) :
    Instance a state m root key kids ↔ Instance b state m root key kids :=
  ⟨instance_forward s,instance_forward (symmetric s)⟩

/-- Finite recursive evidence preserves actual chosen occurrences, order,
multiplicities, and explicit/default output provenance. This statement still
requires a checked surface for all occurrences at the paired context. -/
theorem evidence {roles : Roles.RoleDecls} {a b : Registry}
    {state : GeneralNominalCenteredSteps.State roles} {m : Assignment}
    (surfaces : ∀ root : Occurrence roles, Surface a b state.erased.current.context root)
    (root : Occurrence roles) (data : GeneralDictionaryReadback.Payload) :
    Evidence a state m root data ↔ Evidence b state m root data := by
  have eq : Instance a state m = Instance b state m := by
    funext root key kids
    exact propext (instance_iff (surfaces root))
  unfold GeneralNominalVersionedEvidence231.Evidence
  rw [eq]

end Yulang.GeneralRebaseRegistryEvidence277
