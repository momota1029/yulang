import Yulang.GeneralDictionaryDefaultFrame209

/-! Exact source reconstruction for the total/default evidence judgment.
This establishes representation soundness, not production of evidence. -/
namespace Yulang.GeneralDictionaryDefaultReadback209
open GeneralDeclarations GeneralSourceDictionaries
open GeneralDictionaryTotalEvidence206 (Instance)
open GeneralDictionaryReadback (Payload PayloadEvidence)
variable {roles : Roles.RoleDecls}

 theorem unique_readback (checked : Checked registry)
    (given : GeneralDictionaryTotalEvidence206.Evidence registry state model focus payload) :
    ∃ tree, (Readback focus payload tree ∧ Evidence (Instance registry state model) tree) ∧
      ∀ other, Readback focus payload other → Evidence (Instance registry state model) other → other = tree :=
  GeneralDictionaryReadback.payload_unique_readback _
    (GeneralDictionaryDefaultFrame209.childrenFunctional checked) _ _
    ((GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr given)

/-- The union is used only to compare representations across assignments; it
is not substituted for the language's model-relative evidence judgment. -/
def AnyModelInstance (registry : Registry) (state : GeneralNominalCenteredSteps.State roles) : LocalInstance roles :=
  fun focus key children => ∃ model, Instance registry state model focus key children

 theorem anyModel_functional (checked : Checked registry) :
    GeneralDictionaryReadback.ChildrenFunctional (AnyModelInstance (roles := roles) registry state) := by
  intro focus key first last one two
  obtain ⟨model,one⟩ := one
  obtain ⟨other,two⟩ := two
  exact GeneralDictionaryDefaultFrame209.instance_children checked one two

 theorem model_independent_readback (checked : Checked registry)
    (one : Readback focus payload first) (two : Readback focus payload last)
    (firstEvidence : Evidence (Instance registry state model) first)
    (lastEvidence : Evidence (Instance registry state otherModel) last) : first = last :=
  GeneralDictionaryReadback.indexed_unique _ (anyModel_functional checked) _ _
    (one.1.trans two.1.symm) (one.2.trans two.2.symm)
    (evidence_mono _ _ (fun _ _ _ h => ⟨model,h⟩) firstEvidence)
    (evidence_mono _ _ (fun _ _ _ h => ⟨otherModel,h⟩) lastEvidence)

 theorem node_iff :
    GeneralDictionaryTotalEvidence206.Evidence registry state model focus (.node key payloads) ↔
      ∃ children, Instance registry state model focus key children ∧
        CommonRoleOutermostResolver.All₂
          (GeneralDictionaryTotalEvidence206.Evidence registry state model) children payloads := by
  constructor
  · intro given
    have payload := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr given
    cases payload with
    | node instanceRule children =>
        refine ⟨_,instanceRule,?_⟩
        clear given instanceRule
        induction children with
        | nil => exact .nil
        | cons first rest ih =>
            exact .cons ((GeneralDictionaryReadback.payload_iff_erased _ _ _).mp first) ih
  · rintro ⟨children,instanceRule,given⟩
    exact GeneralDictionaryTotalEvidence206.evidence_node instanceRule given

/-- A selected current frame fixes the exact ordered source list in any
existing evidence at that node, even in a different witness model. -/
 theorem node_current_frame_iff (checked : Checked registry)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state focus key plan) :
    GeneralDictionaryTotalEvidence206.Evidence registry state model focus (.node key payloads) ↔
      Instance registry state model focus key plan.packet.children ∧
        CommonRoleOutermostResolver.All₂
          (GeneralDictionaryTotalEvidence206.Evidence registry state model) plan.packet.children payloads := by
  rw [node_iff]
  constructor
  · rintro ⟨children,instanceRule,given⟩
    obtain ⟨other,cert⟩ := instanceRule
    have equal := cert.children_eq.trans (GeneralDictionaryDefaultFrame209.frame_children checked cert.frame frame)
    exact equal ▸ ⟨⟨other,cert⟩,given⟩
  · rintro ⟨instanceRule,given⟩
    exact ⟨_,instanceRule,given⟩

end Yulang.GeneralDictionaryDefaultReadback209
