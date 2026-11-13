import Yulang.GeneralDictionaryActualSchemaOrigin
import Yulang.GeneralDictionarySemanticCollapseExample

/-! Positive materialization-only regression with two different request target
IDs, a noninjective rename, and a nonempty capture origin. This does not claim
that an operational allocator produces this rename or these branch reports. -/
namespace Yulang.GeneralDictionaryActualSchemaOriginExample
open GeneralDictionaryActualSchemaOrigin GeneralNominalMaterialization
open GeneralNominalRecursiveInspection GeneralDeclarations GeneralDeclarationPatterns
open CommonNominalFullCarrier
abbrev state := GeneralDictionarySemanticCollapseExample.source
abbrev interpretation := GeneralDictionarySemanticCollapseExample.interpretation
abbrev declaration : Declaration := ⟨42,0,[.var 7],[],[],[]⟩
abbrev model : GeneralNominalCommonBridge.Assignment := fun _ => (.base .int,Common.rowEmpty)
abbrev capture : GeneralDeclarationDemands.Capture := ⟨fun _ => (0,1),fun _ => 0⟩
abbrev requests : List Request := [⟨.var 7,0,.actual⟩,⟨.var 7,1,.actual⟩]
abbrev rename : Nat → Nat := fun _ => 10
abbrev oldReport : Report state := { captures := [⟨7,(0,0),some (.source 0)⟩] }
abbrev newReport : Report state := { captures := [⟨7,(0,0),some (.source 10)⟩] }
abbrev body : Schema := ⟨[⟨7,.source 0,.actual⟩,⟨7,.source 1,.actual⟩],[],false⟩

theorem generated_body : generated state interpretation requests = body := by
  simp [generated,requests,normalize,GeneralNominalInspection.translate,schema,Schema.append,body]

theorem changed_targets : (requests.map (renameRequest rename)).map Request.target = [10,10] := rfl

theorem literal_schema_differs : renameSchema rename body ≠ body := by
  intro same
  have same := congrArg (fun s => s.variables.head?.map Use.origin) same
  change some (Origin.source 10) = some (Origin.source 0) at same
  cases same

theorem old_models : Models state declaration capture oldReport body model := by
  refine ⟨?_,?_,?_,?_⟩
  · intro test member; cases member
  · intro entry member
    have casesEntry : entry = ⟨7,.source 0,.actual⟩ ∨ entry = ⟨7,.source 1,.actual⟩ := by
      simpa [body] using member
    rcases casesEntry with rfl | rfl
    all_goals
      refine ⟨⟨_,.source _⟩,?_⟩
      intro actual seen
      cases seen
      exact ⟨subtype_refl _,subtype_refl _⟩
  · intro first one last two _ _ _ a b seenA seenB
    have f : first = ⟨7,.source 0,.actual⟩ ∨ first = ⟨7,.source 1,.actual⟩ := by simpa [body] using one
    have l : last = ⟨7,.source 0,.actual⟩ ∨ last = ⟨7,.source 1,.actual⟩ := by simpa [body] using two
    rcases f with rfl | rfl <;> rcases l with rfl | rfl
    all_goals cases seenA; cases seenB; exact ⟨subtype_refl _,subtype_refl _⟩
  · intro entry member captured present _ _ origin known a b seen observed
    have hcap : captured = ⟨7,(0,0),some (.source 0)⟩ := List.mem_singleton.mp present
    subst captured
    have originEq := Option.some.inj known
    subst origin
    cases observed
    have e : entry = ⟨7,.source 0,.actual⟩ ∨ entry = ⟨7,.source 1,.actual⟩ := by simpa [body] using member
    rcases e with rfl | rfl
    all_goals cases seen; exact ⟨subtype_refl _,subtype_refl _⟩

/-- Full Models for the real generated retargeted requests, not just a
standalone variable equation. Includes repeated-name and capture-origin sharing. -/
theorem retargeted_models : Models state declaration capture newReport
    (generated state interpretation (requests.map (renameRequest rename))) model := by
  rw [← generated_rename,generated_body]
  apply replay declaration capture capture oldReport newReport body rename model
  · intro n; exact ⟨subtype_refl _,subtype_refl _⟩
  · intro entry member
    have e : entry = ⟨7,.source 0,.actual⟩ ∨ entry = ⟨7,.source 1,.actual⟩ := by simpa [body] using member
    rcases e with rfl | rfl <;> rfl
  · intro _ _; exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ _ _ h; exact h
  · intro captured present origin known
    have hcap : captured = ⟨7,(0,0),some (.source 10)⟩ := List.mem_singleton.mp present
    subst captured
    have originEq := Option.some.inj known
    subst origin
    exact ⟨⟨7,(0,0),some (.source 0)⟩,by simp,rfl,.source 0,rfl,rfl⟩
  · exact old_models
end Yulang.GeneralDictionaryActualSchemaOriginExample
