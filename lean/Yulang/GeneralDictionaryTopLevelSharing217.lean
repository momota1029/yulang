import Yulang.GeneralDictionarySharingObstruction217

/-! A finite, plan-independent obstruction check for a two-argument repeated
variable head. It does not assert that a stable reachable fixture exists. -/
namespace Yulang.GeneralDictionaryTopLevelSharing217
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalMaterialization GeneralNominalRecursiveInspection
open GeneralNominalOriginTerms
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls}

def firstCenter (site : Site roles) : Nat := (List.ofFn site.center)[0]?.getD 0
def secondCenter (site : Site roles) : Nat := (List.ofFn site.center)[1]?.getD 0

theorem schema_same (plan : Plan roles) (model : Assignment) (name : Nat)
    (queries : GeneralNominalInspection.queries plan.packet.context.state
      plan.packet.context.interpretation plan.packet.declaration = [.variables [name],.variables [name]])
    (held : plan.SchemaHolds plan.headSchema model) :
    Same model (.source (firstCenter plan.input)) (.source (secondCenter plan.input)) := by
  have left := held.2 ⟨name,.source (firstCenter plan.input),.actual⟩
  have right := held.2 ⟨name,.source (secondCenter plan.input),.actual⟩
  simp only [Plan.headSchema,queries,schemas,schema,Schema.append,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,firstCenter,secondCenter] at left right
  have one := left (by simp)
  have two := right (by simp)
  simp only [ite_true] at one two
  exact same_trans one (same_symm two)

theorem impossible (registry : Registry) (state : GeneralNominalCenteredHeadMatStepJournal.State roles)
    (model : Assignment) (root : Occurrence roles) (key name : Nat)
    (queries : ∀ declaration ∈ registry.declarations, declaration.id = key →
      GeneralNominalInspection.queries state.core.erased.current.context.state
        state.core.erased.current.context.interpretation declaration = [.variables [name],.variables [name]])
    (different : ∀ site ∈ state.core.sites, site.occurrence = root →
      ¬ Same model (.source (firstCenter site)) (.source (secondCenter site))) :
    GeneralDictionarySharingObstruction217.Impossible registry state.core model root key := by
  intro plan frame agreement
  have q := queries plan.packet.declaration frame.visible frame.key_eq
  rw [← frame.context_eq] at q
  have one : (⟨name,.source (firstCenter plan.input),.actual⟩ : Use) ∈ plan.headSchema.variables := by
    simp [Plan.headSchema,q,schemas,schema,Schema.append,firstCenter]
  have two : (⟨name,.source (secondCenter plan.input),.actual⟩ : Use) ∈ plan.headSchema.variables := by
    simp [Plan.headSchema,q,schemas,schema,Schema.append,secondCenter]
  exact different plan.input frame.center_recorded (plan.input_exact.trans frame.occurrence_eq)
    (GeneralDictionaryCurrentAgreement217.use_same plan
      (GeneralDictionaryDefaultRevisit214.frame_finished frame) agreement _ _ one two rfl)
end Yulang.GeneralDictionaryTopLevelSharing217
