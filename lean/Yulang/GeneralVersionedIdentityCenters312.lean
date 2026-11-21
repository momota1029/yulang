import Yulang.GeneralVersionedSiteOrigins312
import Yulang.GeneralDictionaryDefaultAliasCenters215

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
/-! An invocation denotes the same actual centers in any one live journal
model, even across installations with different observation versions. -/
namespace Yulang.GeneralVersionedIdentityCenters312
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralVersionedSiteOrigins312 (TraceData stored_finished stored_visible emitted_origin emitted_above)
open GeneralNominalVersionedFrame231 (childSite)
open GeneralNominalVersionedPlans231 (Holds SchemaHolds)
open GeneralNominalOriginTerms (Same)
open GeneralDictionaryDefaultIdentityCenters214 (CentersSame centers_self)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem head_actual_iff (plan : Plan roles) (m : Assignment) :
    SchemaHolds plan plan.headSchema m ↔ plan.SchemaHolds plan.headSchema m := by
  constructor <;> rintro ⟨tests,uses⟩ <;> refine ⟨tests,?_⟩
  all_goals
    intro entry present
    have tag := GeneralNominalHeadSchemaNames186.head_actual plan entry present
    simpa only [tag,ite_true,GeneralNominalVersionedFrame231.binder_eq] using uses entry present

theorem binders_same
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (data : TraceData root ctx state)
    (first last : Plan roles) (one : first ∈ state.plans) (two : last ∈ state.plans)
    (decl : first.packet.declaration = last.packet.declaration)
    (same : CentersSame m first.input last.input) (valid : Models state m)
    (name : Nat) (named : name ∈ first.packet.declaration.inputNames) :
    Same m (.source (first.binder name)) (.source (last.binder name)) := by
  have cfgA := data.configuration first one
  have cfgB := data.configuration last two
  exact GeneralNominalHeadSchemaSemantic186.binder_same first last decl
    (cfgA.2.1.trans cfgB.2.1.symm) (cfgA.2.2.trans cfgB.2.2.symm) same
    ((head_actual_iff first m).mp (GeneralNominalVersionedDiagnostic232.head_equations (valid.2.1 first one)).2.2)
    ((head_actual_iff last m).mp (GeneralNominalVersionedDiagnostic232.head_equations (valid.2.1 last two)).2.2)
    (stored_finished path one) name named

private theorem child_congr (plan : Plan roles) {a b : Clause} (same : a = b)
    (one : a.Signature roles) (two : b.Signature roles) :
    childSite plan a one = childSite plan b two := by cases same; rfl

theorem centers_of_emission (first last : Plan roles) (m : Assignment)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (invocation : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (clause : Clause) (member : clause ∈ first.packet.declaration.requirements)
    (signature : clause.Signature roles)
    (binders : ∀ name ∈ first.packet.declaration.inputNames,
      Same m (.source (first.binder name)) (.source (last.binder name))) :
    CentersSame m (childSite first clause signature) (childSite last clause signature) := by
  intro index
  have equal (p : Plan roles) :
      List.ofFn (childSite p clause signature).center = List.ofFn (p.childSite clause signature).center := by
    congr 1
    funext i
    exact GeneralNominalVersionedFrame231.childSite_center_eq p clause signature i
  rw [equal first,equal last]
  exact GeneralNominalChildSemantic186.child_centers_list first last seed invocation declaration
    clause member signature m binders index

theorem same_identity
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (valid : Models state m) (first last : Site roles)
    (one : first ∈ state.core.sites) (two : last ∈ state.core.sites)
    (identity : first.occurrence.identity = last.occurrence.identity) :
    CentersSame m first last := by
  obtain ⟨ctx,data⟩ := GeneralVersionedSiteOrigins312.reached path
  have identityInduction : ∀ n, ∀ first last : Site roles,
      first ∈ state.core.sites → last ∈ state.core.sites →
      first.occurrence.identity = n →
      first.occurrence.identity = last.occurrence.identity → CentersSame m first last := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro first last one two atNumber identity
      rcases data.origin first one with rfl|⟨a,ha,ea⟩
      · rcases data.origin last two with rfl|⟨b,hb,eb⟩
        · exact centers_self m _
        · have parent := data.root_le b.input (data.input b hb)
          rw [b.input_exact] at parent
          have above := Nat.lt_of_le_of_lt parent (emitted_above eb)
          exact False.elim (Nat.lt_irrefl _ (identity ▸ above))
      · rcases data.origin last two with rfl|⟨b,hb,eb⟩
        · have parent := data.root_le a.input (data.input a ha)
          rw [a.input_exact] at parent
          have above := Nat.lt_of_le_of_lt parent (emitted_above ea)
          exact False.elim (Nat.lt_irrefl _ (identity ▸ above))
        · obtain ⟨ca,ac,sa,rfl⟩ := emitted_origin ea
          obtain ⟨cb,bc,sb,rfl⟩ := emitted_origin eb
          have seed := (data.configuration a ha).1.trans (data.configuration b hb).1.symm
          obtain ⟨parent,decl,clause⟩ := GeneralNominalChildCoherence184.producer_declarations
            (GeneralNominalCenteredHeadAllocEncoding.registry registry)
            (GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked).2
            a b seed (stored_visible path ha) (stored_visible path hb) ca cb ac bc sa sb identity
          have below : a.input.occurrence.identity < n := by
            rw [a.input_exact,← atNumber]
            exact GeneralVersionedSiteOrigins312.child_above a ca sa
          have same := ih a.input.occurrence.identity below a.input b.input
            (data.input a ha) (data.input b hb) rfl
            ((congrArg Occurrence.identity a.input_exact).trans
              (parent.trans (congrArg Occurrence.identity b.input_exact).symm))
          have readback := binders_same path data a b ha hb decl same valid
          have cbSame := child_congr b clause.symm sb sa
          rw [cbSame]
          exact centers_of_emission a b m seed parent decl ca ac sa readback
  exact identityInduction first.occurrence.identity first last one two rfl identity

end Yulang.GeneralVersionedIdentityCenters312
