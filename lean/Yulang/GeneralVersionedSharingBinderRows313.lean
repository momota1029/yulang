import Yulang.GeneralVersionedBinderTargets312

set_option backward.isDefEq.respectTransparency false
/-! Exact binder-write table from real same-name sharing, independent of
whether a historical dictionary was installed. -/
namespace Yulang.GeneralVersionedSharingBinderRows313
open GeneralNominalCenters GeneralNominalMaterialization
open GeneralNominalRecursiveInspection (Origin Observes)
open GeneralNominalOriginTerms (Same)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedFrame231 (binder)
open GeneralNominalVersionedPlans231 (SchemaHolds)
open GeneralFiniteTypedWrites312 (Write Coherent Protected Holds applyWrites transitive symmetric reflexive)
open GeneralVersionedAliasHeadWrites312 (pool source_retarget)
open GeneralDictionaryHeadSharing220 (holds_iff)
open CommonNominalFullCarrier (Equivalent)

def Tests (plan : Plan roles) (m : Assignment) : Prop :=
  ∀ test ∈ plan.headSchema.tests, GeneralNominalOriginTerms.Head m test.1 test.2

theorem observed {plan : Plan roles} {m : Assignment}
    (sharing : GeneralDictionaryHeadSharing220.Holds plan m)
    (use : Use) (present : use ∈ plan.headSchema.variables) :
    ∃ t, Observes m use.origin t :=
  ((holds_iff plan m).mp sharing use present use present rfl).1

noncomputable def read (plan : Plan roles) (m : Assignment)
    (sharing : GeneralDictionaryHeadSharing220.Holds plan m) (use : Use)
    (present : use ∈ plan.headSchema.variables) :=
  Classical.choose (observed sharing use present)

theorem read_present (plan : Plan roles) (m : Assignment)
    (sharing : GeneralDictionaryHeadSharing220.Holds plan m) (use : Use)
    (present : use ∈ plan.headSchema.variables) :
    Observes m use.origin (read plan m sharing use present) :=
  Classical.choose_spec (observed sharing use present)

noncomputable def rows (plan : Plan roles) (m : Assignment)
    (sharing : GeneralDictionaryHeadSharing220.Holds plan m) : List Write :=
  plan.headSchema.variables.attach.map fun use => (binder plan use.val.name,read plan m sharing use.val use.property)

theorem row_iff (plan : Plan roles) (m : Assignment)
    (sharing : GeneralDictionaryHeadSharing220.Holds plan m) (row : Write) :
    row ∈ rows plan m sharing ↔ ∃ use, ∃ present : use ∈ plan.headSchema.variables,
      (binder plan use.name,read plan m sharing use present) = row := by
  simp only [rows,List.mem_map]
  constructor
  · rintro ⟨⟨use,present⟩,_,eq⟩
    exact ⟨use,present,eq⟩
  · rintro ⟨use,present,eq⟩
    exact ⟨⟨use,present⟩,by simp,eq⟩

theorem observations_agree (plan : Plan roles) (m : Assignment)
    (sharing : GeneralDictionaryHeadSharing220.Holds plan m) (a b : Use)
    (one : a ∈ plan.headSchema.variables) (two : b ∈ plan.headSchema.variables)
    (equal : a.name = b.name) : Equivalent (read plan m sharing a one) (read plan m sharing b two) :=
  ((holds_iff plan m).mp sharing a one b two equal).2.2 _ _
    (read_present plan m sharing a one) (read_present plan m sharing b two)

theorem schema_after (plan : Plan roles) (m : Assignment) (names : List Nat)
    (sharing : GeneralDictionaryHeadSharing220.Holds plan m) (tests : Tests plan m)
    (coherent : Coherent (rows plan m sharing))
    (fixed : Protected (rows plan m sharing) (pool plan names) m) :
    let next := applyWrites (rows plan m sharing) (pool plan names) m
    SchemaHolds plan plan.headSchema next := by
  let next := applyWrites (rows plan m sharing) (pool plan names) m
  have keeps := GeneralFiniteTypedWrites312.preserved (rows plan m sharing) (pool plan names) m
  have solved := GeneralFiniteTypedWrites312.solves (rows plan m sharing) (pool plan names) m coherent fixed
  constructor
  · intro test inTests
    have used : originSource test.1 ∈ plan.headSchema.tests.map (fun t => originSource t.1) :=
      List.mem_map.mpr ⟨test,inTests,rfl⟩
    exact (GeneralNominalCenteredFrame179.head_iff test.1 test.2 (keeps _ (by simp [pool,used]))).mp (tests test inTests)
  · intro use present
    have used : originSource use.origin ∈ plan.headSchema.variables.map (fun u => originSource u.origin) :=
      List.mem_map.mpr ⟨use,present,rfl⟩
    let row := (binder plan use.name,read plan m sharing use present)
    have listed : row ∈ rows plan m sharing := (row_iff ..).mpr ⟨use,present,rfl⟩
    have target : Equivalent (next (binder plan use.name)).1 (read plan m sharing use present) := solved row listed
    simp only [GeneralNominalHeadSchemaNames186.head_actual plan use present,ite_true]
    constructor
    · exact ⟨_,(GeneralNominalCenteredFrame179.observes_iff use.origin (keeps _ (by simp [pool,used])) _).mp
        (read_present plan m sharing use present)⟩
    · refine ⟨⟨_,.source _⟩,?_⟩
      intro a b actual found
      cases found
      have earlier := (GeneralNominalCenteredFrame179.observes_iff use.origin (keeps _ (by simp [pool,used])) _).mpr actual
      have same := ((holds_iff plan m).mp sharing use present use present rfl).2.2 _ _
        earlier (read_present plan m sharing use present)
      exact transitive same (symmetric target)

end Yulang.GeneralVersionedSharingBinderRows313
