import Yulang.GeneralNominalRebaseOriginView243
import Yulang.GeneralPresenceOrderedSubstitution247
import Yulang.GeneralPresenceOrderedDependence247
import Yulang.GeneralPresenceCommonLaws245

/-! Actual origin-path transport through finite ordered definition readback.
Source witnesses may change representative; projected witnesses are preserved
literally. This is not an all-metadata adapter or a source reachability result. -/
namespace Yulang.GeneralNominalOrderedOrigin248
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedDependence247
open GeneralPresenceModelCongruence245 GeneralPresenceOrderedRecovery247
open GeneralPresenceCommonLaws245
open GeneralNominalRebaseOriginView243
open GeneralNominalRecursiveInspection (Test)

theorem equiv_refl (value : Ty) : Equivalent value value :=
 ⟨subtype_refl _,subtype_refl _⟩
theorem equiv_symm (h : Equivalent a b) : Equivalent b a := ⟨h.2,h.1⟩
theorem equiv_trans (h : Equivalent a b) (k : Equivalent b c) : Equivalent a c :=
 ⟨subtype_trans h.1 k.1,subtype_trans k.2 h.2⟩

theorem compatible_symm (h : Compatible model first last) : Compatible model last first :=
 fun name => ⟨⟨(h name).1.2,(h name).1.1⟩,(h name).2.symm⟩

theorem read_mapping (entries : List (Entry Nat)) (assignment : Assignment) :
 GeneralNominalRebaseRawView243.read (mapping entries) assignment = solve model entries assignment :=
 funext (mapping_eval entries model assignment)

theorem compile_ordered_exact (entries : List (Entry Nat)) (assignment : Assignment)
 (origin : GeneralNominalRecursiveInspection.Origin) (actual : Ty) :
 Observes assignment (compile (mapping entries) origin) actual ↔
 GeneralNominalRecursiveInspection.Observes (solve model entries assignment) origin actual := by
 rw [compile_exact,read_mapping]

theorem subst_ordered_exact (entries : List (Entry Nat)) (assignment : Assignment)
 (origin : Origin) (actual : Ty) :
 Observes assignment (subst (mapping entries) origin) actual ↔
 Observes (solve model entries assignment) origin actual := by
 rw [subst_exact,read_mapping]

theorem observes_transport (same : Compatible model first last)
 (seen : Observes first origin actual) :
 ∃ other, Observes last origin other ∧ Equivalent actual other := by
 induction seen with
 | source term =>
   exact ⟨_,.source term,type_eval_equiv model common_laws first last same term⟩
 | nominal seen equal found ih =>
   obtain ⟨other,observed,equivalent⟩ := ih
   exact ⟨_,.nominal observed (equiv_trans (equiv_symm equivalent) equal) found,equiv_refl _⟩
 | structural seen length equal found ih =>
   obtain ⟨other,observed,equivalent⟩ := ih
   exact ⟨_,.structural observed length (equiv_trans (equiv_symm equivalent) equal) found,equiv_refl _⟩

theorem nominal_transport (same : Compatible model first last)
 (seen : Observes first (.nominal parent name index) actual) :
 Observes last (.nominal parent name index) actual := by
 cases seen with
 | nominal before equal found =>
   obtain ⟨other,observed,equivalent⟩ := observes_transport same before
   exact .nominal observed (equiv_trans (equiv_symm equivalent) equal) found

theorem structural_transport (same : Compatible model first last)
 (seen : Observes first (.structural parent shape index) actual) :
 Observes last (.structural parent shape index) actual := by
 cases seen with
 | structural before length equal found =>
   obtain ⟨other,observed,equivalent⟩ := observes_transport same before
   exact .structural observed length (equiv_trans (equiv_symm equivalent) equal) found

theorem nominal_iff (same : Compatible model first last) :
 Observes first (.nominal parent name index) actual ↔
 Observes last (.nominal parent name index) actual :=
 ⟨nominal_transport same,nominal_transport (compatible_symm same)⟩

theorem structural_iff (same : Compatible model first last) :
 Observes first (.structural parent shape index) actual ↔
 Observes last (.structural parent shape index) actual :=
 ⟨structural_transport same,structural_transport (compatible_symm same)⟩

theorem test_transport (same : Equivalent first last) (test : Test)
 (holds : test.Holds first) : test.Holds last := by
 cases test with
 | scalar base => exact equiv_trans (equiv_symm same) holds
 | structural shape =>
   obtain ⟨values,length,equal⟩ := holds
   exact ⟨values,length,equiv_trans (equiv_symm same) equal⟩
 | nominal name arity =>
   obtain ⟨arguments,length,equal⟩ := holds
   exact ⟨arguments,length,equiv_trans (equiv_symm same) equal⟩

theorem test_iff (same : Equivalent first last) (test : Test) :
 test.Holds first ↔ test.Holds last :=
 ⟨test_transport same test,test_transport (equiv_symm same) test⟩

theorem head_transport (same : Compatible model first last)
 (holds : Head first origin test) : Head last origin test := by
 constructor
 · obtain ⟨value,seen⟩ := holds.1
   obtain ⟨other,observed,_⟩ := observes_transport same seen
   exact ⟨other,observed⟩
 · intro value seen
   obtain ⟨other,observed,equal⟩ := observes_transport (compatible_symm same) seen
   exact test_transport (equiv_symm equal) test (holds.2 other observed)

theorem head_iff (same : Compatible model first last) :
 Head first origin test ↔ Head last origin test :=
 ⟨head_transport same,head_transport (compatible_symm same)⟩

theorem same_transport (compatible : Compatible model first last)
 (holds : Same first left right) : Same last left right := by
 refine ⟨?_,?_,?_⟩
 · obtain ⟨value,seen⟩ := holds.1
   obtain ⟨other,observed,_⟩ := observes_transport compatible seen
   exact ⟨other,observed⟩
 · obtain ⟨value,seen⟩ := holds.2.1
   obtain ⟨other,observed,_⟩ := observes_transport compatible seen
   exact ⟨other,observed⟩
 · intro a b seenA seenB
   obtain ⟨a',observedA,equalA⟩ := observes_transport (compatible_symm compatible) seenA
   obtain ⟨b',observedB,equalB⟩ := observes_transport (compatible_symm compatible) seenB
   exact equiv_trans equalA (equiv_trans (holds.2.2 a' b' observedA observedB) (equiv_symm equalB))

theorem same_iff (compatible : Compatible model first last) :
 Same first left right ↔ Same last left right :=
 ⟨same_transport compatible,same_transport (compatible_symm compatible)⟩

theorem nominal_rebase (old fresh : List (Entry Nat)) (safe : SafeOrder old)
 (within : TargetsWithin fresh old) (assignment : Assignment)
 (valid : All model assignment (block old)) (parent : Origin) (name index : Nat) (actual : Ty) :
 Observes (solve model fresh assignment) (subst (mapping old) (.nominal parent name index)) actual ↔
 Observes assignment (.nominal parent name index) actual := by
 rw [subst_ordered_exact,solve_absorbs model old fresh safe within]
 exact nominal_iff (solve_compatible model common_laws old assignment valid)

theorem structural_rebase (old fresh : List (Entry Nat)) (safe : SafeOrder old)
 (within : TargetsWithin fresh old) (assignment : Assignment)
 (valid : All model assignment (block old)) (parent : Origin) (shape : Shape) (index : Nat) (actual : Ty) :
 Observes (solve model fresh assignment) (subst (mapping old) (.structural parent shape index)) actual ↔
 Observes assignment (.structural parent shape index) actual := by
 rw [subst_ordered_exact,solve_absorbs model old fresh safe within]
 exact structural_iff (solve_compatible model common_laws old assignment valid)

theorem head_rebase (old fresh : List (Entry Nat)) (safe : SafeOrder old)
 (within : TargetsWithin fresh old) (assignment : Assignment)
 (valid : All model assignment (block old)) (origin : Origin) (test : Test) :
 Head (solve model fresh assignment) (subst (mapping old) origin) test ↔ Head assignment origin test := by
 rw [head_subst,read_mapping,solve_absorbs model old fresh safe within]
 exact head_iff (solve_compatible model common_laws old assignment valid)

theorem same_rebase (old fresh : List (Entry Nat)) (safe : SafeOrder old)
 (within : TargetsWithin fresh old) (assignment : Assignment)
 (valid : All model assignment (block old)) (left right : Origin) :
 Same (solve model fresh assignment) (subst (mapping old) left) (subst (mapping old) right) ↔
 Same assignment left right := by
 rw [same_subst,read_mapping,solve_absorbs model old fresh safe within]
 exact same_iff (solve_compatible model common_laws old assignment valid)

/- General origins retain equivalent observations, not necessarily the same
source syntax representative. -/
theorem observes_rebase_forward (old fresh : List (Entry Nat)) (safe : SafeOrder old)
 (within : TargetsWithin fresh old) (assignment : Assignment)
 (valid : All model assignment (block old)) (origin : Origin) (actual : Ty)
 (seen : Observes assignment origin actual) :
 ∃ other, Observes (solve model fresh assignment) (subst (mapping old) origin) other ∧
   Equivalent actual other := by
 obtain ⟨other,observed,equal⟩ := observes_transport
   (compatible_symm (solve_compatible model common_laws old assignment valid)) seen
 refine ⟨other,?_,equal⟩
 rw [subst_ordered_exact,solve_absorbs model old fresh safe within]
 exact observed

theorem observes_rebase_backward (old fresh : List (Entry Nat)) (safe : SafeOrder old)
 (within : TargetsWithin fresh old) (assignment : Assignment)
 (valid : All model assignment (block old)) (origin : Origin) (actual : Ty)
 (seen : Observes (solve model fresh assignment) (subst (mapping old) origin) actual) :
 ∃ other, Observes assignment origin other ∧ Equivalent actual other := by
 rw [subst_ordered_exact,solve_absorbs model old fresh safe within] at seen
 exact observes_transport (solve_compatible model common_laws old assignment valid) seen
end Yulang.GeneralNominalOrderedOrigin248
