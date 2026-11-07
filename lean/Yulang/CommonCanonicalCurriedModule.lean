import Yulang.CommonCanonicalCurriedExports
import Yulang.CommonCanonicalArrowModule

/-!
# Complete fixed-depth curried codes through partial module finalization

The computed family code is paired with the original interface's finite
ambient-support code. This exactly characterizes the existing EOF operation
followed by use of its returned qualified binding, for every partial ambient
assignment and target. No known-slot or successful-finalization premise is
imposed on those assignments.

The curried depth is arbitrary but shared by the compared schemes. Local
arities and input-sharing patterns are unrestricted; domains remain local
variables, results remain scalar lattice expressions, and rows remain fixed
ambient identities. Obligations are empty, so arbitrary visible impl sets
and decoders introduce no extra condition. Raw support is retained exactly
as the current `finishModule` checks it, including absorbed captured mentions.

This completes the partial-EOF comparison left separate in
`CommonCanonicalCurriedExports`. General domains, different depths, nonempty
role obligations, generalized row expressions and inference/display readback
remain outside this closed language.
-/

namespace Yulang.CommonCanonicalCurriedModule

open CommonCanonicalCurriedTransfer (Scheme Instances)
open CommonCanonicalCurriedFamilies (canonicalEncoding)
open CommonCanonicalArrowExports (model Ambient)
open CommonCanonicalCurriedExports (toInterface)
open CommonCanonicalArrowModule (ambientInventory missing)
open Inference (Comp)
open QualifiedInference (Interface BindingTyping)

variable {fixed rowSlots arguments generalized other : Nat}

def supportCode (scheme : Scheme fixed rowSlots arguments generalized) : List (Ambient fixed rowSlots) :=
  (ambientInventory fixed rowSlots).filter fun index => decide (index ∈ (toInterface scheme).support)

@[simp] theorem mem_supportCode (scheme : Scheme fixed rowSlots arguments generalized) (index : Ambient fixed rowSlots) :
    index ∈ supportCode scheme ↔ index ∈ (toInterface scheme).support := by
  simp [supportCode]

theorem supportCode_exact (first : Scheme fixed rowSlots arguments generalized)
    (last : Scheme fixed rowSlots arguments other) :
    (∀ index, index ∈ (toInterface first).support ↔ index ∈ (toInterface last).support) ↔
      supportCode first = supportCode last := by
  constructor
  · intro same
    have predicates : (fun index => decide (index ∈ (toInterface first).support)) =
        (fun index => decide (index ∈ (toInterface last).support)) := by
      funext index
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using same index
    simp only [supportCode, predicates]
  · intro same index
    rw [← mem_supportCode first index, same, mem_supportCode]

theorem known_missing_iff (scheme : Scheme fixed rowSlots arguments generalized) (index : Ambient fixed rowSlots) :
    (toInterface scheme).known (missing index) = true ↔ index ∉ (toInterface scheme).support := by
  rw [Interface.known, List.all_eq_true]
  constructor
  · intro known member
    have found := known index member
    simp [missing] at found
  · intro absent slot member
    have different : slot ≠ index := fun same => absent (same ▸ member)
    simp [missing, different]

theorem known_iff_of_support (first : Scheme fixed rowSlots arguments generalized)
    (last : Scheme fixed rowSlots arguments other)
    (same : ∀ index, index ∈ (toInterface first).support ↔ index ∈ (toInterface last).support)
    (assignment : Ambient fixed rowSlots → Option (Comp model)) :
    (toInterface first).known assignment = true ↔ (toInterface last).known assignment = true := by
  simp only [Interface.known, List.all_eq_true]
  exact ⟨fun known index member => known index ((same index).mpr member),
    fun known index member => known index ((same index).mp member)⟩

/-- The actual EOF function returns a closed interface, which is then used
by the existing qualified binding judgment. -/
def FinishedInstances (scheme : Scheme fixed rowSlots arguments generalized)
    (decode : model.Ty → Roles.Term) (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (assignment : Ambient fixed rowSlots → Option (Comp model))
    (theory : RoleConstraints.Theory model) (target : Comp model) : Prop :=
  ∃ closed : QualifiedInference.ClosedInterface model generalized,
    QualifiedInference.finishModule model decode impls wf assignment (toInterface scheme) = some closed ∧
      BindingTyping model theory
        (.qualified generalized closed.requirements (fun parameters => Comp.pure model (closed.value parameters))) target

theorem finished_instances_exact (scheme : Scheme fixed rowSlots arguments generalized)
    (decode : model.Ty → Roles.Term) (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (assignment : Ambient fixed rowSlots → Option (Comp model))
    (theory : RoleConstraints.Theory model) (target : Comp model) :
    FinishedInstances scheme decode impls wf assignment theory target ↔
      (toInterface scheme).known assignment = true ∧
        Instances scheme
          (fun index => (QualifiedInference.completeAssignment model assignment (.inr index)).2)
          (fun index => (QualifiedInference.completeAssignment model assignment (.inl index)).1) target.1 := by
  constructor
  · rintro ⟨closed, accepted, typed⟩
    obtain ⟨known, same⟩ :=
      (CommonCanonicalCurriedExports.finishModule_exact scheme decode impls wf assignment closed).mp accepted
    subst closed
    exact ⟨known, (CommonCanonicalCurriedExports.binding_instances_exact scheme theory _ target).mp typed⟩
  · rintro ⟨known, member⟩
    refine ⟨(toInterface scheme).closeAt model (QualifiedInference.completeAssignment model assignment),
      (CommonCanonicalCurriedExports.finishModule_exact scheme decode impls wf assignment _).mpr ⟨known, rfl⟩, ?_⟩
    exact (CommonCanonicalCurriedExports.binding_instances_exact scheme theory _ target).mpr member

theorem finished_total_instances_exact (scheme : Scheme fixed rowSlots arguments generalized)
    (decode : model.Ty → Roles.Term) (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (ambient : Ambient fixed rowSlots → Comp model)
    (theory : RoleConstraints.Theory model) (target : Comp model) :
    FinishedInstances scheme decode impls wf (fun index => some (ambient index)) theory target ↔
      (toInterface scheme).scheme.Holds model theory (Inference.extend ambient target) := by
  rw [finished_instances_exact, CommonCanonicalCurriedExports.scheme_instances_exact]
  simp [Interface.known, QualifiedInference.completeAssignment]

theorem finished_top_iff_known (scheme : Scheme fixed rowSlots arguments generalized)
    (decode : model.Ty → Roles.Term) (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (assignment : Ambient fixed rowSlots → Option (Comp model)) (theory : RoleConstraints.Theory model) :
    FinishedInstances scheme decode impls wf assignment theory (.top, Common.rowEmpty) ↔
      (toInterface scheme).known assignment = true := by
  rw [finished_instances_exact]
  exact ⟨And.left, fun known => ⟨known, fun _ => .bottom, CommonBoundCoalescing.le_top _⟩⟩

def exportCanonicalEncoding (scheme : Scheme fixed rowSlots arguments generalized) :
    CommonCanonicalCurriedFamilies.Code fixed rowSlots arguments × List (Ambient fixed rowSlots) :=
  (canonicalEncoding scheme, supportCode scheme)

/-- Arbitrary shared finite depth, independent generalized arities, arbitrary
decoder and well-formed visible impl set. All partial ambient assignments,
caller theories and targets are quantified without known/success premises. -/
theorem export_canonicalEncoding_exact (first : Scheme fixed rowSlots arguments generalized)
    (last : Scheme fixed rowSlots arguments other)
    (decode : model.Ty → Roles.Term) (impls : List Roles.Impl) (wf : Roles.WellFormed impls) :
    (∀ assignment : Ambient fixed rowSlots → Option (Comp model),
      ∀ theory : RoleConstraints.Theory model, ∀ target : Comp model,
        FinishedInstances first decode impls wf assignment theory target ↔
          FinishedInstances last decode impls wf assignment theory target) ↔
      exportCanonicalEncoding first = exportCanonicalEncoding last := by
  simp only [exportCanonicalEncoding, Prod.mk.injEq]
  constructor
  · intro same
    constructor
    · apply (CommonCanonicalCurriedExports.interface_canonicalEncoding_exact first last).mp
      intro theory ambient target
      simpa only [finished_total_instances_exact] using
        same (fun index => some (ambient index)) theory target
    · apply (supportCode_exact first last).mp
      intro index
      have observed := same (missing index) (fun _ => False) (.top, Common.rowEmpty)
      rw [finished_top_iff_known, finished_top_iff_known, known_missing_iff, known_missing_iff] at observed
      simpa only [Decidable.not_not] using not_congr observed
  · rintro ⟨valueSame, supportSame⟩ assignment theory target
    rw [finished_instances_exact, finished_instances_exact]
    exact and_congr (known_iff_of_support first last ((supportCode_exact first last).mpr supportSame) assignment)
      ((CommonCanonicalCurriedFamilies.canonicalEncoding_exact first last).mpr valueSame _ _ _)

namespace Examples

open CommonCanonicalCurriedFamilies.Examples (shared joined shared_joined_code)

/-- `a -> a -> a` and `a -> b -> a | b` retain equal EOF/use codes even
though one quantifies one type parameter and the other quantifies two. -/
theorem shared_joined_export_code : exportCanonicalEncoding shared = exportCanonicalEncoding joined := by
  exact Prod.ext shared_joined_code (by decide +kernel)

theorem shared_joined_finished_instances (decode : model.Ty → Roles.Term)
    (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (assignment : Ambient 0 1 → Option (Comp model))
    (theory : RoleConstraints.Theory model) (target : Comp model) :
    FinishedInstances shared decode impls wf assignment theory target ↔
      FinishedInstances joined decode impls wf assignment theory target :=
  ((export_canonicalEncoding_exact shared joined decode impls wf).mpr shared_joined_export_code)
    assignment theory target

end Examples

end Yulang.CommonCanonicalCurriedModule
