import Yulang.CommonCanonicalArrowExports

/-!
# Complete shared-arrow codes through the existing EOF gate

An instance-family code does not record the raw ambient support checked by
`finishModule`. Absorption can remove a captured occurrence semantically while
the original interface still requires that slot to be resolved at EOF.

This module adds the finite ambient-support code and proves completeness for
the actual composite operation: `finishModule` returns a closed interface,
and that interface's existing qualified binding admits the target. Every
partial ambient assignment, role theory and target is quantified. The role
resolver and its well-formed visible impl list are arbitrary; the empty
obligations of this closed arrow fragment make pending resolution vacuous.

The support code retains the current gate's behavior; it does not invent a
new weak-slot policy or claim that ordinary code equality preserves partial
exportability. Extraction from inference, nonempty qualifiers, generalized
rows, nominal types, arbitrary constructor interfaces and rendering remain
separate obligations.
-/

namespace Yulang.CommonCanonicalArrowModule

open CommonCanonicalArrowFamilies (Scheme Instances canonicalEncoding)
open CommonCanonicalArrowExports (model Ambient toInterface)
open Inference (Comp)
open QualifiedInference (Interface BindingTyping)

variable {fixed rowSlots generalized other : Nat}

def ambientInventory (fixed rowSlots : Nat) : List (Ambient fixed rowSlots) :=
  (List.finRange fixed).map Sum.inl ++ (List.finRange rowSlots).map Sum.inr

@[simp] theorem mem_ambientInventory (index : Ambient fixed rowSlots) :
    index ∈ ambientInventory fixed rowSlots := by
  cases index <;> simp [ambientInventory]

def supportCode (scheme : Scheme fixed rowSlots generalized) : List (Ambient fixed rowSlots) :=
  (ambientInventory fixed rowSlots).filter fun index => decide (index ∈ (toInterface scheme).support)

@[simp] theorem mem_supportCode (scheme : Scheme fixed rowSlots generalized) (index : Ambient fixed rowSlots) :
    index ∈ supportCode scheme ↔ index ∈ (toInterface scheme).support := by
  simp [supportCode]

theorem supportCode_exact (first : Scheme fixed rowSlots generalized) (last : Scheme fixed rowSlots other) :
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

def missing (index : Ambient fixed rowSlots) : Ambient fixed rowSlots → Option (Comp model) :=
  fun slot => if slot = index then none else some (.bottom, Common.rowEmpty)

theorem known_missing_iff (scheme : Scheme fixed rowSlots generalized) (index : Ambient fixed rowSlots) :
    (toInterface scheme).known (missing index) = true ↔ index ∉ (toInterface scheme).support := by
  rw [Interface.known, List.all_eq_true]
  constructor
  · intro known member
    have found := known index member
    simp [missing] at found
  · intro absent slot member
    have different : slot ≠ index := fun same => absent (same ▸ member)
    simp [missing, different]

theorem known_iff_of_support (first : Scheme fixed rowSlots generalized) (last : Scheme fixed rowSlots other)
    (same : ∀ index, index ∈ (toInterface first).support ↔ index ∈ (toInterface last).support)
    (assignment : Ambient fixed rowSlots → Option (Comp model)) :
    (toInterface first).known assignment = true ↔ (toInterface last).known assignment = true := by
  simp only [Interface.known, List.all_eq_true]
  exact ⟨fun known index member => known index ((same index).mpr member),
    fun known index member => known index ((same index).mp member)⟩

/-- This is the existing EOF result followed by the existing binding rule,
not a replacement meaning for an interface or its obligations. -/
def FinishedInstances (scheme : Scheme fixed rowSlots generalized)
    (decode : model.Ty → Roles.Term) (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (assignment : Ambient fixed rowSlots → Option (Comp model))
    (theory : RoleConstraints.Theory model) (target : Comp model) : Prop :=
  ∃ closed : QualifiedInference.ClosedInterface model generalized,
    QualifiedInference.finishModule model decode impls wf assignment (toInterface scheme) = some closed ∧
      BindingTyping model theory
        (.qualified generalized closed.requirements (fun parameters => Comp.pure model (closed.value parameters))) target

theorem finished_instances_exact (scheme : Scheme fixed rowSlots generalized)
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
      (CommonCanonicalArrowExports.finishModule_exact scheme decode impls wf assignment closed).mp accepted
    subst closed
    exact ⟨known, (CommonCanonicalArrowExports.binding_instances_exact scheme theory _ target).mp typed⟩
  · rintro ⟨known, member⟩
    refine ⟨(toInterface scheme).closeAt model (QualifiedInference.completeAssignment model assignment),
      (CommonCanonicalArrowExports.finishModule_exact scheme decode impls wf assignment _).mpr ⟨known, rfl⟩, ?_⟩
    exact (CommonCanonicalArrowExports.binding_instances_exact scheme theory _ target).mpr member

theorem finished_total_instances_exact (scheme : Scheme fixed rowSlots generalized)
    (decode : model.Ty → Roles.Term) (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (ambient : Ambient fixed rowSlots → Comp model)
    (theory : RoleConstraints.Theory model) (target : Comp model) :
    FinishedInstances scheme decode impls wf (fun index => some (ambient index)) theory target ↔
      (toInterface scheme).scheme.Holds model theory (Inference.extend ambient target) := by
  rw [finished_instances_exact, CommonCanonicalArrowExports.scheme_instances_exact]
  simp [Interface.known, QualifiedInference.completeAssignment]

theorem finished_top_iff_known (scheme : Scheme fixed rowSlots generalized)
    (decode : model.Ty → Roles.Term) (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (assignment : Ambient fixed rowSlots → Option (Comp model)) (theory : RoleConstraints.Theory model) :
    FinishedInstances scheme decode impls wf assignment theory (.top, Common.rowEmpty) ↔
      (toInterface scheme).known assignment = true := by
  rw [finished_instances_exact]
  exact ⟨And.left, fun known => ⟨known, fun _ => .bottom, CommonBoundCoalescing.le_top _⟩⟩

def exportCanonicalEncoding (scheme : Scheme fixed rowSlots generalized) :
    CommonCanonicalArrowFamilies.Code fixed rowSlots × List (Ambient fixed rowSlots) :=
  (canonicalEncoding scheme, supportCode scheme)

/-- Complete canonicality for partial EOF export followed by public use.
The decoder and visible impl set are arbitrary, as are all partial ambient
assignments, caller theories and target computations. Different generalized
arities are allowed; the finite type/row context is shared and fixed. -/
theorem export_canonicalEncoding_exact (first : Scheme fixed rowSlots generalized) (last : Scheme fixed rowSlots other)
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
    · apply (CommonCanonicalArrowExports.interface_canonicalEncoding_exact first last).mp
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
      ((CommonCanonicalArrowFamilies.canonicalEncoding_exact first last).mpr valueSame _ _ _)

namespace Examples

def plain : Scheme 1 1 1 := ⟨0, 0, 0, .atom (.var 1)⟩
def absorbed : Scheme 1 1 1 :=
  ⟨0, 0, 0, .union (.atom (.var 1)) (.inter (.atom (.var 0)) .bottom)⟩

theorem absorbed_captured_same_family_code : canonicalEncoding plain = canonicalEncoding absorbed := by
  decide +kernel

theorem absorbed_captured_different_export_code : exportCanonicalEncoding plain ≠ exportCanonicalEncoding absorbed := by
  decide +kernel

/-- The distinction is an actual EOF failure on the original syntax, not
only a difference in the newly stored support list. -/
theorem absorbed_captured_changes_EOF (decode : model.Ty → Roles.Term)
    (impls : List Roles.Impl) (wf : Roles.WellFormed impls) (theory : RoleConstraints.Theory model) :
    FinishedInstances plain decode impls wf (missing (.inl 0)) theory (.top, Common.rowEmpty) ∧
      ¬ FinishedInstances absorbed decode impls wf (missing (.inl 0)) theory (.top, Common.rowEmpty) := by
  rw [finished_top_iff_known, finished_top_iff_known, known_missing_iff, known_missing_iff]
  decide +kernel

end Examples

end Yulang.CommonCanonicalArrowModule
