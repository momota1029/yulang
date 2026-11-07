import Yulang.CommonRoleFiniteTailSemantic

/-! Smallest component-count core example. Open record tails are admitted by
the existing verified-declaration API; surface record annotations do not have
spread syntax, and no source reachability is claimed. -/
namespace Yulang.CommonRoleFiniteTailExamples

open CommonRoleInspectedSemantics

def headPattern : Pattern := .record .int (.var 0)
def implementation : Roles.Impl := ⟨0, [headPattern.encode], [⟨0, [(.var 0 : Pattern).encode]⟩], 0⟩
def goal : Goal := ⟨0, CommonRoleFiniteTailClock.atom⟩

def declaration : CommonRoleHeadDetermination.Declaration :=
  ⟨0, 0, [.record 0 .int (.var 0)], [(0, [.var 0])], [(0, .int)]⟩

theorem old_verified_api_accepts :
    declaration.toImpl = implementation ∧ (CommonRoleHeadDetermination.verify declaration).isSome = true := by
  decide +kernel

theorem normalized_checked : CommonRoleNormalizedDeclarations.checkImpl implementation = true := by decide +kernel

theorem declaration_fixed : CommonRoleNormalizedDeclarations.normalizeImpl implementation = implementation := by
  decide +kernel

theorem declaration_sizes : Roles.argsSize implementation.head = 3 ∧
    Roles.argsSize (CommonRoleNormalizedDeclarations.normalizeImpl implementation).head = 3 ∧
    Roles.argsSize [(.var 0 : Pattern).encode] = 1 := by decide +kernel

theorem goal_ready : Ready [implementation] goal := finite_ready _ _ rfl

theorem head_matches : Matches implementation goal (fun _ => CommonRoleFiniteTailClock.atom.eval) :=
  ⟨rfl, _, _, rfl, interpret_encode headPattern _, CommonRoleFiniteTailClock.atom_absorbs⟩

theorem child_returns : interpretGoal ⟨0, [(.var 0 : Pattern).encode]⟩ (fun _ => CommonRoleFiniteTailClock.atom) = some goal := by
  simp [interpretGoal, instantiate, goal]

def substitute (pattern : Pattern) (replacement : Nat → Pattern) : Pattern :=
  match pattern with
  | .var name => replacement name
  | .int => .int
  | .empty => .empty
  | .pair first last => .pair (substitute first replacement) (substitute last replacement)
  | .variant tag payload => .variant tag (substitute payload replacement)
  | .record payload rest => .record (substitute payload replacement) (substitute rest replacement)

def capture : Nat → Pattern := fun _ => .record .int .empty

theorem normalization_does_not_commute_with_capture :
    substitute (headPattern.visible false) capture ≠ (substitute headPattern capture).visible false := by
  decide +kernel

theorem post_capture_sizes :
    (substitute headPattern capture).encode.size = 5 ∧
      ((substitute headPattern capture).visible false).encode.size = 3 ∧
      (capture 0).encode.size = 3 := by decide +kernel

theorem finite_children_differ : ¬ Common.Equivalent CommonRoleFiniteTailClock.atom.eval Common.emptyRecord := by
  intro same
  have observed := (CommonCanonicalShapes.equivalent_iff_probes _ _).mp same 0 0
    ⟨fun _ => .bottom, fun _ => []⟩ (.field 0 .trivial)
  simp [CommonRoleFiniteTailClock.atom, Description.eval, Common.record, Common.emptyRecord,
    Common.observeTy, CommonSyntax.Layer.evalAt, CommonSyntax.observe, CommonFinite.ProbeAt,
    CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep] at observed

def HeadDeterminesRequirements (implementation : Roles.Impl) : Prop :=
  ∀ σ τ : Nat → Common.Ty,
    (∀ term ∈ implementation.head, ∃ first last, interpretTerm term σ = some first ∧
      interpretTerm term τ = some last ∧ Common.Equivalent first last) →
    ∀ child ∈ implementation.constraints, ∀ term ∈ child.args, ∃ first last,
      interpretTerm term σ = some first ∧ interpretTerm term τ = some last ∧ Common.Equivalent first last

theorem requirements_not_determined : ¬ HeadDeterminesRequirements implementation := by
  intro determines
  let σ : Nat → Common.Ty := fun _ => CommonRoleFiniteTailClock.atom.eval
  let τ : Nat → Common.Ty := fun _ => Common.emptyRecord
  have heads : ∀ term ∈ implementation.head, ∃ first last, interpretTerm term σ = some first ∧
      interpretTerm term τ = some last ∧ Common.Equivalent first last := by
    intro term member
    have equal : term = headPattern.encode := by simpa [implementation] using member
    subst term
    exact ⟨_, _, interpret_encode headPattern σ, interpret_encode headPattern τ,
      CommonRoleFiniteTailClock.atom_absorbs⟩
  obtain ⟨first, last, firstRead, lastRead, same⟩ := determines σ τ heads
    ⟨0, [(.var 0 : Pattern).encode]⟩ (by simp [implementation])
    (.var 0) (by simp [Pattern.encode])
  have firstEqual : first = CommonRoleFiniteTailClock.atom.eval := Option.some.inj firstRead.symm
  have lastEqual : last = Common.emptyRecord := Option.some.inj lastRead.symm
  subst first
  subst last
  exact finite_children_differ same

end Yulang.CommonRoleFiniteTailExamples
