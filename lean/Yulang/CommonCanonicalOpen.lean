import Yulang.Common
import Yulang.ProducerCanonicalOpenClauses

/-!
# The same open scalar encoding over arbitrary common parameters

The finite scalar syntax and its executable code are reused unchanged. Every
shared parameter now ranges over `Common.Ty`, including regular blocks, masks,
exact/default records and functions with arbitrary concrete rows. Only the
outer expression grammar is restricted to the scalar lattice fragment.

The Boolean profile argument is proved from the independent common probe
interpreter. It does not restrict demand environments or parameter instances
to the separating witnesses used in the proof. The code remains relative to
fixed shared parameter IDs; binder alpha-renaming and full interfaces are
outside this module.
-/

namespace Yulang.CommonCanonicalOpen

open ProducerCanonicalOpen (Atom Expr atoms profiles mem_profiles)
open CommonFinite (ProbeAt ProbeStep MaskedProbeStep)

variable {n : Nat}

def atomType (parameters : Fin n → Common.Ty) : Atom n → Common.Ty
  | .var index => parameters index
  | .base scalar => .base scalar

def instantiate (parameters : Fin n → Common.Ty) : Expr n → Common.Ty
  | .atom entry => atomType parameters entry
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (instantiate parameters first) (instantiate parameters last)
  | .inter first last => .inter (instantiate parameters first) (instantiate parameters last)

def toTerm : Expr n → Core.PresenceGeneration.TyTerm (Fin n)
  | .atom (.var index) => .var index
  | .atom (.base scalar) => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (toTerm first) (toTerm last)
  | .inter first last => .inter (toTerm first) (toTerm last)

/-- The shared parameter interpretation is the actual presence type-term
evaluation, with any simultaneous row assignment to those same slots. -/
theorem toTerm_eval (parameters : Fin n → Common.Ty) (rows : Fin n → Common.Row)
    (expression : Expr n) :
    (toTerm expression).eval Common.model (fun index => (parameters index, rows index)) =
      instantiate parameters expression := by
  induction expression with
  | atom entry => cases entry <;> rfl
  | bottom | top => rfl
  | union first last ihf ihl | inter first last ihf ihl =>
      simp only [toTerm, Core.PresenceGeneration.TyTerm.eval, instantiate]
      rw [ihf, ihl]
      rfl

def finiteAtom (parameters : Fin n → CommonFinite.Ty Common.Row) : Atom n → CommonFinite.Ty Common.Row
  | .var index => parameters index
  | .base scalar => .base scalar

def finiteInstantiate (parameters : Fin n → CommonFinite.Ty Common.Row) : Expr n → CommonFinite.Ty Common.Row
  | .atom entry => finiteAtom parameters entry
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (finiteInstantiate parameters first) (finiteInstantiate parameters last)
  | .inter first last => .inter (finiteInstantiate parameters first) (finiteInstantiate parameters last)

theorem observe_instantiate (depth : Nat) (parameters : Fin n → Common.Ty) (expression : Expr n) :
    Common.observeTy depth (instantiate parameters expression) =
      finiteInstantiate (fun index => Common.observeTy depth (parameters index)) expression := by
  induction expression with
  | atom entry => cases entry <;> rfl
  | bottom | top => rfl
  | union first last ihf ihl | inter first last ihf ihl =>
      change _ = _
      simp only [instantiate, Common.observeTy, CommonSyntax.Layer.evalAt, finiteInstantiate] at *
      rw [ihf, ihl]

private def roleEnvironment (profile : List (Atom n)) : CommonFinite.Environment Common.Row :=
  ⟨fun _ => .bottom,
    fun _ => (ProducerCanonicalBase.baseOrder.filter (fun scalar => decide (Atom.base scalar ∈ profile))).map
      ProducerContextual.Head.base⟩

private def roleParameters (profile : List (Atom n)) : Fin n → Common.Ty :=
  fun index => if Atom.var index ∈ profile then .bottom else .top

private def finiteRoleParameters (profile : List (Atom n)) : Fin n → CommonFinite.Ty Common.Row :=
  fun index => if Atom.var index ∈ profile then .bottom else .top

private theorem observe_roleParameters (depth : Nat) (profile : List (Atom n)) :
    (fun index => Common.observeTy depth (roleParameters profile index)) = finiteRoleParameters profile := by
  funext index
  simp only [roleParameters, finiteRoleParameters]
  split <;> rfl

private theorem atom_role_exact (rank : Nat) (profile : List (Atom n)) (entry : Atom n) :
    ProbeAt Common.rowLe rank (roleEnvironment profile) (finiteAtom (finiteRoleParameters profile) entry)
      (.role 0) ↔ entry ∈ profile := by
  cases entry with
  | var index =>
      by_cases member : Atom.var index ∈ profile <;> cases rank <;>
        simp [finiteAtom, finiteRoleParameters, member, ProbeAt, ProbeStep, MaskedProbeStep]
  | base scalar =>
      cases rank <;> simp [finiteAtom, ProbeAt, ProbeStep, MaskedProbeStep, roleEnvironment]

theorem finite_role_exact (rank : Nat) (profile : List (Atom n)) (expression : Expr n) :
    ProbeAt Common.rowLe rank (roleEnvironment profile)
      (finiteInstantiate (finiteRoleParameters profile) expression) (.role 0) ↔ expression.eval profile = true := by
  induction expression with
  | atom entry => simp [finiteInstantiate, Expr.eval, atom_role_exact]
  | bottom => simp [finiteInstantiate, Expr.eval]
  | top => cases rank <;> simp [ProbeAt, ProbeStep, MaskedProbeStep, finiteInstantiate, Expr.eval]
  | union first last ihf ihl | inter first last ihf ihl =>
      simp [finiteInstantiate, Expr.eval, ihf, ihl]

private theorem finite_probe_exact (rank : Nat) (environment : CommonFinite.Environment Common.Row)
    (observation : CommonFinite.Observation Common.Row) (nontrivial : observation ≠ .trivial)
    (parameters : Fin n → CommonFinite.Ty Common.Row) (profile : List (Atom n))
    (atomsExact : ∀ entry,
      ProbeAt Common.rowLe rank environment (finiteAtom parameters entry) observation ↔ entry ∈ profile)
    (expression : Expr n) :
    ProbeAt Common.rowLe rank environment (finiteInstantiate parameters expression) observation ↔
      expression.eval profile = true := by
  induction expression with
  | atom entry => simp [finiteInstantiate, Expr.eval, atomsExact]
  | bottom => simp [finiteInstantiate, Expr.eval]
  | top => cases rank <;> cases observation <;>
      simp_all [ProbeAt, ProbeStep, MaskedProbeStep, finiteInstantiate, Expr.eval]
  | union first last ihf ihl | inter first last ihf ihl =>
      simp [finiteInstantiate, Expr.eval, ihf, ihl]

/-- Every finite common observation determines one Boolean profile of the
finitely many shared atoms. Classical truth decisions occur only in this
existence proof, never in the executable encoding. -/
theorem finite_observation_has_profile (rank : Nat) (environment : CommonFinite.Environment Common.Row)
    (observation : CommonFinite.Observation Common.Row) (nontrivial : observation ≠ .trivial)
    (parameters : Fin n → CommonFinite.Ty Common.Row) :
    ∃ profile ∈ profiles n, ∀ expression : Expr n,
      ProbeAt Common.rowLe rank environment (finiteInstantiate parameters expression) observation ↔
        expression.eval profile = true := by
  classical
  let profile := (atoms n).filter fun entry =>
    decide (ProbeAt Common.rowLe rank environment (finiteAtom parameters entry) observation)
  refine ⟨profile, (mem_profiles profile).mpr List.filter_sublist, ?_⟩
  apply finite_probe_exact rank environment observation nontrivial parameters profile
  intro entry
  simp [profile]

theorem finite_equivalent_of_profiles (first last : Expr n)
    (same : ∀ profile ∈ profiles n, first.eval profile = last.eval profile)
    (parameters : Fin n → CommonFinite.Ty Common.Row) :
    CommonFinite.ProducerEq Common.rowLe (finiteInstantiate parameters first) (finiteInstantiate parameters last) := by
  apply (CommonFinite.producerEq_iff_probe _ _).mpr
  intro rank environment observation
  by_cases trivial : observation = .trivial
  · subst observation
    simp
  · obtain ⟨profile, member, exact⟩ :=
      finite_observation_has_profile rank environment observation trivial parameters
    rw [exact first, exact last, same profile member]

def Equivalent (first last : Expr n) : Prop :=
  ∀ parameters : Fin n → Common.Ty,
    Common.Equivalent (instantiate parameters first) (instantiate parameters last)

/-- Every common type is permitted in every parameter slot, simultaneously.
The right side is finite, but the left side quantifies all regular types, all
depths/ranks, all environments and every union-free demand. -/
theorem common_scalar_profile_exact (first last : Expr n) :
    Equivalent first last ↔ ∀ profile ∈ profiles n, first.eval profile = last.eval profile := by
  constructor
  · intro same profile _
    apply Bool.eq_iff_iff.mpr
    have actual := same (roleParameters profile)
    have observed := (CommonFinite.producerEq_iff_probe _ _).mp ⟨actual.1 0, actual.2 0⟩
      0 (roleEnvironment profile) (.role 0)
    simpa only [observe_instantiate, observe_roleParameters, finite_role_exact] using observed
  · intro same parameters
    have finite (depth : Nat) := finite_equivalent_of_profiles first last same
      (fun index => Common.observeTy depth (parameters index))
    constructor <;> intro depth
    · simpa only [observe_instantiate] using (finite depth).1
    · simpa only [observe_instantiate] using (finite depth).2

/-- Enlarging the parameter carrier to common regular/presence syntax adds
no scalar-family equality and loses none. This is a proved transfer, not an
assumption restricting the common parameter environment to old types. -/
theorem contextual_family_exact (first last : Expr n) :
    Equivalent first last ↔ ProducerCanonicalOpen.Equivalent Common.rowLe first last :=
  (common_scalar_profile_exact first last).trans
    (ProducerCanonicalOpen.equivalent_iff_evaluations Common.rowLe first last).symm

abbrev canonicalEncoding := @ProducerCanonicalOpenClauses.canonicalEncoding
abbrev normalize := @ProducerCanonicalOpenClauses.normalize

theorem canonicalEncoding_exact (first last : Expr n) :
    Equivalent first last ↔ canonicalEncoding first = canonicalEncoding last := by
  rw [common_scalar_profile_exact, ProducerCanonicalOpenClauses.canonicalEncoding_eq_iff]

theorem normalize_equivalent (expression : Expr n) : Equivalent (normalize expression) expression :=
  (common_scalar_profile_exact _ _).mpr (ProducerCanonicalOpenClauses.normalize_eval expression)

theorem normalize_idempotent (expression : Expr n) : normalize (normalize expression) = normalize expression :=
  ProducerCanonicalOpenClauses.normalize_idempotent expression

theorem normalize_exact (first last : Expr n) :
    Equivalent first last ↔ normalize first = normalize last := by
  constructor
  · intro same
    exact congrArg ProducerCanonicalOpenClauses.readback ((canonicalEncoding_exact first last).mp same)
  · intro same
    change ProducerCanonicalOpenClauses.normalize first = ProducerCanonicalOpenClauses.normalize last at same
    apply (common_scalar_profile_exact first last).mpr
    intro profile present
    rw [← ProducerCanonicalOpenClauses.normalize_eval first profile present, same,
      ProducerCanonicalOpenClauses.normalize_eval last profile present]

theorem instantiated_normalize_equivalent (parameters : Fin n → Common.Ty) (expression : Expr n) :
    Common.Equivalent (instantiate parameters (normalize expression)) (instantiate parameters expression) :=
  normalize_equivalent expression parameters

theorem union_comm (first last : Expr n) : Equivalent (.union first last) (.union last first) :=
  (common_scalar_profile_exact _ _).mpr fun _ _ => by simp [Expr.eval, Bool.and_comm]

end Yulang.CommonCanonicalOpen
