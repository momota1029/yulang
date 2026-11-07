import Yulang.CommonRecordEnvelope

/-!
# A finite outer test for the common top type

The Boolean inspects only the independent root syntax. It never unfolds a
guarded reference, asks a subtype solver, or bounds constructor depth or
negative-context rank. A positive result has a finite role witness at every
depth; a negative result leaves only the trivial observation.
-/

namespace Yulang.CommonTopTest

open CommonSyntax (Layer)
open CommonRecordEnvelope (heads)

universe u v

variable {Row : Type u} {Index : Type v}

/-- Whether the outer syntax admits a nontrivial observation. Arbitrary
payload references and rows do not affect this finite test. -/
def nontrivial : Layer Row Index → Bool
  | .top => false
  | .union first last => nontrivial first && nontrivial last
  | .inter first last => nontrivial first || nontrivial last
  | .mask _ source => nontrivial source
  | _ => true

theorem nontrivial_map (rename : Index → Target) (source : Layer Row Index) :
    nontrivial (source.map rename) = nontrivial source := by
  induction source <;> simp_all [nontrivial, Layer.map]

theorem nontrivial_role_exact (leRow : Row → Row → Prop)
    (env : CommonFinite.Environment Row)
    (argumentOrder : CommonFinite.Ty Row → CommonFinite.Ty Row → Prop)
    (assignment : Index → CommonFinite.Ty Row) (depth : Nat)
    (hidden : List Nat) (name : Nat) (source : Layer Row Index)
    (roles : ∀ head ∈ heads source, head ∈ env.roles name) :
    CommonFinite.MaskedProbeStep leRow env argumentOrder hidden
        (source.evalAt depth assignment) (.role name) ↔ nontrivial source = true := by
  induction source generalizing hidden with
  | union first last before after =>
      have leftRoles : ∀ head ∈ heads first, head ∈ env.roles name :=
        fun head member => roles head (List.mem_append.mpr (Or.inl member))
      have rightRoles : ∀ head ∈ heads last, head ∈ env.roles name :=
        fun head member => roles head (List.mem_append.mpr (Or.inr member))
      simpa only [Layer.evalAt, CommonFinite.maskedProbeStep_union, nontrivial,
        Bool.and_eq_true] using and_congr (before hidden leftRoles) (after hidden rightRoles)
  | inter first last before after =>
      have leftRoles : ∀ head ∈ heads first, head ∈ env.roles name :=
        fun head member => roles head (List.mem_append.mpr (Or.inl member))
      have rightRoles : ∀ head ∈ heads last, head ∈ env.roles name :=
        fun head member => roles head (List.mem_append.mpr (Or.inr member))
      simpa only [Layer.evalAt, CommonFinite.maskedProbeStep_inter, nontrivial,
        Bool.or_eq_true] using or_congr (before hidden leftRoles) (after hidden rightRoles)
  | mask more source ih =>
      simpa only [Layer.evalAt, CommonFinite.MaskedProbeStep, nontrivial] using
        ih (hidden ++ more) roles
  | recordDefault label source fallback ih =>
      have present := roles .records (by simp [heads])
      cases depth <;> simpa [Layer.evalAt, CommonFinite.MaskedProbeStep, nontrivial] using present
  | bottom | top => simp [Layer.evalAt, CommonFinite.MaskedProbeStep, nontrivial]
  | base scalar =>
      simpa [Layer.evalAt, CommonFinite.MaskedProbeStep, nontrivial] using
        roles (.base scalar) (by simp [heads])
  | pair first last =>
      simpa [Layer.evalAt, CommonFinite.MaskedProbeStep, nontrivial] using
        roles .pair (by simp [heads])
  | emptyRecord =>
      simpa [Layer.evalAt, CommonFinite.MaskedProbeStep, nontrivial] using
        roles .records (by simp [heads])
  | exactEmpty =>
      simpa [Layer.evalAt, CommonFinite.MaskedProbeStep, nontrivial] using
        roles .records (by simp [heads])
  | record label payload rest ih =>
      simpa [Layer.evalAt, CommonFinite.MaskedProbeStep, nontrivial] using
        roles .records (by simp [heads])
  | variant label payload =>
      simpa [Layer.evalAt, CommonFinite.MaskedProbeStep, nontrivial] using
        roles (.variant label) (by simp [heads])
  | arrow input inputRow output outputRow =>
      simpa [Layer.evalAt, CommonFinite.MaskedProbeStep, nontrivial] using
        roles .arrow (by simp [heads])

theorem nontrivial_of_probe (leRow : Row → Row → Prop)
    (env : CommonFinite.Environment Row)
    (argumentOrder : CommonFinite.Ty Row → CommonFinite.Ty Row → Prop)
    (assignment : Index → CommonFinite.Ty Row) (depth : Nat)
    (hidden : List Nat) (source : Layer Row Index) (obs : CommonFinite.Observation Row)
    (notTrivial : obs ≠ .trivial)
    (accepted : CommonFinite.MaskedProbeStep leRow env argumentOrder hidden
      (source.evalAt depth assignment) obs) : nontrivial source = true := by
  induction source generalizing hidden with
  | union first last before after =>
      have both := (CommonFinite.maskedProbeStep_union hidden _ _ obs).mp accepted
      simp only [nontrivial, Bool.and_eq_true]
      exact ⟨before hidden both.1, after hidden both.2⟩
  | inter first last before after =>
      have either := (CommonFinite.maskedProbeStep_inter hidden _ _ obs).mp accepted
      simp only [nontrivial, Bool.or_eq_true]
      exact either.elim
        (fun valid => Or.inl (before hidden valid)) (fun valid => Or.inr (after hidden valid))
  | mask more source ih =>
      apply ih (hidden ++ more)
      simpa only [Layer.evalAt, CommonFinite.maskedProbeStep_mask] using accepted
  | top =>
      cases obs <;> simp_all [Layer.evalAt, CommonFinite.MaskedProbeStep]
  | _ => rfl

def roleEnvironment (source : Common.Ty) : CommonFinite.Environment Common.Row :=
  ⟨fun _ => .bottom, fun _ => heads source⟩

/-- The same finite role list witnesses non-topness at every depth and rank. -/
theorem role_witness (source : Common.Ty) (positive : nontrivial source = true)
    (depth rank : Nat) :
    CommonFinite.ProbeAt Common.rowLe rank (roleEnvironment source)
      (Common.observeTy depth source) (.role 0) := by
  cases rank <;>
    exact (nontrivial_role_exact Common.rowLe (roleEnvironment source) _ _ depth
      [] 0 source (fun _ member => member)).mpr positive

/-- Exact for all common types, including arbitrary regular and negative children. -/
theorem top_iff (source : Common.Ty) :
    Common.Equivalent source .top ↔ nontrivial source = false := by
  constructor
  · intro same
    cases found : nontrivial source with
    | false => rfl
    | true =>
        have impossible := (CommonFinite.producerLe_iff_probe _ _).mp (same.2 0) 0
          (roleEnvironment source) (.role 0) (role_witness source found 0 0)
        exact False.elim impossible
  · intro empty
    constructor
    · intro depth
      apply (CommonFinite.producerLe_iff_probe _ _).mpr
      intro rank env obs accepted
      cases obs <;> cases rank <;>
        simp_all [Common.observeTy, Layer.evalAt, CommonFinite.ProbeAt, CommonFinite.ProbeStep,
          CommonFinite.MaskedProbeStep]
    · intro depth
      apply (CommonFinite.producerLe_iff_probe _ _).mpr
      intro rank env obs accepted
      by_cases trivial : obs = .trivial
      · subst obs
        exact CommonFinite.probeAt_trivial rank _
      · have positive : nontrivial source = true := by
          cases rank <;> exact nontrivial_of_probe Common.rowLe env _ _ depth [] source obs
            trivial accepted
        simp [empty] at positive

theorem nontrivial_iff_not_top (source : Common.Ty) :
    nontrivial source = true ↔ ¬ Common.Equivalent source .top := by
  rw [top_iff]
  cases nontrivial source <;> simp

end Yulang.CommonTopTest
