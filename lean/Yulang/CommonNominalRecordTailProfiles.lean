import Yulang.CommonNominalPayloadProjection

/-!
# Record-tail comparison through ordinary child profiles

At depth zero every guarded payload is bottom; default is still an ordinary
record insertion at that cutoff. Two finite Boolean inspections therefore
account for all initial field and nontrivial optional tests. At positive
depths the exact payload projections reduce the remaining obligations to
ordinary child comparisons, without a shifted-depth predicate.
-/

namespace Yulang.CommonNominalRecordTailProfiles

open CommonNominalSyntax (Layer)
open CommonNominalPayloadProjection

universe u v

/-- Field observations at the initial constructor cutoff. -/
def initialField (hidden : List Nat) (label : Nat) : Layer Row Index → Bool
  | .bottom => true
  | .union first last => initialField hidden label first && initialField hidden label last
  | .inter first last => initialField hidden label first || initialField hidden label last
  | .mask more source => initialField (hidden ++ more) label source
  | .record current _ rest | .recordDefault current rest _ =>
      if label = current ∧ current ∉ hidden then true else initialField hidden label rest
  | _ => false

/-- Nontrivial optional observations at the initial constructor cutoff. -/
def initialOptional (hidden : List Nat) (label : Nat) : Layer Row Index → Bool
  | .bottom => true
  | .union first last => initialOptional hidden label first && initialOptional hidden label last
  | .inter first last => initialOptional hidden label first || initialOptional hidden label last
  | .mask more source => initialOptional (hidden ++ more) label source
  | .exactEmpty => decide (label ∉ hidden)
  | .record current _ rest | .recordDefault current rest _ =>
      if label = current ∧ current ∉ hidden then true else initialOptional hidden label rest
  | _ => false

private theorem bottom_probe {Row : Type u} (leRow : Row → Row → Prop)
    (env : CommonNominalFinite.Environment Row)
    (argumentOrder : CommonNominalFinite.Ty Row → CommonNominalFinite.Ty Row → Prop)
    (obs : CommonNominalFinite.Observation Row) :
    CommonNominalFinite.MaskedProbeStep leRow env argumentOrder [] .bottom obs := by
  cases obs <;> trivial

theorem initial_field_finite_exact {Row : Type u} {Index : Type v}
    (leRow : Row → Row → Prop) (env : CommonNominalFinite.Environment Row)
    (argumentOrder : CommonNominalFinite.Ty Row → CommonNominalFinite.Ty Row → Prop)
    (hidden : List Nat) (label : Nat) (source : Layer Row Index) (obs : CommonNominalFinite.Observation Row) :
    CommonNominalFinite.MaskedProbeStep leRow env argumentOrder hidden
        (source.evalAt 0 (fun _ => .bottom)) (.field label obs) ↔
      initialField hidden label source = true := by
  induction source generalizing hidden <;>
    simp_all [Layer.evalAt, CommonNominalFinite.MaskedProbeStep, initialField, bottom_probe]
  all_goals grind

theorem initial_optional_finite_exact {Row : Type u} {Index : Type v}
    (leRow : Row → Row → Prop) (env : CommonNominalFinite.Environment Row)
    (argumentOrder : CommonNominalFinite.Ty Row → CommonNominalFinite.Ty Row → Prop)
    (hidden : List Nat) (label : Nat) (source : Layer Row Index) (obs : CommonNominalFinite.Observation Row)
    (nontrivial : obs ≠ .trivial) :
    CommonNominalFinite.MaskedProbeStep leRow env argumentOrder hidden
        (source.evalAt 0 (fun _ => .bottom)) (.optional label obs) ↔
      initialOptional hidden label source = true := by
  induction source generalizing hidden <;>
    simp_all [Layer.evalAt, CommonNominalFinite.MaskedProbeStep, initialOptional, bottom_probe]
  all_goals grind

theorem initial_field_exact (hidden : List Nat) (label : Nat) (source : CommonNominalCarrier.Ty)
    (rank : Nat) (env : CommonNominalFinite.Environment CommonNominalCarrier.Row) (obs : CommonNominalCarrier.Observation) :
    CommonNominalFinite.MaskedProbeAt Common.rowLe rank env hidden
        (CommonNominalCarrier.observeTy 0 source) (.field label obs) ↔ initialField hidden label source = true := by
  cases rank <;> exact initial_field_finite_exact Common.rowLe env _ hidden label source obs

theorem initial_optional_exact (hidden : List Nat) (label : Nat) (source : CommonNominalCarrier.Ty)
    (rank : Nat) (env : CommonNominalFinite.Environment CommonNominalCarrier.Row) (obs : CommonNominalCarrier.Observation)
    (nontrivial : obs ≠ .trivial) :
    CommonNominalFinite.MaskedProbeAt Common.rowLe rank env hidden
        (CommonNominalCarrier.observeTy 0 source) (.optional label obs) ↔ initialOptional hidden label source = true := by
  cases rank <;> exact initial_optional_finite_exact Common.rowLe env _ hidden label source obs nontrivial

theorem profile_getD_exact (profile : Option CommonNominalCarrier.Ty) (depth rank : Nat)
    (env : CommonNominalFinite.Environment CommonNominalCarrier.Row) (obs : CommonNominalCarrier.Observation) :
    CommonNominalFinite.ProbeAt Common.rowLe rank env
        (CommonNominalCarrier.observeTy depth (profile.getD .top)) obs ↔
      ProfileAt depth rank env profile obs ∨ obs = .trivial := by
  cases profile with
  | none =>
      cases rank <;> cases obs <;>
        simp [ProfileAt, CommonNominalCarrier.observeTy, Layer.evalAt, CommonNominalFinite.ProbeAt,
          CommonNominalFinite.ProbeStep, CommonNominalFinite.MaskedProbeStep]
  | some payload =>
      simp only [Option.getD, ProfileAt]
      constructor
      · exact Or.inl
      · rintro (accepted | rfl)
        · exact accepted
        · exact CommonNominalFinite.probeAt_trivial rank _

/-- The tail passes only nontrivial optional demands. Adding the trivial
test to both profiles makes this exactly an ordinary subtype comparison. -/
theorem optional_profiles_exact (source target : Option CommonNominalCarrier.Ty) :
    CommonNominalCarrier.Subtype (source.getD .top) (target.getD .top) ↔
      ∀ depth rank env obs, obs ≠ .trivial → ProfileAt depth rank env target obs →
        ProfileAt depth rank env source obs := by
  constructor
  · intro below depth rank env obs nontrivial accepted
    have output := (CommonNominalFinite.producerLe_iff_probe _ _).mp (below depth) rank env obs
      ((profile_getD_exact target depth rank env obs).mpr (Or.inl accepted))
    exact ((profile_getD_exact source depth rank env obs).mp output).resolve_right nontrivial
  · intro below depth
    apply (CommonNominalFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    by_cases trivial : obs = .trivial
    · subst obs
      exact CommonNominalFinite.probeAt_trivial rank _
    · apply (profile_getD_exact source depth rank env obs).mpr
      exact Or.inl (below depth rank env obs trivial
        (((profile_getD_exact target depth rank env obs).mp accepted).resolve_right trivial))

theorem field_profiles_exact (label : Nat) (source target : CommonNominalCarrier.Ty) :
    ProfileLe (fieldType [] label source) (fieldType [] label target) ↔
      ∀ depth rank env obs,
        CommonNominalFinite.ProbeAt Common.rowLe rank env (CommonNominalCarrier.observeTy (depth + 1) target)
          (.field label obs) →
        CommonNominalFinite.ProbeAt Common.rowLe rank env (CommonNominalCarrier.observeTy (depth + 1) source)
          (.field label obs) := by
  rw [profileLe_exact]
  apply forall_congr'
  intro depth
  apply forall_congr'
  intro rank
  apply forall_congr'
  intro env
  apply forall_congr'
  intro obs
  exact imp_congr
    (by simpa only [CommonNominalFinite.maskedProbeAt_nil] using
      (field_type_exact [] label target depth rank env obs).symm)
    (by simpa only [CommonNominalFinite.maskedProbeAt_nil] using
      (field_type_exact [] label source depth rank env obs).symm)

theorem optional_tail_profiles_exact (label : Nat) (source target : CommonNominalCarrier.Ty) :
    CommonNominalCarrier.Subtype ((optionalType [] label source).getD .top)
        ((optionalType [] label target).getD .top) ↔
      ∀ depth rank env obs, obs ≠ .trivial →
        CommonNominalFinite.ProbeAt Common.rowLe rank env (CommonNominalCarrier.observeTy (depth + 1) target)
          (.optional label obs) →
        CommonNominalFinite.ProbeAt Common.rowLe rank env (CommonNominalCarrier.observeTy (depth + 1) source)
          (.optional label obs) := by
  rw [optional_profiles_exact]
  apply forall_congr'
  intro depth
  apply forall_congr'
  intro rank
  apply forall_congr'
  intro env
  apply forall_congr'
  intro obs
  apply imp_congr_right
  intro _
  exact imp_congr
    (by simpa only [CommonNominalFinite.maskedProbeAt_nil] using
      (optional_type_exact [] label target depth rank env obs).symm)
    (by simpa only [CommonNominalFinite.maskedProbeAt_nil] using
      (optional_type_exact [] label source depth rank env obs).symm)

/-- At one remaining label: finite initial checks and ordinary child
comparisons. Neither condition contains the original tail comparison. -/
def AtLabel (source target : CommonNominalCarrier.Ty) (label : Nat) : Prop :=
  (initialField [] label target = true → initialField [] label source = true) ∧
  (initialOptional [] label target = true → initialOptional [] label source = true) ∧
  ProfileLe (fieldType [] label source) (fieldType [] label target) ∧
  CommonNominalCarrier.Subtype ((optionalType [] label source).getD .top) ((optionalType [] label target).getD .top)

/-- Same-depth tail comparison reduces to the declared per-label child
conditions at every visible label. The finite inventory pass can now remove
this last label quantifier independently of regular depth and demand rank. -/
theorem tail_profiles_exact (hidden : List Nat) (source target : CommonNominalCarrier.Ty) :
    CommonNominalCarrier.RecordTailLe hidden source target ↔
      ∀ label, label ∉ hidden → AtLabel source target label := by
  constructor
  · intro below label visible
    let env : CommonNominalFinite.Environment CommonNominalCarrier.Row := ⟨fun _ => .bottom, fun _ => []⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro initial
      have accepted : CommonNominalFinite.ProbeAt Common.rowLe 0 env (CommonNominalCarrier.observeTy 0 target)
          (.field label .impossible) := by
        simpa only [CommonNominalFinite.maskedProbeAt_nil] using
          (initial_field_exact [] label target 0 env .impossible).mpr initial
      have output := (below 0).1 0 env label visible .impossible accepted
      exact (initial_field_exact [] label source 0 env .impossible).mp
        ((CommonNominalFinite.maskedProbeAt_nil 0 env _ _).mpr output)
    · intro initial
      have accepted : CommonNominalFinite.ProbeAt Common.rowLe 0 env (CommonNominalCarrier.observeTy 0 target)
          (.optional label .impossible) := by
        simpa only [CommonNominalFinite.maskedProbeAt_nil] using
          (initial_optional_exact [] label target 0 env .impossible (by intro same; cases same)).mpr initial
      have output := (below 0).2 0 env label visible .impossible (by intro same; cases same) accepted
      exact (initial_optional_exact [] label source 0 env .impossible (by intro same; cases same)).mp
        ((CommonNominalFinite.maskedProbeAt_nil 0 env _ _).mpr output)
    · exact (field_profiles_exact label source target).mpr
        (fun depth rank next obs => (below (depth + 1)).1 rank next label visible obs)
    · exact (optional_tail_profiles_exact label source target).mpr
        (fun depth rank next obs => (below (depth + 1)).2 rank next label visible obs)
  · intro every depth
    constructor
    · intro rank env label visible obs accepted
      have conditions := every label visible
      cases depth with
      | zero =>
          have initial := (initial_field_exact [] label target rank env obs).mp
            ((CommonNominalFinite.maskedProbeAt_nil rank env _ _).mpr accepted)
          exact (CommonNominalFinite.maskedProbeAt_nil rank env _ _).mp
            ((initial_field_exact [] label source rank env obs).mpr (conditions.1 initial))
      | succ depth =>
          exact (field_profiles_exact label source target).mp conditions.2.2.1
            depth rank env obs accepted
    · intro rank env label visible obs nontrivial accepted
      have conditions := every label visible
      cases depth with
      | zero =>
          have initial := (initial_optional_exact [] label target rank env obs nontrivial).mp
            ((CommonNominalFinite.maskedProbeAt_nil rank env _ _).mpr accepted)
          exact (CommonNominalFinite.maskedProbeAt_nil rank env _ _).mp
            ((initial_optional_exact [] label source rank env obs nontrivial).mpr (conditions.2.1 initial))
      | succ depth =>
          exact (optional_tail_profiles_exact label source target).mp conditions.2.2.2
            depth rank env obs nontrivial accepted

end Yulang.CommonNominalRecordTailProfiles
