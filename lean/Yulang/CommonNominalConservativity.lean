import Yulang.CommonNominalEmbedding

/-!
# Old demand order in arbitrary extended negative environments

At each negative rank, a finite family of old arrow inputs is observed. For
an arbitrary extended parameter, intersect exactly those old inputs above it.
This single old witness realizes all comparisons in that family simultaneously.
The induction uses the previous rank's conservativity, not a restriction of
extended parameters or an added assumption on solved instances.
-/

namespace Yulang.CommonNominalConservativity

abbrev Row := Common.Row
abbrev Old := CommonFinite.Ty Row
abbrev New := CommonNominalFinite.Ty Row
abbrev embed := @CommonNominalEmbedding.finite Row
abbrev OldLe (rank : Nat) := CommonFinite.ProducerLeAt Common.rowLe rank
abbrev NewLe (rank : Nat) := CommonNominalFinite.ProducerLeAt Common.rowLe rank

private def meet : List Old → Old
  | [] => .top
  | head :: tail => .inter head (meet tail)

private theorem new_trans {rank : Nat} {a b c : New}
    (first : NewLe rank a b) (last : NewLe rank b c) : NewLe rank a c :=
  fun env demand accepted => first env demand (last env demand accepted)

private theorem new_top (rank : Nat) (type : New) : NewLe rank type .top := by
  apply (CommonNominalFinite.producerLeAt_iff_probe _ _ _).mpr
  intro env obs accepted
  cases rank <;> cases obs <;>
    simp_all [CommonNominalFinite.ProbeAt, CommonNominalFinite.ProbeStep,
      CommonNominalFinite.MaskedProbeStep]

private theorem new_meet (rank : Nat) (type : New) (inputs : List Old) :
    NewLe rank type (embed (meet inputs)) ↔ ∀ input ∈ inputs, NewLe rank type (embed input) := by
  induction inputs with
  | nil =>
      constructor
      · intro _ input member; cases member
      · intro _; exact new_top rank type
  | cons head tail ih =>
      change NewLe rank type (.inter (embed head) (embed (meet tail))) ↔ _
      have split : NewLe rank type (.inter (embed head) (embed (meet tail))) ↔
          NewLe rank type (embed head) ∧ NewLe rank type (embed (meet tail)) := by
        simp only [NewLe, CommonNominalFinite.producerLeAt_iff_probe,
          CommonNominalFinite.probeAt_inter, or_imp, forall_and]
      rw [split, ih]
      simp

private theorem old_meet_member (rank : Nat) (inputs : List Old) (input : Old)
    (present : input ∈ inputs) : OldLe rank (meet inputs) input := by
  apply (CommonFinite.producerLeAt_iff_probe _ _ _).mpr
  intro env obs accepted
  induction inputs with
  | nil => cases present
  | cons head tail ih =>
      change CommonFinite.ProbeAt Common.rowLe rank env (.inter head (meet tail)) obs
      apply (CommonFinite.probeAt_inter _ _ _ _).mpr
      rcases List.mem_cons.mp present with rfl | later
      · exact Or.inl accepted
      · exact Or.inr (ih later)

private noncomputable def witness (rank : Nat) (parameter : New) (inputs : List Old) : Old := by
  classical
  exact meet (inputs.filter fun input => decide (NewLe rank parameter (embed input)))

/-- One old witness, shared across every input in the whole finite family. -/
private theorem witness_exact (rank : Nat)
    (previous : ∀ first last : Old, NewLe rank (embed first) (embed last) ↔ OldLe rank first last)
    (parameter : New) (inputs : List Old) (input : Old) (present : input ∈ inputs) :
    NewLe rank parameter (embed input) ↔ OldLe rank (witness rank parameter inputs) input := by
  classical
  let selected := inputs.filter fun input => decide (NewLe rank parameter (embed input))
  have below : NewLe rank parameter (embed (witness rank parameter inputs)) := by
    apply (new_meet rank parameter selected).mpr
    intro chosen member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  constructor
  · intro accepted
    exact old_meet_member rank selected input (List.mem_filter.mpr ⟨present, by simp [accepted]⟩)
  · intro accepted
    exact new_trans below ((previous _ _).mpr accepted)

end Yulang.CommonNominalConservativity

namespace Yulang.CommonNominalConservativity

private def project : CommonNominalFinite.Observation Row → CommonFinite.Observation Row
  | .trivial => .trivial
  | .impossible => .impossible
  | .base scalar => .base scalar
  | .records => .records
  | .role name => .role name
  | .pairFirst obs => .pairFirst (project obs)
  | .pairLast obs => .pairLast (project obs)
  | .field label obs => .field label (project obs)
  | .optional label obs => .optional label (project obs)
  | .variant label obs => .variant label (project obs)
  | .arrowArgument name => .arrowArgument name
  | .arrowResult obs => .arrowResult (project obs)
  | .arrowInputRow row => .arrowInputRow row
  | .arrowOutputRow row => .arrowOutputRow row
  | .float | .nominalHead _ _ | .nominalLower _ _ | .nominalUpper _ _ |
      .nominalRowLower _ _ | .nominalRowUpper _ _ => .impossible

private def lift : CommonFinite.Observation Row → CommonNominalFinite.Observation Row
  | .trivial => .trivial
  | .impossible => .impossible
  | .base scalar => .base scalar
  | .records => .records
  | .role name => .role name
  | .pairFirst obs => .pairFirst (lift obs)
  | .pairLast obs => .pairLast (lift obs)
  | .field label obs => .field label (lift obs)
  | .optional label obs => .optional label (lift obs)
  | .variant label obs => .variant label (lift obs)
  | .arrowArgument name => .arrowArgument name
  | .arrowResult obs => .arrowResult (lift obs)
  | .arrowInputRow row => .arrowInputRow row
  | .arrowOutputRow row => .arrowOutputRow row

@[simp] private theorem project_lift (obs : CommonFinite.Observation Row) : project (lift obs) = obs := by
  induction obs <;> simp [lift, project, *]

@[simp] private theorem project_trivial (obs : CommonNominalFinite.Observation Row) :
    project obs = .trivial ↔ obs = .trivial := by
  cases obs <;> simp [project]

private def inputs : Old → List Old
  | .base _ | .bottom | .top | .emptyRecord | .exactEmpty => []
  | .union first last | .inter first last | .pair first last |
      .record _ first last | .recordDefault _ first last => inputs first ++ inputs last
  | .variant _ payload | .mask _ payload => inputs payload
  | .arrow input _ result _ => input :: inputs result

private def Compatible (oldEnv : CommonFinite.Environment Row)
    (newEnv : CommonNominalFinite.Environment Row)
    (oldArg : Old → Old → Prop) (newArg : New → New → Prop) : Old → Prop
  | .base _ | .bottom | .top | .emptyRecord | .exactEmpty => True
  | .union first last | .inter first last | .pair first last |
      .record _ first last | .recordDefault _ first last =>
      Compatible oldEnv newEnv oldArg newArg first ∧ Compatible oldEnv newEnv oldArg newArg last
  | .variant _ payload | .mask _ payload => Compatible oldEnv newEnv oldArg newArg payload
  | .arrow input _ result _ =>
      (∀ name, newArg (newEnv.types name) (embed input) ↔ oldArg (oldEnv.types name) input) ∧
        Compatible oldEnv newEnv oldArg newArg result

private theorem compatible_iff (oldEnv : CommonFinite.Environment Row)
    (newEnv : CommonNominalFinite.Environment Row)
    (oldArg : Old → Old → Prop) (newArg : New → New → Prop) (type : Old) :
    Compatible oldEnv newEnv oldArg newArg type ↔
      ∀ input ∈ inputs type, ∀ name,
        newArg (newEnv.types name) (embed input) ↔ oldArg (oldEnv.types name) input := by
  induction type <;> simp [Compatible, inputs, *, List.mem_append, or_imp, forall_and]

private theorem project_step (oldEnv : CommonFinite.Environment Row)
    (newEnv : CommonNominalFinite.Environment Row) (roles : newEnv.roles = oldEnv.roles)
    (oldArg : Old → Old → Prop) (newArg : New → New → Prop) (type : Old)
    (compatible : Compatible oldEnv newEnv oldArg newArg type)
    (hidden : List Nat) (obs : CommonNominalFinite.Observation Row) :
    CommonNominalFinite.MaskedProbeStep Common.rowLe newEnv newArg hidden (embed type) obs ↔
      CommonFinite.MaskedProbeStep Common.rowLe oldEnv oldArg hidden type (project obs) := by
  induction type generalizing hidden obs with
  | base scalar | bottom | top | emptyRecord | exactEmpty =>
      cases obs <;> simp [embed, CommonNominalEmbedding.finite, project,
        CommonNominalFinite.MaskedProbeStep, CommonFinite.MaskedProbeStep, roles]
  | union first last ihf ihl | inter first last ihf ihl | pair first last ihf ihl =>
      have forward := ihf compatible.1
      have backward := ihl compatible.2
      cases obs <;> simp [embed, CommonNominalEmbedding.finite, project,
        CommonNominalFinite.MaskedProbeStep, CommonFinite.MaskedProbeStep,
        forward, backward, roles]
  | record label head tail ihh iht | recordDefault label head tail ihh iht =>
      have forward := ihh compatible.1
      have backward := iht compatible.2
      cases obs <;> simp [embed, CommonNominalEmbedding.finite, project,
        CommonNominalFinite.MaskedProbeStep, CommonFinite.MaskedProbeStep,
        forward, backward, roles]
  | variant label payload ih | mask hidden' payload ih =>
      have inner := ih compatible
      cases obs <;> simp [embed, CommonNominalEmbedding.finite, project,
        CommonNominalFinite.MaskedProbeStep, CommonFinite.MaskedProbeStep, inner, roles]
  | arrow input inputRow result resultRow _ ihr =>
      have output := ihr compatible.2
      cases obs <;> simp [embed, CommonNominalEmbedding.finite, project,
        CommonNominalFinite.MaskedProbeStep, CommonFinite.MaskedProbeStep,
        output, compatible.1, roles]

end Yulang.CommonNominalConservativity

namespace Yulang.CommonNominalConservativity

private theorem project_zero (oldEnv : CommonFinite.Environment Row)
    (newEnv : CommonNominalFinite.Environment Row) (roles : newEnv.roles = oldEnv.roles)
    (type : Old) (obs : CommonNominalFinite.Observation Row) :
    CommonNominalFinite.ProbeAt Common.rowLe 0 newEnv (embed type) obs ↔
      CommonFinite.ProbeAt Common.rowLe 0 oldEnv type (project obs) := by
  apply project_step oldEnv newEnv roles (fun _ _ => True) (fun _ _ => True) type _ [] obs
  apply (compatible_iff _ _ _ _ _).mpr
  intro input _ name
  rfl

private noncomputable def oldWitnessEnvironment (rank : Nat) (newEnv : CommonNominalFinite.Environment Row)
    (family : List Old) : CommonFinite.Environment Row :=
  ⟨fun name => witness rank (newEnv.types name) family, newEnv.roles⟩

private def newEnvironment (oldEnv : CommonFinite.Environment Row) :
    CommonNominalFinite.Environment Row := ⟨fun name => embed (oldEnv.types name), oldEnv.roles⟩

private theorem project_successor_new (rank : Nat)
    (previous : ∀ first last : Old, NewLe rank (embed first) (embed last) ↔ OldLe rank first last)
    (newEnv : CommonNominalFinite.Environment Row) (family : List Old) (type : Old)
    (supported : ∀ input ∈ inputs type, input ∈ family)
    (obs : CommonNominalFinite.Observation Row) :
    CommonNominalFinite.ProbeAt Common.rowLe (rank + 1) newEnv (embed type) obs ↔
      CommonFinite.ProbeAt Common.rowLe (rank + 1)
        (oldWitnessEnvironment rank newEnv family) type (project obs) := by
  apply project_step (oldWitnessEnvironment rank newEnv family) newEnv rfl
    (fun expected input => ∀ next obs,
      CommonFinite.ProbeAt Common.rowLe rank next input obs →
        CommonFinite.ProbeAt Common.rowLe rank next expected obs)
    (fun expected input => ∀ next obs,
      CommonNominalFinite.ProbeAt Common.rowLe rank next input obs →
        CommonNominalFinite.ProbeAt Common.rowLe rank next expected obs) type _ [] obs
  apply (compatible_iff _ _ _ _ _).mpr
  intro input present name
  exact (CommonNominalFinite.producerLeAt_iff_probe _ _ _).symm.trans
    ((witness_exact rank previous (newEnv.types name) family input (supported input present)).trans
      (CommonFinite.producerLeAt_iff_probe _ _ _))

private theorem project_successor_old (rank : Nat)
    (previous : ∀ first last : Old, NewLe rank (embed first) (embed last) ↔ OldLe rank first last)
    (oldEnv : CommonFinite.Environment Row) (type : Old)
    (obs : CommonNominalFinite.Observation Row) :
    CommonNominalFinite.ProbeAt Common.rowLe (rank + 1) (newEnvironment oldEnv) (embed type) obs ↔
      CommonFinite.ProbeAt Common.rowLe (rank + 1) oldEnv type (project obs) := by
  apply project_step oldEnv (newEnvironment oldEnv) rfl
    (fun expected input => ∀ next obs,
      CommonFinite.ProbeAt Common.rowLe rank next input obs →
        CommonFinite.ProbeAt Common.rowLe rank next expected obs)
    (fun expected input => ∀ next obs,
      CommonNominalFinite.ProbeAt Common.rowLe rank next input obs →
        CommonNominalFinite.ProbeAt Common.rowLe rank next expected obs) type _ [] obs
  apply (compatible_iff _ _ _ _ _).mpr
  intro input _ name
  exact (CommonNominalFinite.producerLeAt_iff_probe _ _ _).symm.trans
    ((previous (oldEnv.types name) input).trans (CommonFinite.producerLeAt_iff_probe _ _ _))

/-- Every rank and every pair of old finite types. The forward and backward
proofs quantify arbitrary extended environments; no nominal-free environment
premise is introduced. The finite intersection witness is shared by every
arrow input observed in both endpoints. -/
theorem finite_order_rank_exact (rank : Nat) (first last : Old) :
    NewLe rank (embed first) (embed last) ↔ OldLe rank first last := by
  induction rank generalizing first last with
  | zero =>
      constructor
      · intro below
        apply (CommonFinite.producerLeAt_iff_probe _ _ _).mpr
        intro env obs accepted
        have translated : CommonNominalFinite.ProbeAt Common.rowLe 0
            (newEnvironment env) (embed last) (lift obs) := by
          apply (project_zero env (newEnvironment env) rfl last (lift obs)).mpr
          simpa only [project_lift] using accepted
        have supplied := (CommonNominalFinite.producerLeAt_iff_probe _ _ _).mp below _ _ translated
        simpa only [project_lift] using
          (project_zero env (newEnvironment env) rfl first (lift obs)).mp supplied
      · intro below
        apply (CommonNominalFinite.producerLeAt_iff_probe _ _ _).mpr
        intro env obs accepted
        let oldEnv : CommonFinite.Environment Row := ⟨fun _ => .bottom, env.roles⟩
        apply (project_zero oldEnv env rfl first obs).mpr
        exact (CommonFinite.producerLeAt_iff_probe _ _ _).mp below _ _
          ((project_zero oldEnv env rfl last obs).mp accepted)
  | succ rank previous =>
      constructor
      · intro below
        apply (CommonFinite.producerLeAt_iff_probe _ _ _).mpr
        intro env obs accepted
        have translated : CommonNominalFinite.ProbeAt Common.rowLe (rank + 1)
            (newEnvironment env) (embed last) (lift obs) := by
          apply (project_successor_old rank previous env last (lift obs)).mpr
          simpa only [project_lift] using accepted
        have supplied := (CommonNominalFinite.producerLeAt_iff_probe _ _ _).mp below _ _ translated
        simpa only [project_lift] using
          (project_successor_old rank previous env first (lift obs)).mp supplied
      · intro below
        apply (CommonNominalFinite.producerLeAt_iff_probe _ _ _).mpr
        intro env obs accepted
        let family := inputs first ++ inputs last
        have firstSupport : ∀ input ∈ inputs first, input ∈ family :=
          fun _ member => List.mem_append.mpr (Or.inl member)
        have lastSupport : ∀ input ∈ inputs last, input ∈ family :=
          fun _ member => List.mem_append.mpr (Or.inr member)
        apply (project_successor_new rank previous env family first firstSupport obs).mpr
        exact (CommonFinite.producerLeAt_iff_probe _ _ _).mp below _ _
          ((project_successor_new rank previous env family last lastSupport obs).mp accepted)

/-- The previously missing finite conservativity proposition, now proved. -/
theorem finite_order_conservative : CommonNominalEmbedding.FiniteOrderConservative := by
  intro first last
  exact forall_congr' fun rank => finite_order_rank_exact rank first last

/-- Arbitrary old Common types, with arbitrary regular graphs, default/mask
records, arrows and rows. Their order is preserved and reflected in the full
nested nominal/float carrier, without an extra hypothesis. -/
theorem common_subtype_exact (first last : Common.Ty) :
    CommonNominalCarrier.Subtype (CommonNominalEmbedding.embed first) (CommonNominalEmbedding.embed last) ↔
      Common.Subtype first last :=
  CommonNominalEmbedding.old_order_of_finite_conservativity finite_order_conservative first last

end Yulang.CommonNominalConservativity
