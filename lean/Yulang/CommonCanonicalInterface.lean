import Yulang.CommonCanonicalShapes

/-!
# Self-contained codes for finite common constructor families

The constructor tree, labels and shared row IDs are part of the code. Unlike
`CommonCanonicalShapes`, two inputs need not be indexed by the same shape.
Equality is the independent common-demand equality for all simultaneous type
and row assignments. The proof separates different constructors and labels
by their actual observations, and separates row IDs by concrete row sets.

This finite grammar contains arbitrary nested pairs, single required fields,
tags and arrows with scalar-lattice domains. Scalar leaves retain arbitrary
shared common-type parameters. Unions between the same declared shape are
collected componentwise by the existing pass before encoding. Mixed-head
lattice expressions, general record spines, regular interfaces and existential
reparameterization are not claimed by this module.
-/

namespace Yulang.CommonCanonicalInterface

open ProducerCanonicalOpen (Expr Atom)
open ProducerCanonicalShapes (Shape Term Bundle collect)
open CommonFinite (ProbeAt ProbeStep MaskedProbeStep)
open ProducerContextual (Head)

variable {n : Nat}

/-- A finite constructor tree with no hidden shape index. -/
inductive Form (n : Nat) where
  | scalar : Expr n → Form n
  | pair : Form n → Form n → Form n
  | required : Nat → Form n → Form n
  | variant : Nat → Form n → Form n
  | arrow : Nat → Nat → Expr n → Form n → Form n
  deriving DecidableEq, Repr

def Form.instantiate (rows : Nat → Common.Row) (parameters : Fin n → Common.Ty) :
    Form n → Common.Ty
  | .scalar expression => CommonCanonicalOpen.instantiate parameters expression
  | .pair first last => Common.pair (first.instantiate rows parameters) (last.instantiate rows parameters)
  | .required label payload => Common.required label (payload.instantiate rows parameters)
  | .variant label payload => Common.variant label (payload.instantiate rows parameters)
  | .arrow incoming outgoing input output =>
      Common.arrow (CommonCanonicalOpen.instantiate parameters input) (rows incoming)
        (output.instantiate rows parameters) (rows outgoing)

/-- The code includes every constructor, label and row-slot ID. -/
inductive Code (n : Nat) where
  | scalar : List (List (Atom n)) → Code n
  | pair : Code n → Code n → Code n
  | required : Nat → Code n → Code n
  | variant : Nat → Code n → Code n
  | arrow : Nat → Nat → List (List (Atom n)) → Code n → Code n
  deriving DecidableEq, Repr

def encode : Form n → Code n
  | .scalar expression => .scalar (CommonCanonicalOpen.canonicalEncoding expression)
  | .pair first last => .pair (encode first) (encode last)
  | .required label payload => .required label (encode payload)
  | .variant label payload => .variant label (encode payload)
  | .arrow incoming outgoing input output =>
      .arrow incoming outgoing (CommonCanonicalOpen.canonicalEncoding input) (encode output)

def Code.readback : Code n → Form n
  | .scalar code => .scalar (ProducerCanonicalOpenClauses.readback code)
  | .pair first last => .pair first.readback last.readback
  | .required label payload => .required label payload.readback
  | .variant label payload => .variant label payload.readback
  | .arrow incoming outgoing input output =>
      .arrow incoming outgoing (ProducerCanonicalOpenClauses.readback input) output.readback

def normalize (expression : Form n) : Form n := (encode expression).readback

def Equivalent (first last : Form n) : Prop :=
  ∀ rows : Nat → Common.Row, ∀ parameters : Fin n → Common.Ty,
    Common.Equivalent (first.instantiate rows parameters) (last.instantiate rows parameters)

def Form.root : Form n → Option Head
  | .scalar _ => none
  | .pair _ _ => some .pair
  | .required _ _ => some .records
  | .variant label _ => some (.variant label)
  | .arrow _ _ _ _ => some .arrow

private def roleEnvironment (roles : List Head) : CommonFinite.Environment Common.Row :=
  ⟨fun _ => .bottom, fun _ => roles⟩

private def roleProbe (roles : List Head) (type : Common.Ty) : Prop :=
  ProbeAt Common.rowLe 0 (roleEnvironment roles) (Common.observeTy 1 type) (.role 0)

private theorem scalar_role_nonbase (expression : Expr n) (head : Head)
    (notBase : ∀ scalar, Head.base scalar ≠ head) :
    roleProbe [] (CommonCanonicalOpen.instantiate (fun _ => .bottom) expression) ↔
      roleProbe [head] (CommonCanonicalOpen.instantiate (fun _ => .bottom) expression) := by
  induction expression with
  | atom entry =>
      cases entry <;>
        simp [roleProbe, CommonCanonicalOpen.instantiate, CommonCanonicalOpen.atomType,
          Common.observeTy, CommonSyntax.Layer.evalAt, ProbeAt, ProbeStep, MaskedProbeStep,
          roleEnvironment, notBase]
  | bottom | top => rfl
  | union first last ihf ihl | inter first last ihf ihl =>
      simpa [roleProbe, CommonCanonicalOpen.instantiate, Common.observeTy,
        CommonSyntax.Layer.evalAt] using (by first | exact and_congr ihf ihl | exact or_congr ihf ihl)

private theorem root_role (form : Form n) (head : Head) (root : form.root = some head)
    (rows : Nat → Common.Row) (parameters : Fin n → Common.Ty) (roles : List Head) :
    roleProbe roles (form.instantiate rows parameters) ↔ head ∈ roles := by
  cases form <;> simp_all [Form.root, Form.instantiate, roleProbe, Common.observeTy,
    Common.pair, Common.required, Common.record, Common.emptyRecord, Common.variant,
    Common.arrow, CommonSyntax.Layer.evalAt, ProbeAt, ProbeStep, MaskedProbeStep, roleEnvironment]

private theorem root_nonbase (form : Form n) (head : Head) (root : form.root = some head)
    (scalar : Inference.Base) : Head.base scalar ≠ head := by
  cases form <;> simp_all [Form.root]
  all_goals subst head; simp

private theorem equivalent_role {first last : Form n} (same : Equivalent first last)
    (rows : Nat → Common.Row) (parameters : Fin n → Common.Ty) (roles : List Head) :
    roleProbe roles (first.instantiate rows parameters) ↔
      roleProbe roles (last.instantiate rows parameters) :=
  (CommonCanonicalShapes.equivalent_iff_probes _ _).mp (same rows parameters)
    1 0 (roleEnvironment roles) (.role 0)

private theorem scalar_not_root (expression : Expr n) (form : Form n) (head : Head)
    (root : form.root = some head) : ¬ Equivalent (.scalar expression) form := by
  intro same
  let rows : Nat → Common.Row := fun _ => Common.rowEmpty
  let parameters : Fin n → Common.Ty := fun _ => .bottom
  have empty := equivalent_role same rows parameters []
  have singleton := equivalent_role same rows parameters [head]
  have invariant := scalar_role_nonbase expression head (root_nonbase form head root)
  have none : ¬ roleProbe [] (form.instantiate rows parameters) := by
    rw [root_role form head root]
    simp
  have some : roleProbe [head] (form.instantiate rows parameters) := by
    rw [root_role form head root]
    simp
  exact none (empty.mp (invariant.mpr (singleton.mpr some)))

theorem equivalent_symm {first last : Form n} (same : Equivalent first last) : Equivalent last first :=
  fun rows parameters => Common.equivalent_symm (same rows parameters)

/-- Root constructor differences are reflected by the independent demands,
even when scalar leaves contain arbitrary shared common parameters. -/
theorem equivalent_root {first last : Form n} (same : Equivalent first last) : first.root = last.root := by
  cases firstRoot : first.root with
  | none =>
      cases lastRoot : last.root with
      | none => rfl
      | some head =>
          cases first <;> simp_all [Form.root]
          exact False.elim (scalar_not_root _ last head lastRoot same)
  | some firstHead =>
      cases lastRoot : last.root with
      | none =>
          cases last <;> simp_all [Form.root]
          exact False.elim (scalar_not_root _ first firstHead firstRoot (equivalent_symm same))
      | some lastHead =>
          have observed := equivalent_role same (fun _ => Common.rowEmpty)
            (fun _ => .bottom) [firstHead]
          rw [root_role first firstHead firstRoot, root_role last lastHead lastRoot] at observed
          have equal : lastHead = firstHead := by simpa using observed.mp (by simp)
          simp [equal]

private theorem required_presence (label current : Nat) (payload : Common.Ty) :
    ProbeAt Common.rowLe 0 (roleEnvironment []) (Common.observeTy 1 (Common.required label payload))
      (.field current .trivial) ↔ current = label := by
  simp [Common.required, Common.record, Common.emptyRecord, Common.observeTy,
    CommonSyntax.Layer.evalAt, ProbeAt, ProbeStep, MaskedProbeStep]

theorem equivalent_required_label {label label' : Nat} {payload payload' : Form n}
    (same : Equivalent (.required label payload) (.required label' payload')) : label = label' := by
  have observed := (CommonCanonicalShapes.equivalent_iff_probes _ _).mp
    (same (fun _ => Common.rowEmpty) (fun _ => .bottom))
    1 0 (roleEnvironment []) (.field label .trivial)
  change (_ ↔ _) at observed
  simp only [Form.instantiate, required_presence] at observed
  exact observed.mp True.intro

private theorem row_ids_equal {first last : Nat}
    (equal : ∀ rows : Nat → Common.Row, rows first = rows last) : first = last := by
  let rows : Nat → Common.Row := fun index _ => index = first
  have observed := congrFun (equal rows) (0, [])
  have lastEq : last = first := Eq.mp observed rfl
  exact lastEq.symm

theorem equivalent_arrow_rows {incoming outgoing incoming' outgoing' : Nat}
    {input input' : Expr n} {output output' : Form n}
    (same : Equivalent (.arrow incoming outgoing input output) (.arrow incoming' outgoing' input' output')) :
    incoming = incoming' ∧ outgoing = outgoing' := by
  have compare (rows : Nat → Common.Row) := same rows (fun _ => .bottom)
  have split (rows : Nat → Common.Row) :=
    (Common.common_arrow_iff _ _ _ _ _ _ _ _).mp (compare rows).1
  have reverse (rows : Nat → Common.Row) :=
    (Common.common_arrow_iff _ _ _ _ _ _ _ _).mp (compare rows).2
  exact ⟨row_ids_equal (fun rows => Common.rowLe_antisymm (reverse rows).2.1 (split rows).2.1),
    row_ids_equal (fun rows => Common.rowLe_antisymm (split rows).2.2.2 (reverse rows).2.2.2)⟩

theorem equivalent_scalar_iff (first last : Expr n) :
    Equivalent (.scalar first) (.scalar last) ↔ CommonCanonicalOpen.Equivalent first last := by
  exact ⟨fun same => same (fun _ => Common.rowEmpty), fun same _ => same⟩

theorem equivalent_pair_iff (first last first' last' : Form n) :
    Equivalent (.pair first last) (.pair first' last') ↔
      Equivalent first first' ∧ Equivalent last last' := by
  simp only [Equivalent, Form.instantiate, CommonCanonicalShapes.pair_equivalent_iff, forall_and]

theorem equivalent_required_iff (label : Nat) (first last : Form n) :
    Equivalent (.required label first) (.required label last) ↔ Equivalent first last := by
  simp only [Equivalent, Form.instantiate, CommonCanonicalShapes.required_equivalent_iff]

theorem equivalent_variant_iff (label : Nat) (first last : Form n) :
    Equivalent (.variant label first) (.variant label last) ↔ Equivalent first last := by
  simp only [Equivalent, Form.instantiate, CommonCanonicalShapes.variant_equivalent_iff]

theorem equivalent_arrow_iff (incoming outgoing : Nat) (input input' : Expr n) (output output' : Form n) :
    Equivalent (.arrow incoming outgoing input output) (.arrow incoming outgoing input' output') ↔
      CommonCanonicalOpen.Equivalent input input' ∧ Equivalent output output' := by
  simp only [Equivalent, Form.instantiate, CommonCanonicalShapes.arrow_equivalent_iff, forall_and]
  constructor
  · rintro ⟨inputs, outputs⟩
    exact ⟨inputs (fun _ => Common.rowEmpty), outputs⟩
  · rintro ⟨inputs, outputs⟩
    exact ⟨fun _ => inputs, outputs⟩

/-- Exactness compares arbitrary constructor trees. In particular it does
not assume equal shapes, labels, or row IDs before comparing the codes. -/
theorem canonicalEncoding_exact (first last : Form n) : Equivalent first last ↔ encode first = encode last := by
  constructor
  · intro same
    induction first generalizing last with
    | scalar expression =>
        have root := equivalent_root same
        cases last <;> simp [Form.root] at root
        rename_i other
        exact congrArg Code.scalar ((CommonCanonicalOpen.canonicalEncoding_exact expression other).mp
          ((equivalent_scalar_iff _ _).mp same))
    | pair first last ihf ihl =>
        have root := equivalent_root same
        cases last <;> simp [Form.root] at root
        rename_i first' last'
        have pieces := (equivalent_pair_iff _ _ _ _).mp same
        simp only [encode, ihf first' pieces.1, ihl last' pieces.2]
    | required label payload ih =>
        have root := equivalent_root same
        cases last <;> simp [Form.root] at root
        rename_i label' payload'
        have labels := equivalent_required_label same
        subst label'
        exact congrArg (Code.required label) (ih payload' ((equivalent_required_iff _ _ _).mp same))
    | variant label payload ih =>
        have root := equivalent_root same
        cases last <;> simp [Form.root] at root
        rename_i label' payload'
        subst label'
        exact congrArg (Code.variant label) (ih payload' ((equivalent_variant_iff _ _ _).mp same))
    | arrow incoming outgoing input output ih =>
        have root := equivalent_root same
        cases last <;> simp [Form.root] at root
        rename_i incoming' outgoing' input' output'
        obtain ⟨inputs, outputs⟩ := equivalent_arrow_rows same
        subst incoming'
        subst outgoing'
        have pieces := (equivalent_arrow_iff _ _ _ _ _ _).mp same
        simp only [encode, (CommonCanonicalOpen.canonicalEncoding_exact _ _).mp pieces.1,
          ih output' pieces.2]
  · intro equal
    induction first generalizing last with
    | scalar expression =>
        cases last <;> simp [encode] at equal
        rename_i other
        exact (equivalent_scalar_iff _ _).mpr ((CommonCanonicalOpen.canonicalEncoding_exact _ _).mpr equal)
    | pair first last ihf ihl =>
        cases last <;> simp [encode] at equal
        rename_i first' last'
        exact (equivalent_pair_iff _ _ _ _).mpr ⟨ihf first' equal.1, ihl last' equal.2⟩
    | required label payload ih =>
        cases last <;> simp [encode] at equal
        rename_i label' payload'
        obtain ⟨rfl, payloads⟩ := equal
        exact (equivalent_required_iff _ _ _).mpr (ih payload' payloads)
    | variant label payload ih =>
        cases last <;> simp [encode] at equal
        rename_i label' payload'
        obtain ⟨rfl, payloads⟩ := equal
        exact (equivalent_variant_iff _ _ _).mpr (ih payload' payloads)
    | arrow incoming outgoing input output ih =>
        cases last <;> simp [encode] at equal
        rename_i incoming' outgoing' input' output'
        obtain ⟨rfl, rfl, inputs, outputs⟩ := equal
        exact (equivalent_arrow_iff _ _ _ _ _ _).mpr
          ⟨(CommonCanonicalOpen.canonicalEncoding_exact _ _).mpr inputs, ih output' outputs⟩

theorem normalize_equivalent (expression : Form n) : Equivalent (normalize expression) expression := by
  induction expression with
  | scalar expression =>
      exact (equivalent_scalar_iff _ _).mpr (CommonCanonicalOpen.normalize_equivalent expression)
  | pair first last ihf ihl => exact (equivalent_pair_iff _ _ _ _).mpr ⟨ihf, ihl⟩
  | required label payload ih => exact (equivalent_required_iff _ _ _).mpr ih
  | variant label payload ih => exact (equivalent_variant_iff _ _ _).mpr ih
  | arrow incoming outgoing input output ih =>
      exact (equivalent_arrow_iff _ _ _ _ _ _).mpr
        ⟨CommonCanonicalOpen.normalize_equivalent input, ih⟩

theorem normalize_exact (first last : Form n) :
    Equivalent first last ↔ normalize first = normalize last := by
  constructor
  · intro same
    exact congrArg Code.readback ((canonicalEncoding_exact _ _).mp same)
  · intro equal rows parameters
    have hf := normalize_equivalent first rows parameters
    have hl := normalize_equivalent last rows parameters
    rw [equal] at hf
    exact Common.equivalent_trans (Common.equivalent_symm hf) hl

theorem normalize_idempotent (expression : Form n) : normalize (normalize expression) = normalize expression :=
  (normalize_exact _ _).mp (normalize_equivalent expression)

def fromBundle : (shape : Shape) → Bundle n shape → Form n
  | .scalar, expression => .scalar expression
  | .pair first last, fields => .pair (fromBundle first fields.1) (fromBundle last fields.2)
  | .required label payload, fields => .required label (fromBundle payload fields)
  | .variant label payload, fields => .variant label (fromBundle payload fields)
  | .arrow incoming outgoing result, fields =>
      .arrow incoming outgoing fields.1 (fromBundle result fields.2)

theorem fromBundle_instantiate (shape : Shape) (fields : Bundle n shape)
    (rows : Nat → Common.Row) (parameters : Fin n → Common.Ty) :
    (fromBundle shape fields).instantiate rows parameters =
      CommonCanonicalShapes.instantiateBundle rows parameters shape fields := by
  induction shape with
  | scalar => rfl
  | pair first last ihf ihl =>
      simp only [fromBundle, Form.instantiate, CommonCanonicalShapes.instantiateBundle, ihf, ihl]
  | required label payload ih => exact congrArg (Common.required label) (ih fields)
  | variant label payload ih => exact congrArg (Common.variant label) (ih fields)
  | arrow incoming outgoing result ih =>
      simp only [fromBundle, Form.instantiate, CommonCanonicalShapes.instantiateBundle, ih]

def fromTerm {shape : Shape} (expression : Term n shape) : Form n := fromBundle shape (collect expression)

theorem fromTerm_equivalent {shape : Shape} (expression : Term n shape)
    (rows : Nat → Common.Row) (parameters : Fin n → Common.Ty) :
    Common.Equivalent ((fromTerm expression).instantiate rows parameters)
      (CommonCanonicalShapes.instantiate rows parameters expression) := by
  rw [fromTerm, fromBundle_instantiate]
  exact CommonCanonicalShapes.collect_equivalent rows parameters expression

/-- The source shape travels with the source rather than being an external
precondition shared by the two interfaces under comparison. -/
structure Interface (n : Nat) where
  shape : Shape
  body : Term n shape

def Interface.instantiate (rows : Nat → Common.Row) (parameters : Fin n → Common.Ty)
    (interface : Interface n) : Common.Ty :=
  CommonCanonicalShapes.instantiate rows parameters interface.body

def Interface.Equivalent (first last : Interface n) : Prop :=
  ∀ rows : Nat → Common.Row, ∀ parameters : Fin n → Common.Ty,
    Common.Equivalent (first.instantiate rows parameters) (last.instantiate rows parameters)

def Interface.canonicalEncoding (interface : Interface n) : Code n := encode (fromTerm interface.body)

def Interface.normalize (interface : Interface n) : Form n :=
  CommonCanonicalInterface.normalize (fromTerm interface.body)

private theorem interface_equivalent_forms (first last : Interface n) :
    first.Equivalent last ↔ Equivalent (fromTerm first.body) (fromTerm last.body) := by
  constructor
  · intro same rows parameters
    exact Common.equivalent_trans (fromTerm_equivalent first.body rows parameters)
      (Common.equivalent_trans (same rows parameters)
        (Common.equivalent_symm (fromTerm_equivalent last.body rows parameters)))
  · intro same rows parameters
    exact Common.equivalent_trans (Common.equivalent_symm (fromTerm_equivalent first.body rows parameters))
      (Common.equivalent_trans (same rows parameters) (fromTerm_equivalent last.body rows parameters))

/-- For every finite parameter count and any two declared finite constructor
interfaces, uniform common-demand equivalence holds exactly when the complete
finite codes agree. Shared row IDs are universally instantiated, not erased. -/
theorem interface_canonicalEncoding_exact (first last : Interface n) :
    first.Equivalent last ↔ first.canonicalEncoding = last.canonicalEncoding :=
  (interface_equivalent_forms first last).trans (canonicalEncoding_exact _ _)

theorem interface_normalize_exact (first last : Interface n) :
    first.Equivalent last ↔ first.normalize = last.normalize :=
  (interface_equivalent_forms first last).trans (normalize_exact _ _)

theorem interface_normalize_equivalent (interface : Interface n)
    (rows : Nat → Common.Row) (parameters : Fin n → Common.Ty) :
    Common.Equivalent (interface.normalize.instantiate rows parameters) (interface.instantiate rows parameters) :=
  Common.equivalent_trans (normalize_equivalent (fromTerm interface.body) rows parameters)
    (fromTerm_equivalent interface.body rows parameters)

namespace Examples

theorem required_labels_are_part_of_code (first last : Nat) (payload : Form n) :
    encode (.required first payload) = encode (.required last payload) ↔ first = last := by
  simp [encode]

theorem shared_arrow_rows_are_part_of_code (first first' last last' : Nat)
    (input : Expr n) (output : Form n) :
    encode (.arrow first last input output) = encode (.arrow first' last' input output) ↔
      first = first' ∧ last = last' := by
  simp [encode]

theorem int_str_order_fixed :
    normalize (n := 0) (.scalar (.union (.atom (.base .str)) (.atom (.base .int)))) =
      .scalar (.union (.atom (.base .int)) (.atom (.base .str))) := by
  decide +kernel

end Examples

end Yulang.CommonCanonicalInterface
