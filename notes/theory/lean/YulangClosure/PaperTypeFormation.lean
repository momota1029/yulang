import YulangClosure.PaperTypeSubstitution

/-!
Paper-faithful formation layer over the frozen substitution algebra. Record
presence is explicitly encoded in r1's two tags; those tags carry no claim about
field mutability. This file proves only formation/operation-signature facts,
not the full typing-substitution lemma or executor safety.
-/
namespace YulangClosure.PaperTypes

inductive Presence where
  | required | optional
  deriving DecidableEq, Repr

def Presence.encode : Presence → Mutability
  | .required => .immutable
  | .optional => .mutable

def Presence.decode : Mutability → Presence
  | .immutable => .required
  | .mutable => .optional

@[simp] theorem Presence.decode_encode (p : Presence) :
    Presence.decode p.encode = p := by cases p <;> rfl

@[simp] theorem Presence.encode_decode (p : Mutability) :
    Presence.encode (Presence.decode p) = p := by cases p <;> rfl

def recordPresence (encoded : Mutability) : Presence := Presence.decode encoded

mutual
  inductive Formed : Nat → Ty → Prop where
    | var {scope i} : i < scope → Formed scope (.var i)
    | base {scope b} : Formed scope (.base b)
    | top {scope} : Formed scope .top
    | bottom {scope} : Formed scope .bottom
    | union {scope a b} : Formed scope a → Formed scope b → Formed scope (.union a b)
    | intersection {scope a b} : Formed scope a → Formed scope b → Formed scope (.intersection a b)
    | tuple {scope xs} : TupleFormed scope xs → Formed scope xs
    | record {scope fields labels} : RecordFormed scope fields labels → Formed scope fields
    | variant {scope arms labels} : VariantFormed scope arms labels → Formed scope arms
    | nominal {scope id args} : ArgumentFormed scope args → Formed scope (.nominal id args)
    | mu {scope body} : Formed (scope + 1) body → Formed scope (.mu body)
    | thunk {scope result} : Formed scope result → Formed scope (.thunk result)
    | callable {scope carrier result} : Formed scope carrier → Formed scope result → Formed scope (.callable carrier result)
    | poly {scope body} : Formed (scope + 1) body → Formed scope (.poly body)

  inductive TupleFormed : Nat → Ty → Prop where
    | nil {scope} : TupleFormed scope .tupleNil
    | cons {scope head tail} : Formed scope head → TupleFormed scope tail → TupleFormed scope (.tupleCons head tail)

  inductive ArgumentFormed : Nat → Ty → Prop where
    | nil {scope} : ArgumentFormed scope .tupleNil
    | cons {scope head tail} : Formed scope head → ArgumentFormed scope tail → ArgumentFormed scope (.tupleCons head tail)

  inductive RecordFormed : Nat → Ty → List Nat → Prop where
    | nil {scope} : RecordFormed scope .recordNil []
    | cons {scope label field tail labels} {presence : Presence} :
        Formed scope field → RecordFormed scope tail labels → label ∉ labels →
        RecordFormed scope (.recordCons label (Presence.encode presence) field tail) (label :: labels)

  inductive VariantFormed : Nat → Ty → List Nat → Prop where
    | nil {scope} : VariantFormed scope .variantNil []
    | cons {scope label payloads tail labels} : ArgumentFormed scope payloads →
        VariantFormed scope tail labels → label ∉ labels →
        VariantFormed scope (.variantCons label payloads tail) (label :: labels)
end

mutual
  theorem formed_mapVars {source target : Nat} (ρ : Nat → Nat) {t : Ty}
      (h : Formed source t) (mapScope : ∀ i, i < source → ρ i < target) :
      Formed target (mapVars ρ t) := by
    cases h with
    | var hi => exact .var (mapScope _ hi)
    | base => exact .base
    | top => exact .top
    | bottom => exact .bottom
    | union ha hb => exact .union (formed_mapVars ρ ha mapScope) (formed_mapVars ρ hb mapScope)
    | intersection ha hb => exact .intersection (formed_mapVars ρ ha mapScope) (formed_mapVars ρ hb mapScope)
    | tuple hx => exact .tuple (tuple_mapVars ρ hx mapScope)
    | record hx => exact .record (record_mapVars ρ hx mapScope)
    | variant hx => exact .variant (variant_mapVars ρ hx mapScope)
    | nominal hx => exact .nominal (arguments_mapVars ρ hx mapScope)
    | mu hb =>
        apply Formed.mu
        apply formed_mapVars (liftRen ρ) hb
        intro i hi
        cases i with
        | zero => exact Nat.succ_pos _
        | succ i => exact Nat.succ_lt_succ (mapScope i (Nat.lt_of_succ_lt_succ hi))
    | thunk hr => exact .thunk (formed_mapVars ρ hr mapScope)
    | callable hc hr => exact .callable (formed_mapVars ρ hc mapScope) (formed_mapVars ρ hr mapScope)
    | poly hb =>
        apply Formed.poly
        apply formed_mapVars (liftRen ρ) hb
        intro i hi
        cases i with
        | zero => exact Nat.succ_pos _
        | succ i => exact Nat.succ_lt_succ (mapScope i (Nat.lt_of_succ_lt_succ hi))

  theorem tuple_mapVars {source target : Nat} (ρ : Nat → Nat) {xs : Ty}
      (h : TupleFormed source xs) (mapScope : ∀ i, i < source → ρ i < target) :
      TupleFormed target (mapVars ρ xs) := by
    cases h with
    | nil => exact .nil
    | cons hh ht => exact .cons (formed_mapVars ρ hh mapScope) (tuple_mapVars ρ ht mapScope)

  theorem arguments_mapVars {source target : Nat} (ρ : Nat → Nat) {xs : Ty}
      (h : ArgumentFormed source xs) (mapScope : ∀ i, i < source → ρ i < target) :
      ArgumentFormed target (mapVars ρ xs) := by
    cases h with
    | nil => exact .nil
    | cons hh ht => exact .cons (formed_mapVars ρ hh mapScope) (arguments_mapVars ρ ht mapScope)

  theorem record_mapVars {source target : Nat} (ρ : Nat → Nat) {xs : Ty} {labels : List Nat}
      (h : RecordFormed source xs labels) (mapScope : ∀ i, i < source → ρ i < target) :
      RecordFormed target (mapVars ρ xs) labels := by
    cases h with
    | nil => exact .nil
    | cons hh ht hlabels => exact .cons (formed_mapVars ρ hh mapScope) (record_mapVars ρ ht mapScope) hlabels

  theorem variant_mapVars {source target : Nat} (ρ : Nat → Nat) {xs : Ty} {labels : List Nat}
      (h : VariantFormed source xs labels) (mapScope : ∀ i, i < source → ρ i < target) :
      VariantFormed target (mapVars ρ xs) labels := by
    cases h with
    | nil => exact .nil
    | cons hh ht hlabels => exact .cons (arguments_mapVars ρ hh mapScope) (variant_mapVars ρ ht mapScope) hlabels
end

mutual
  theorem formed_subst {source target : Nat} (σ : Nat → Ty) {t : Ty}
      (h : Formed source t) (subScope : ∀ i, i < source → Formed target (σ i)) :
      Formed target (subst σ t) := by
    cases h with
    | var hi => exact subScope _ hi
    | base => exact .base
    | top => exact .top
    | bottom => exact .bottom
    | union ha hb => exact .union (formed_subst σ ha subScope) (formed_subst σ hb subScope)
    | intersection ha hb => exact .intersection (formed_subst σ ha subScope) (formed_subst σ hb subScope)
    | tuple hx => exact .tuple (tuple_subst σ hx subScope)
    | record hx => exact .record (record_subst σ hx subScope)
    | variant hx => exact .variant (variant_subst σ hx subScope)
    | nominal hx => exact .nominal (arguments_subst σ hx subScope)
    | mu hb =>
        apply Formed.mu
        apply formed_subst (liftSub σ) hb
        intro i hi
        cases i with
        | zero => exact .var (Nat.zero_lt_succ _)
        | succ i =>
            apply formed_mapVars Nat.succ (subScope i (Nat.lt_of_succ_lt_succ hi))
            intro j hj
            exact Nat.succ_lt_succ hj
    | thunk hr => exact .thunk (formed_subst σ hr subScope)
    | callable hc hr => exact .callable (formed_subst σ hc subScope) (formed_subst σ hr subScope)
    | poly hb =>
        apply Formed.poly
        apply formed_subst (liftSub σ) hb
        intro i hi
        cases i with
        | zero => exact .var (Nat.zero_lt_succ _)
        | succ i =>
            apply formed_mapVars Nat.succ (subScope i (Nat.lt_of_succ_lt_succ hi))
            intro j hj
            exact Nat.succ_lt_succ hj

  theorem tuple_subst {source target : Nat} (σ : Nat → Ty) {xs : Ty}
      (h : TupleFormed source xs) (subScope : ∀ i, i < source → Formed target (σ i)) :
      TupleFormed target (subst σ xs) := by
    cases h with
    | nil => exact .nil
    | cons hh ht => exact .cons (formed_subst σ hh subScope) (tuple_subst σ ht subScope)

  theorem arguments_subst {source target : Nat} (σ : Nat → Ty) {xs : Ty}
      (h : ArgumentFormed source xs) (subScope : ∀ i, i < source → Formed target (σ i)) :
      ArgumentFormed target (subst σ xs) := by
    cases h with
    | nil => exact .nil
    | cons hh ht => exact .cons (formed_subst σ hh subScope) (arguments_subst σ ht subScope)

  theorem record_subst {source target : Nat} (σ : Nat → Ty) {xs : Ty} {labels : List Nat}
      (h : RecordFormed source xs labels) (subScope : ∀ i, i < source → Formed target (σ i)) :
      RecordFormed target (subst σ xs) labels := by
    cases h with
    | nil => exact .nil
    | cons hh ht hlabels => exact .cons (formed_subst σ hh subScope) (record_subst σ ht subScope) hlabels

  theorem variant_subst {source target : Nat} (σ : Nat → Ty) {xs : Ty} {labels : List Nat}
      (h : VariantFormed source xs labels) (subScope : ∀ i, i < source → Formed target (σ i)) :
      VariantFormed target (subst σ xs) labels := by
    cases h with
    | nil => exact .nil
    | cons hh ht hlabels => exact .cons (arguments_subst σ hh subScope) (variant_subst σ ht subScope) hlabels
end

def argsSyntax : List Ty → Ty
  | [] => .tupleNil
  | a :: rest => .tupleCons a (argsSyntax rest)

inductive ArgsFormed (scope : Nat) : List Ty → Prop where
  | nil : ArgsFormed scope []
  | cons {head tail} : Formed scope head → ArgsFormed scope tail → ArgsFormed scope (head :: tail)

def lookupTypeArgument : List Ty → Nat → Option Ty
  | [], _ => none
  | argument :: _, 0 => some argument
  | _ :: rest, index + 1 => lookupTypeArgument rest index

def instantiateSubstitution (arguments : List Ty) (index : Nat) : Ty :=
  match lookupTypeArgument arguments index with
  | some argument => argument
  | none => .var (index - arguments.length)

structure OperationDeclaration where
  identity : Nat
  typeArity : Nat
  payloadTemplate : Ty
  responseTemplate : Ty
  deriving DecidableEq, Repr

def liftSubN : Nat → (Nat → Ty) → Nat → Ty
  | 0, σ => σ
  | n + 1, σ => liftSub (liftSubN n σ)

def OperationDeclaration.WellFormed (ambient : Nat) (declaration : OperationDeclaration) : Prop :=
  YulangClosure.PaperTypes.Formed (declaration.typeArity + ambient) declaration.payloadTemplate ∧
  YulangClosure.PaperTypes.Formed (declaration.typeArity + ambient) declaration.responseTemplate

def OperationDeclaration.instantiate (declaration : OperationDeclaration)
    (arguments : List Ty) : OperationInstance :=
  let σ := instantiateSubstitution arguments
  { identity := declaration.identity
    typeArguments := argsSyntax arguments
    payloadType := subst σ declaration.payloadTemplate
    responseType := subst σ declaration.responseTemplate }

def OperationDeclaration.substAmbient (σ : Nat → Ty)
    (declaration : OperationDeclaration) : OperationDeclaration :=
  { declaration with
    payloadTemplate := subst (liftSubN declaration.typeArity σ) declaration.payloadTemplate
    responseTemplate := subst (liftSubN declaration.typeArity σ) declaration.responseTemplate }

def mapOperationArguments (σ : Nat → Ty) (arguments : List Ty) : List Ty :=
  arguments.map (subst σ)

theorem liftSubN_bound (n : Nat) (σ : Nat → Ty) (i : Nat) (h : i < n) :
    liftSubN n σ i = .var i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp [liftSubN, liftSub]
      | succ i =>
          have hi : i < n := by omega
          simp [liftSubN, liftSub, ih i hi, mapVars]

theorem liftSubN_free (n : Nat) (σ : Nat → Ty) (i : Nat) (h : n ≤ i) :
    liftSubN n σ i = mapVars (fun j => j + n) (σ (i - n)) := by
  induction n generalizing i with
  | zero =>
      simp only [liftSubN]
      have heq : (fun j => j + 0) = id := by funext j; simp
      simp only [Nat.sub_zero]
      rw [heq, mapVars_id]
  | succ n ih =>
      cases i with
      | zero => omega
      | succ i =>
          have hi : n ≤ i := by omega
          have hsub : i + 1 - (n + 1) = i - n := by omega
          simp only [liftSubN, liftSub]
          rw [ih i hi]
          rw [hsub]
          rw [mapVars_comp]
          congr 1

theorem lookupTypeArgument_map (σ : Nat → Ty) (arguments : List Ty) (i : Nat) :
    lookupTypeArgument (mapOperationArguments σ arguments) i =
      Option.map (subst σ) (lookupTypeArgument arguments i) := by
  induction arguments generalizing i with
  | nil => cases i <;> rfl
  | cons head tail ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i

def OperationInstance.Instantiates (op : OperationInstance)
    (declaration : OperationDeclaration) (arguments : List Ty) : Prop :=
  arguments.length = declaration.typeArity ∧
  op = declaration.instantiate arguments

theorem arguments_formList {scope : Nat} (arguments : List Ty)
    (formed : ArgsFormed scope arguments) :
    ArgumentFormed scope (argsSyntax arguments) := by
  induction formed with
  | nil => exact .nil
  | @cons head tail hhead htail ih => exact .cons hhead (by simpa [argsSyntax] using ih)

theorem formed_get_of_forall {scope : Nat} {arguments : List Ty}
    (formed : ArgsFormed scope arguments) (i : Nat)
    (hi : i < arguments.length) :
    ∃ argument, lookupTypeArgument arguments i = some argument ∧ Formed scope argument := by
  induction formed generalizing i with
  | nil => simp at hi
  | @cons head tail hhead htail ih =>
    cases i with
      | zero => exact ⟨head, rfl, hhead⟩
      | succ i =>
          have hi' : i < tail.length := by simpa using hi
          obtain ⟨argument, hget, hformed⟩ := ih i hi'
          exact ⟨argument, hget, hformed⟩

theorem lookupTypeArgument_none_of_ge (arguments : List Ty) (i : Nat)
    (h : arguments.length ≤ i) : lookupTypeArgument arguments i = none := by
  induction arguments generalizing i with
  | nil => cases i <;> rfl
  | cons head tail ih =>
      cases i with
      | zero => simp at h
      | succ i => apply ih; simpa using h

theorem operation_instantiation_preserves_formation (declaration : OperationDeclaration)
    (ambient : Nat) (args : List Ty)
    (hdecl : declaration.WellFormed ambient)
    (hargs : ArgsFormed ambient args)
    (harity : args.length = declaration.typeArity) :
    Formed ambient (declaration.instantiate args).payloadType ∧
    Formed ambient (declaration.instantiate args).responseType := by
  have hsub : ∀ i, i < declaration.typeArity + ambient →
      Formed ambient (instantiateSubstitution args i) := by
    intro i hi
    by_cases harg : i < args.length
    · obtain ⟨argument, hget, hformed⟩ := formed_get_of_forall hargs i harg
      simp [instantiateSubstitution, hget]
      exact hformed
    · have hindex : i - args.length < ambient := by omega
      have hnone : lookupTypeArgument args i = none :=
        lookupTypeArgument_none_of_ge args i (Nat.le_of_not_lt harg)
      simp [instantiateSubstitution, hnone]
      exact .var hindex
  constructor
  · simpa [OperationDeclaration.instantiate] using
      formed_subst (instantiateSubstitution args) hdecl.1 hsub
  · simpa [OperationDeclaration.instantiate] using
      formed_subst (instantiateSubstitution args) hdecl.2 hsub

def OperationInstance.InstantiatesIn (op : OperationInstance)
    (declarations : List OperationDeclaration) (arguments : List Ty) : Prop :=
  ∃ declaration, declaration ∈ declarations ∧
    op.Instantiates declaration arguments

theorem perform_operation_formations_from_declaration (op : OperationInstance)
    (declarations : List OperationDeclaration) (arguments : List Ty) (ambient : Nat)
    (hinst : op.InstantiatesIn declarations arguments)
    (hargs : ArgsFormed ambient arguments)
    (hdecls : ∀ declaration, declaration ∈ declarations → declaration.WellFormed ambient) :
    Formed ambient op.payloadType ∧ Formed ambient op.responseType := by
  rcases hinst with ⟨declaration, hmember, hin⟩
  obtain ⟨hargsLength, hop⟩ := hin
  subst op
  simpa [OperationDeclaration.instantiate] using
    operation_instantiation_preserves_formation declaration ambient arguments
      (hdecls declaration hmember) hargs hargsLength

theorem operation_instance_fields_from_one_signature (op : OperationInstance)
    (declaration : OperationDeclaration) (arguments : List Ty)
    (h : op.Instantiates declaration arguments) :
    op.identity = declaration.identity ∧
    op.typeArguments = argsSyntax arguments ∧
    op.payloadType = subst (instantiateSubstitution arguments) declaration.payloadTemplate ∧
    op.responseType = subst (instantiateSubstitution arguments) declaration.responseTemplate := by
  rcases h with ⟨_, h⟩
  cases h
  simp [OperationDeclaration.instantiate]

theorem operation_identity_is_declaration_identity (op : OperationInstance)
    (declaration : OperationDeclaration) (arguments : List Ty)
    (h : op.Instantiates declaration arguments) : op.identity = declaration.identity :=
  (operation_instance_fields_from_one_signature op declaration arguments h).1

end YulangClosure.PaperTypes
