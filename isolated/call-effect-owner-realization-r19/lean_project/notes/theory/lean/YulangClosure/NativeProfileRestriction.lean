import Init

/-!
# Dependent-record equations for native profile hereditary restriction

The authoritative native `L`, `DeclContribution`, and `NP` constructions are
paper definitions, not datatypes in the current Lean development. This module
does NOT replace them with a smaller syntax. It checks the dependent-record
algebra used by the original-constructor induction in
`notes/theory/2026-10-26-native-profile-hereditary-restriction.md`.

`W` is the entire original joint tuple, not a world identifier or an erased
endpoint. `P w` is an entire original dependent packet, including its genuine
license evidence. Restriction functions are the original independent leaf
actions; none of the theorems assumes naturality of a generated native profile.
There is no `SourceProblem.InferenceSoundness` instance in this module.
-/
namespace YulangClosure.NativeProfileRestriction

set_option autoImplicit false

universe u v w u' v' w' u'' v''

/-- Retain the whole joint tuple and the packet depending on that exact tuple. -/
abbrev Packet {W : Type u} (P : W → Type v) := Sigma P

/-- The dependent record action at one independently lawful extension. -/
def restrictPacket {W : Type u} {W' : Type u'}
    {P : W → Type v} {P' : W' → Type v'}
    (r : W → W') (a : ∀ w, P w → P' (r w)) : Packet P → Packet P'
  | ⟨w, p⟩ => ⟨r w, a w p⟩

theorem restrictPacket_mk {W : Type u} {W' : Type u'}
    {P : W → Type v} {P' : W' → Type v'}
    (r : W → W') (a : ∀ w, P w → P' (r w)) (w : W) (p : P w) :
    restrictPacket r a ⟨w, p⟩ = ⟨r w, a w p⟩ := rfl

theorem restrictPacket_tuple {W : Type u} {W' : Type u'}
    {P : W → Type v} {P' : W' → Type v'}
    (r : W → W') (a : ∀ w, P w → P' (r w)) (p : Packet P) :
    (restrictPacket r a p).1 = r p.1 := rfl

theorem restrictPacket_identity {W : Type u} {P : W → Type v}
    (p : Packet P) : restrictPacket id (fun _ x => x) p = p := rfl

/-- Actual insertion/use routes compose on one whole tuple and its evidence. -/
theorem restrictPacket_comp {W : Type u} {W' : Type u'} {W'' : Type u''}
    {P : W → Type v} {P' : W' → Type v'} {P'' : W'' → Type v''}
    (r : W → W') (a : ∀ w, P w → P' (r w))
    (s : W' → W'') (b : ∀ w, P' w → P'' (s w)) (p : Packet P) :
    restrictPacket s b (restrictPacket r a p) =
      restrictPacket (fun w => s (r w)) (fun w x => b (r w) (a w x)) p := rfl

/-- An occurrence/operand/root tag retains the complete source packet. -/
def tagged {Tag : Type u'} {W : Type u} {P : W → Type v}
    (t : Tag) (p : Packet P) : Tag × Packet P := (t, p)

theorem tagged_restriction {Tag : Type w} {Tag' : Type w'}
    {W : Type u} {W' : Type u'} {P : W → Type v} {P' : W' → Type v'}
    (tagMap : Tag → Tag') (r : W → W') (a : ∀ w, P w → P' (r w))
    (t : Tag) (p : Packet P) :
    Prod.map tagMap (restrictPacket r a) (tagged t p) =
      tagged (tagMap t) (restrictPacket r a p) := rfl

theorem tagged_projection {Tag : Type w} {W : Type u} {P : W → Type v}
    (t : Tag) (p : Packet P) : (tagged t p).2 = p := rfl

/-- Pair uses one original tuple; it cannot combine two unrelated worlds. -/
def sharedPair {W : Type u} {P : W → Type v} {Q : W → Type w}
    (x : W) (p : P x) (q : Q x) : Packet (fun x => P x × Q x) :=
  ⟨x, p, q⟩

theorem sharedPair_restriction {W : Type u} {W' : Type u'}
    {P : W → Type v} {P' : W' → Type v'}
    {Q : W → Type w} {Q' : W' → Type w'}
    (r : W → W') (a : ∀ x, P x → P' (r x))
    (b : ∀ x, Q x → Q' (r x)) (x : W) (p : P x) (q : Q x) :
    restrictPacket r (fun x pq => (a x pq.1, b x pq.2)) (sharedPair x p q) =
      sharedPair (r x) (a x p) (b x q) := rfl

/-- Arbitrarily many fields remain dependent on the same tuple. -/
def sharedFields {W : Type u} {K : Type w} {P : W → K → Type v}
    (x : W) (p : ∀ k, P x k) : Packet (fun x => ∀ k, P x k) := ⟨x, p⟩

theorem sharedFields_restriction {W : Type u} {W' : Type u'} {K : Type w}
    {P : W → K → Type v} {P' : W' → K → Type v'}
    (r : W → W') (a : ∀ x k, P x k → P' (r x) k)
    (x : W) (p : ∀ k, P x k) :
    restrictPacket r (fun x ps k => a x k (ps k)) (sharedFields x p) =
      sharedFields (r x) (fun k => a x k (p k)) := rfl

/-- The sum is the actual alternative tag, not a union of erased endpoints. -/
def restrictAlternative {P : Type u} {Q : Type v} {P' : Type u'} {Q' : Type v'}
    (a : P → P') (b : Q → Q') : Sum P Q → Sum P' Q'
  | .inl p => .inl (a p)
  | .inr q => .inr (b q)

theorem restrictAlternative_left {P : Type u} {Q : Type v}
    {P' : Type u'} {Q' : Type v'} (a : P → P') (b : Q → Q') (p : P) :
    restrictAlternative a b (.inl p) = .inl (a p) := rfl

theorem restrictAlternative_right {P : Type u} {Q : Type v}
    {P' : Type u'} {Q' : Type v'} (a : P → P') (b : Q → Q') (q : Q) :
    restrictAlternative a b (.inr q) = .inr (b q) := rfl

/-- Static local policy is appended to an already licensed original packet.
`D` may be the actual FullProtection/NoConcreteRemovalGrant policy pair.
It is not a predicate asserting live authority or permission at an event. -/
def appendLocal {W : Type u} {P : W → Type v} {D : Type w}
    (defaultPolicy : D) (p : Packet P) : Packet (fun x => P x × D) :=
  ⟨p.1, p.2, defaultPolicy⟩

theorem appendLocal_restriction {W : Type u} {W' : Type u'}
    {P : W → Type v} {P' : W' → Type v'} {D : Type w}
    (r : W → W') (a : ∀ x, P x → P' (r x))
    (defaultPolicy : D) (p : Packet P) :
    restrictPacket r (fun x pd => (a x pd.1, pd.2)) (appendLocal defaultPolicy p) =
      appendLocal defaultPolicy (restrictPacket r a p) := rfl

theorem appendLocal_original {W : Type u} {P : W → Type v} {D : Type w}
    (defaultPolicy : D) (p : Packet P) :
    (⟨(appendLocal defaultPolicy p).1, (appendLocal defaultPolicy p).2.1⟩ : Packet P) =
      p := rfl

theorem appendLocal_policy {W : Type u} {P : W → Type v} {D : Type w}
    (defaultPolicy : D) (p : Packet P) :
    (appendLocal defaultPolicy p).2.2 = defaultPolicy := rfl

/-- Assembly over the actual inherited/local partition; the two fibers retain
their original packet types and their original license witnesses. -/
def assembleFields {I : Type u} {J : Type v}
    {P : I → Type w} {Q : J → Type w}
    (inherited : ∀ i, P i) (localFields : ∀ j, Q j) :
    (k : Sum I J) → Sum.elim P Q k
  | .inl i => inherited i
  | .inr j => localFields j

theorem assembleFields_inherited {I : Type u} {J : Type v}
    {P : I → Type w} {Q : J → Type w}
    (inherited : ∀ i, P i) (localFields : ∀ j, Q j) (i : I) :
    assembleFields inherited localFields (.inl i) = inherited i := rfl

theorem assembleFields_local {I : Type u} {J : Type v}
    {P : I → Type w} {Q : J → Type w}
    (inherited : ∀ i, P i) (localFields : ∀ j, Q j) (j : J) :
    assembleFields inherited localFields (.inr j) = localFields j := rfl

/-- Pointwise naturality over an arbitrary licensed field index. Nothing
requires this index to be inhabited, finite, or quotiented by its endpoint. -/
theorem assembleFields_restriction {I : Type u} {J : Type v}
    {P : I → Type w} {Q : J → Type w}
    {P' : I → Type w'} {Q' : J → Type w'}
    (a : ∀ i, P i → P' i) (b : ∀ j, Q j → Q' j)
    (inherited : ∀ i, P i) (localFields : ∀ j, Q j) (k : Sum I J) :
    assembleFields (fun i => a i (inherited i)) (fun j => b j (localFields j)) k =
      (match k with
       | .inl i => a i (assembleFields inherited localFields (.inl i))
       | .inr j => b j (assembleFields inherited localFields (.inr j))) := by
  cases k <;> rfl

/-- Bind/hiding retains one dependent middle witness, then all of its fields.
For hiding the inner packet includes the original admission certificate. -/
def dependentBind {W : Type u} {B : W → Type v} {P : (x : W) → B x → Type w}
    (x : W) (b : B x) (p : P x b) : Packet (fun x => Sigma (P x)) := ⟨x, b, p⟩

theorem dependentBind_restriction {W : Type u} {W' : Type u'}
    {B : W → Type v} {B' : W' → Type v'}
    {P : (x : W) → B x → Type w} {P' : (x : W') → B' x → Type w'}
    (r : W → W') (middle : ∀ x, B x → B' (r x))
    (a : ∀ x b, P x b → P' (r x) (middle x b))
    (x : W) (b : B x) (p : P x b) :
    restrictPacket r
      (fun x bp => ⟨middle x bp.1, a x bp.1 bp.2⟩)
      (dependentBind x b p) =
    dependentBind (r x) (middle x b) (a x b p) := rfl

theorem dependentBind_middle {W : Type u} {B : W → Type v}
    {P : (x : W) → B x → Type w} (x : W) (b : B x) (p : P x b) :
    (dependentBind x b p).2.1 = b := rfl

/-- A suspended suffix remains a function on the original dependent inlet.
This is restriction by actual precomposition, not production of an inlet. -/
def restrictSuffix {A : Type u} {A' : Type u'} {P : A → Type v}
    (r : A' → A) (f : ∀ a, P a) : ∀ a', P (r a') := fun a' => f (r a')

theorem restrictSuffix_comp {A : Type u} {A' : Type u'} {A'' : Type u''}
    {P : A → Type v} (r : A' → A) (s : A'' → A') (f : ∀ a, P a) :
    restrictSuffix s (restrictSuffix r f) =
      restrictSuffix (fun a'' => r (s a'')) f := rfl

theorem restrictSuffix_apply {A : Type u} {A' : Type u'} {P : A → Type v}
    (r : A' → A) (f : ∀ a, P a) (a' : A') :
    restrictSuffix r f a' = f (r a') := rfl

/-- The record equation used by the paper's actual ValueBind profile case:
old fields and a genuine new returned certificate share their current tuple;
only the genuinely new local policy is appended. This checks that record
equation, not an undeclared Lean source-typing or ValueBind judgment. -/
theorem valueBind_profile_restriction {W : Type u} {W' : Type u'}
    {Old : W → Type v} {Old' : W' → Type v'}
    {New : W → Type w} {New' : W' → Type w'} {D : Type u''}
    (r : W → W') (oldAct : ∀ x, Old x → Old' (r x))
    (newAct : ∀ x, New x → New' (r x)) (defaultPolicy : D)
    (x : W) (old : Old x) (new : New x) :
    restrictPacket r
      (fun x p => ((oldAct x p.1.1, newAct x p.1.2), p.2))
      (appendLocal defaultPolicy (sharedPair x old new)) =
    appendLocal defaultPolicy (sharedPair (r x) (oldAct x old) (newAct x new)) := rfl

end YulangClosure.NativeProfileRestriction
