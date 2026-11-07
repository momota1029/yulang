import Yulang.CorePresenceGenerationExact
import Yulang.CoreInferenceSyntax

/-!
# Independent Core rules and exact generation at the presence model interface

The rules use the extended signature and do not mention generated formulas or
legacy typing in their definition. The Core generator checks the complete
source fragment before decoding, so no out-of-fragment Core expression becomes
the decoder's default unit literal. This is still constraint generation, not a
concrete regular presence inference entry or a claim about solved instances.
-/

namespace Yulang.Core.PresenceGeneration.CoreRules

abbrev Term := Required.Term
abbrev embed := Required.embed
abbrev decode := Required.decode

inductive Binding (m : Model) where
  | mono : Comp m → Binding m
  | poly : Term → List (Binding m) → Binding m
  /-- An independently prescribed signature quantifies value types only.
  Inferred row assignments and the lexical environment are captured by
  `instantiate`; no fresh row assignment is supplied at a call. -/
  | signature (n : Nat) (instantiate : (Fin n → m.Ty) → Comp m) : Binding m

mutual
  inductive Typing (m : Model) : List (Binding m) → Term → Comp m → Prop where
    | var : Γ[n]? = some b → BindingTyping m b c → Typing m Γ (.var n) c
    | lit : Comp.le m (Comp.pure m (m.base b)) c → Typing m Γ (.lit b) c
    | lam : Typing m (.mono a :: Γ) body b →
        Comp.le m (Comp.pure m (Comp.arrow m a b)) c → Typing m Γ (.lam body) c
    | app : Typing m Γ f (Comp.arrow m a b, ef) → Typing m Γ x a →
        Comp.le m (b.1, m.join ef b.2) c → Typing m Γ (.app f x) c
    | letValue : v.isValue = true → Typing m Γ v (Comp.pure m a) →
        Typing m (.poly v Γ :: Γ) body c → Typing m Γ (.letE none v body) c
    | letComputed : Typing m Γ v a →
        Typing m (.mono (Comp.pure m a.1) :: Γ) body b →
        Comp.le m (b.1, m.join a.2 b.2) c → Typing m Γ (.letE none v body) c
    | branch : Typing m Γ condition (m.base .bool, eg) →
        Typing m Γ yes a → Typing m Γ no b →
        Comp.le m (m.union a.1 b.1, m.join eg (m.join a.2 b.2)) c →
        Typing m Γ (.branch condition yes no) c
    | pair : Typing m Γ x a → Typing m Γ y b →
        Comp.le m (m.pair a.1 b.1, m.join a.2 b.2) c → Typing m Γ (.pair x y) c
    | fst : Typing m Γ x (m.pair a b, er) →
        Comp.le m (a, er) c → Typing m Γ (.fst x) c
    | snd : Typing m Γ x (m.pair a b, er) →
        Comp.le m (b, er) c → Typing m Γ (.snd x) c
    | emptyRecord : Comp.le m (Comp.pure m m.exactEmpty) c →
        Typing m Γ .emptyRecord c
    | record : Typing m Γ x a → Typing m Γ rest b → m.subTy b.1 m.emptyRecord →
        Comp.le m (m.record l a.1 b.1, m.join a.2 b.2) c →
        Typing m Γ (.record l x rest) c
    | recordDefault : Typing m Γ source a → Typing m Γ fallback b →
        m.subTy a.1 m.emptyRecord →
        Comp.le m (m.recordDefault l a.1 b.1, m.join a.2 b.2) c →
        Typing m Γ (.recordDefault l source fallback) c
    | field : Typing m Γ x (m.required l a, er) →
        Comp.le m (a, er) c → Typing m Γ (.field l x) c
    | variant : Typing m Γ x a →
        Comp.le m (m.variant l a.1, a.2) c → Typing m Γ (.variant l x) c

  inductive BindingTyping (m : Model) : Binding m → Comp m → Prop where
    | mono : Comp.le m a c → BindingTyping m (.mono a) c
    | poly : Typing m Γ v (Comp.pure m c.1) → m.subRow m.empty c.2 →
        BindingTyping m (.poly v Γ) c
    | signature {n : Nat} {instantiate : (Fin n → m.Ty) → Comp m} {ι : Fin n → m.Ty} :
        Comp.le m (instantiate ι) c →
        BindingTyping m (.signature n instantiate) c
end


def model (m : Model) : TypingModel Signature.empty :=
  ⟨List (Binding m), Comp m, Typing m⟩

def binding : PresenceGeneration.Binding m → Binding m
  | .mono a => .mono a
  | .poly e Γ => .poly (embed e) (Γ.map binding)
  | .signature n instantiate => .signature n instantiate

def unbinding : Binding m → PresenceGeneration.Binding m
  | .mono a => .mono a
  | .poly e Γ => .poly (decode e) (Γ.map unbinding)
  | .signature n instantiate => .signature n instantiate

@[simp] theorem unbinding_binding (b : PresenceGeneration.Binding m) : unbinding (binding b) = b := by
  induction b using PresenceGeneration.Binding.rec
    (motive_2 := fun Γ => (Γ.map binding).map unbinding = Γ) <;>
    simp_all [binding, unbinding, List.map_map, Function.comp_def]

theorem preserved (h : PresenceGeneration.Typing m Γ e c) :
    Typing m (Γ.map binding) (embed e) c := by
  induction h using PresenceGeneration.Typing.rec
    (motive_2 := fun b c _ => BindingTyping m (binding b) c)
  all_goals simp only [embed, Required.embed, binding, List.map_cons] at *
  case var found _ ih => exact .var (by simp [List.getElem?_map, found]) ih
  all_goals first
    | apply Typing.letValue <;> first | simpa using ‹_› | assumption
    | apply Typing.lit; assumption
    | apply Typing.lam <;> assumption
    | apply Typing.app <;> assumption
    | apply Typing.letComputed <;> assumption
    | apply Typing.branch <;> assumption
    | apply Typing.pair <;> assumption
    | apply Typing.fst <;> assumption
    | apply Typing.snd <;> assumption
    | apply Typing.emptyRecord; assumption
    | apply Typing.record <;> assumption
    | apply Typing.recordDefault <;> assumption
    | apply Typing.field <;> assumption
    | apply Typing.variant <;> assumption
    | apply BindingTyping.mono; assumption
    | apply BindingTyping.poly <;> assumption
    | apply BindingTyping.signature; assumption

theorem reflected (h : Typing m Γ e c) :
    PresenceGeneration.Typing m (Γ.map unbinding) (decode e) c := by
  induction h using Typing.rec
    (motive_2 := fun b c _ => PresenceGeneration.BindingTyping m (unbinding b) c)
  all_goals simp only [decode, Required.decode, unbinding, List.map_cons] at *
  case var found _ ih => exact .var (by simp [List.getElem?_map, found]) ih
  case letValue value _ _ ihv ihb => exact .letValue (Required.decode_value _ value) ihv ihb
  all_goals first
    | apply PresenceGeneration.Typing.lit; assumption
    | apply PresenceGeneration.Typing.lam <;> assumption
    | apply PresenceGeneration.Typing.app <;> assumption
    | apply PresenceGeneration.Typing.letComputed <;> assumption
    | apply PresenceGeneration.Typing.branch <;> assumption
    | apply PresenceGeneration.Typing.pair <;> assumption
    | apply PresenceGeneration.Typing.fst <;> assumption
    | apply PresenceGeneration.Typing.snd <;> assumption
    | apply PresenceGeneration.Typing.emptyRecord; assumption
    | apply PresenceGeneration.Typing.record <;> assumption
    | apply PresenceGeneration.Typing.recordDefault <;> assumption
    | apply PresenceGeneration.Typing.field <;> assumption
    | apply PresenceGeneration.Typing.variant <;> assumption
    | apply PresenceGeneration.BindingTyping.mono; assumption
    | apply PresenceGeneration.BindingTyping.poly <;> assumption
    | apply PresenceGeneration.BindingTyping.signature; assumption

/-- All models, all environments (including captured schemes), terms and
result computations. No inference success or syntactic support premise. -/
theorem conservative (m : Model) (Γ : List (PresenceGeneration.Binding m))
    (e : Inference.Expr) (c : Comp m) :
    PresenceGeneration.Typing m Γ e c ↔ Core.Typing (model m) (Γ.map binding) (embed e) c := by
  constructor
  · exact preserved
  · intro h
    simpa [List.map_map, Function.comp_def] using reflected h



/-- Every derivable expression lies in the intended syntactic fragment. The
claim includes invalid source expressions as inputs to the gate; it does not
assume a successful solver. -/
theorem typing_syntax (typed : Typing m Γ e c) : InferenceSyntax.supported e = true := by
  induction typed using Typing.rec
    (motive_2 := fun _ _ _ => True)
  all_goals first
    | trivial
    | simp_all [InferenceSyntax.supported]

/-- A first-order formula for every Core expression. Out-of-fragment syntax
has no rule in this model and generates the false formula; this is not the
public solver's `rejected`/`unsupported` classification. -/
def generateCore (Γ : SchemeEnv α) (e : Term) (out : CompTerm α) : Formula α :=
  if InferenceSyntax.supported e then generate Γ (decode e) out else .bot

@[simp] theorem generateCore_embed (Γ : SchemeEnv α) (e : Inference.Expr)
    (out : CompTerm α) : generateCore Γ (embed e) out = generate Γ e out := by
  simp [generateCore, embed, decode]

/-- Every extended model, every corresponding captured environment, every
Core expression, every value/row valuation, and every symbolic output. The
formula and the independent Core constructor judgment agree. -/
theorem generateCore_exact (m : Model) (e : Term) (sΓ : SchemeEnv α)
    (Γ : List (PresenceGeneration.Binding m)) (ρ : α → Comp m) (out : CompTerm α)
    (henv : EnvRel m ρ sΓ Γ) :
    (generateCore sΓ e out).Holds m ρ ↔
      Core.Typing (model m) (Γ.map binding) e (out.eval m ρ) := by
  change _ ↔ Typing m (Γ.map binding) e (out.eval m ρ)
  constructor
  · intro held
    cases supported : InferenceSyntax.supported e with
    | false => simp [generateCore, supported, Formula.Holds] at held
    | true =>
        have source : (generate sΓ (decode e) out).Holds m ρ := by
          simpa only [generateCore, supported, ↓reduceIte] using held
        have typed := preserved ((generate_models_iff_typing m (decode e) sΓ Γ ρ out henv).mp source)
        simpa only [embed, decode, InferenceSyntax.embed_decode e supported] using typed
  · intro typed
    have supported := typing_syntax typed
    have source : PresenceGeneration.Typing m Γ (decode e) (out.eval m ρ) := by
      simpa [List.map_map, Function.comp_def] using reflected typed
    have held := (generate_models_iff_typing m (decode e) sΓ Γ ρ out henv).mpr source
    simpa only [generateCore, supported, ↓reduceIte] using held

def principalCore (Γ : SchemeEnv α) (e : Term) : Scheme α :=
  generateCore Γ.lift e (CompTerm.var none)

/-- All result computations are quantified; no solved scheme or input typing
is a hypothesis. The conclusion concerns a constraint scheme. -/
theorem principalCore_exact (m : Model) (e : Term) (sΓ : SchemeEnv α)
    (Γ : List (PresenceGeneration.Binding m)) (ρ : α → Comp m)
    (henv : EnvRel m ρ sΓ Γ) (c : Comp m) :
    (principalCore sΓ e).Holds m (extend ρ c) ↔
      Core.Typing (model m) (Γ.map binding) e c := by
  simpa only [principalCore, CompTerm.eval_var, extend_none]
    using generateCore_exact m e sΓ.lift Γ (extend ρ c) (CompTerm.var none) (henv.lift c)

end Yulang.Core.PresenceGeneration.CoreRules
