import Yulang.CoreEffectTyping

/-! The historical recursive judgement embeds into the M2 judgement when its
monomorphic signatures factor through resolved keys. The compatibility premise
is explicit because the historical API allowed unrelated signatures sharing a
key. Both directions retain the explicit key-signature compatibility premise. -/
namespace Yulang.Core.EffectTyping
open Inference (Model Comp)
open RowInference (RowAlgebra RowView)
variable {m : Model} {Op Key Scope : Type} {algebra : RowAlgebra Key Scope}

def monoSignature (sig : RecursiveEffects.Signature m Key) : OperationSignature m Key :=
  { locals := 0, input := fun _ => sig.input, output := fun _ => sig.output,
    key := sig.key, extra := sig.extra }

def monomorphicContract (sigs : Op → RecursiveEffects.Signature m Key)
    (keySigs : Key → LocalSignature m)
    (compatible : ∀ op, (monoSignature (sigs op)).toLocalSignature = keySigs (sigs op).key) :
    Contract ⟨Op, Key, Scope, Empty, Empty⟩ m where
  operation := fun op => monoSignature (sigs op)
  keySignature := keySigs
  coherent := compatible
  permission := fun _ _ => true

def legacyBinding : RecursiveEffects.Binding m Op Key Scope → Binding m ⟨Op, Key, Scope, Empty, Empty⟩
  | .mono c => .mono c
  | .poly e Γ => .poly (Effects.embed e) (Γ.map legacyBinding)
  | .signature n instantiate => .signature n instantiate

theorem legacy_preserved {view : RowView m algebra} {sigs : Op → RecursiveEffects.Signature m Key}
    (keySigs : Key → LocalSignature m)
    (compatible : ∀ op, (monoSignature (sigs op)).toLocalSignature = keySigs (sigs op).key) (h : RecursiveEffects.Typing m view sigs Γ e c) :
    Typing m view (monomorphicContract sigs keySigs compatible) (Γ.map legacyBinding) (Effects.embed e) c := by
  induction h using RecursiveEffects.Typing.rec
    (motive_2 := fun b c _ => BindingTyping m view (monomorphicContract sigs keySigs compatible) (legacyBinding b) c)
  all_goals simp only [Effects.embed, legacyBinding, List.map_cons] at *
  case var found _ ih => exact .var (by simp [List.getElem?_map, found]) ih
  case request hp ht hr ih =>
    exact .request (ι := Fin.elim0) ih ht hr
  case handler ha hr ho ht he iha ihr iho =>
    exact .handler rfl iha ihr (fun _ => iho) (fun _ => ht) (fun _ => he)
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
    | apply Typing.field <;> assumption
    | apply Typing.variant <;> assumption
    | apply Typing.request <;> assumption
    | apply Typing.boundary <;> assumption
    | apply BindingTyping.mono; assumption
    | apply BindingTyping.poly <;> assumption
    | apply BindingTyping.signature; assumption

/-- Retraction used only with an explicit legacy-syntax invariant. -/
def legacyUnbinding : Binding m ⟨Op, Key, Scope, Empty, Empty⟩ → RecursiveEffects.Binding m Op Key Scope
  | .mono c => .mono c
  | .poly e Γ => .poly (Effects.decode e) (Γ.map legacyUnbinding)
  | .signature n instantiate => .signature n instantiate

def LegacyTerm (e : Effects.Term Op Key Scope) : Prop := Effects.embed (Effects.decode e) = e

def LegacyBinding : Binding m ⟨Op, Key, Scope, Empty, Empty⟩ → Prop
  | .mono _ | .signature _ _ => True
  | .poly e Γ => LegacyTerm e ∧ ∀ b ∈ Γ, LegacyBinding b

abbrev LegacyEnv (Γ : List (Binding m ⟨Op, Key, Scope, Empty, Empty⟩)) := ∀ b ∈ Γ, LegacyBinding b

private theorem legacy_mono {Γ : List (Binding m ⟨Op, Key, Scope, Empty, Empty⟩)}
    (h : LegacyEnv Γ) (a : Comp m) : LegacyEnv (.mono a :: Γ) := by
  simpa [LegacyEnv, LegacyBinding] using h

private theorem legacy_poly {Γ : List (Binding m ⟨Op, Key, Scope, Empty, Empty⟩)}
    (h : LegacyEnv Γ) {e : Effects.Term Op Key Scope} (he : LegacyTerm e) :
    LegacyEnv (.poly e Γ :: Γ) := by
  simpa [LegacyEnv, LegacyBinding] using And.intro (And.intro he h) h

/-- Reflection applies only when the term and every captured binding are in the
legacy image. It does not decode a multi/partial handler into a dummy literal. -/
theorem legacy_reflected {view : RowView m algebra} {sigs : Op → RecursiveEffects.Signature m Key}
    (keySigs : Key → LocalSignature m)
    (compatible : ∀ op, (monoSignature (sigs op)).toLocalSignature = keySigs (sigs op).key)
    (h : Typing m view (monomorphicContract sigs keySigs compatible) Γ e c) :
    LegacyEnv Γ → LegacyTerm e →
    RecursiveEffects.Typing m view sigs (Γ.map legacyUnbinding) (Effects.decode e) c := by
  induction h using Typing.rec
    (motive_2 := fun b c _ => LegacyBinding b →
      RecursiveEffects.BindingTyping m view sigs (legacyUnbinding b) c)
  case var found _ ih =>
    intro env _
    exact .var (by simp [List.getElem?_map, found]) (ih (env _ (List.mem_of_getElem? found)))
  case handler allowed ha hr ho ht he iha ihr iho =>
    intro env good
    simp only [LegacyTerm, Effects.decode, Effects.embed, Core.Expr.handler.injEq, true_and] at good
    exact .handler (iha env good.1) (by simpa [List.map_cons, legacyUnbinding] using ihr (legacy_mono env _) good.2.1)
      (by simpa [List.map_cons, legacyUnbinding, monomorphicContract, monoSignature] using iho Fin.elim0 (legacy_mono (legacy_mono env _) _) good.2.2)
      (ht Fin.elim0) (he Fin.elim0)
  case multiHandler | partialHandler =>
    intro _ good
    simp [LegacyTerm, Effects.decode, Effects.embed] at good
  case letValue value hv hb ihv ihb =>
    intro env good
    simp only [LegacyTerm, Effects.decode, Effects.embed, Core.Expr.letE.injEq, true_and] at good
    exact .letValue (Effects.decode_value _ value) (ihv env good.1) (by simpa [List.map_cons, legacyUnbinding] using ihb (legacy_poly env good.1) good.2)
  case poly =>
    have good := ‹LegacyBinding (.poly _ _)›
    simp only [LegacyBinding] at good
    rcases good with ⟨term, env⟩
    simp only [legacyUnbinding]
    apply RecursiveEffects.BindingTyping.poly
    · solve_by_elim
    · assumption
  all_goals intros
  all_goals simp_all only [LegacyTerm, Effects.decode, Effects.embed, legacyUnbinding, List.map_cons,
    Core.Expr.lam.injEq, Core.Expr.app.injEq, Core.Expr.letE.injEq,
    Core.Expr.branch.injEq, Core.Expr.pair.injEq, Core.Expr.fst.injEq, Core.Expr.snd.injEq,
    Core.Expr.record.injEq, Core.Expr.field.injEq, Core.Expr.variant.injEq,
    Core.Expr.request.injEq, Core.Expr.boundary.injEq, true_and]
  all_goals first
    | apply RecursiveEffects.Typing.lit; assumption
    | apply RecursiveEffects.Typing.lam <;> solve_by_elim [legacy_mono, True.intro]
    | apply RecursiveEffects.Typing.app <;> solve_by_elim [legacy_mono, True.intro]
    | apply RecursiveEffects.Typing.letComputed <;> solve_by_elim [legacy_mono, True.intro]
    | apply RecursiveEffects.Typing.branch <;> solve_by_elim [legacy_mono, True.intro]
    | apply RecursiveEffects.Typing.pair <;> solve_by_elim [legacy_mono, True.intro]
    | apply RecursiveEffects.Typing.fst <;> solve_by_elim [legacy_mono, True.intro]
    | apply RecursiveEffects.Typing.snd <;> solve_by_elim [legacy_mono, True.intro]
    | apply RecursiveEffects.Typing.emptyRecord; assumption
    | apply RecursiveEffects.Typing.record <;> solve_by_elim [legacy_mono, True.intro]
    | apply RecursiveEffects.Typing.field <;> solve_by_elim [legacy_mono, True.intro]
    | apply RecursiveEffects.Typing.variant <;> solve_by_elim [legacy_mono, True.intro]
    | apply RecursiveEffects.Typing.request <;> solve_by_elim [legacy_mono, True.intro]
    | apply RecursiveEffects.Typing.boundary <;> solve_by_elim [legacy_mono, True.intro]
    | apply RecursiveEffects.BindingTyping.mono; assumption
    | apply RecursiveEffects.BindingTyping.signature; assumption

@[simp] theorem legacyUnbinding_binding (b : RecursiveEffects.Binding m Op Key Scope) :
    legacyUnbinding (legacyBinding b) = b := by
  induction b using RecursiveEffects.Binding.rec
    (motive_2 := fun Γ => (Γ.map legacyBinding).map legacyUnbinding = Γ) <;>
    simp_all [legacyBinding, legacyUnbinding, List.map_map, Function.comp_def]

theorem legacyBinding_good (b : RecursiveEffects.Binding m Op Key Scope) :
    LegacyBinding (legacyBinding b) := by
  induction b using RecursiveEffects.Binding.rec
    (motive_2 := fun Γ => LegacyEnv (Γ.map legacyBinding)) <;>
    simp_all [LegacyBinding, legacyBinding, LegacyEnv, LegacyTerm]

/-- All monomorphic legacy terms, captured environments and result computations,
provided that operation signatures factor through resolved operation keys. -/
theorem legacy_conservative (view : RowView m algebra) (sigs : Op → RecursiveEffects.Signature m Key)
    (keySigs : Key → LocalSignature m)
    (compatible : ∀ op, (monoSignature (sigs op)).toLocalSignature = keySigs (sigs op).key)
    (Γ : List (RecursiveEffects.Binding m Op Key Scope)) (e : RecursiveEffects.Expr Op Key Scope) (c : Comp m) :
    RecursiveEffects.Typing m view sigs Γ e c ↔
      Core.Typing (model m view (monomorphicContract sigs keySigs compatible))
        (Γ.map legacyBinding) (Effects.embed e) c := by
  constructor
  · exact legacy_preserved keySigs compatible
  · intro h
    have env : LegacyEnv (Γ.map legacyBinding) := by
      intro b hb
      obtain ⟨old, _, rfl⟩ := List.mem_map.mp hb
      exact legacyBinding_good old
    simpa [List.map_map, Function.comp_def] using
      legacy_reflected keySigs compatible h env (by simp [LegacyTerm])

/-- The actual historical finite generator, with its scheme/signature relations,
now targets the independent M2 Core judgement on the legacy image. -/
theorem legacy_generate_models_iff_typing (view : RowView m algebra)
    (sigs : Op → RecursiveEffects.Signature m Key) (keySigs : Key → LocalSignature m)
    (compatible : ∀ op, (monoSignature (sigs op)).toLocalSignature = keySigs (sigs op).key)
    (e : RecursiveEffects.Expr Op Key Scope) (sigsTerm : RecursiveEffects.Signatures Op Key α)
    (sΓ : RecursiveEffects.SchemeEnv Key Scope α) (Γ : List (RecursiveEffects.Binding m Op Key Scope))
    (ρ : α → Comp m) (out : Inference.CompTerm α)
    (henv : RecursiveEffects.EnvRel m view sigs ρ sΓ Γ)
    (hsig : RecursiveEffects.SigRel m ρ sigsTerm sigs) :
    (RecursiveEffects.generate sigsTerm sΓ e out).Holds m view ρ ↔
      Core.Typing (model m view (monomorphicContract sigs keySigs compatible))
        (Γ.map legacyBinding) (Effects.embed e) (out.eval m ρ) :=
  (RecursiveEffects.generate_models_iff_typing m view sigs e sigsTerm sΓ Γ ρ out henv hsig).trans
    (legacy_conservative view sigs keySigs compatible Γ e (out.eval m ρ))

end Yulang.Core.EffectTyping
