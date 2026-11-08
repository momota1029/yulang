import Yulang.CommonEffectMixedSource
import Yulang.CommonEffectMixedFormula

/-! Actual finite structural generation for the unchanged recursive effect
source, now using one mixed type/row-local table throughout the recursion. All stored schemes, declarations and masks are finite syntax.
This layer does not solve the generated universal constraints. -/
namespace Yulang.CommonEffectMixedGeneration
open Core.PresenceGeneration (Comp CompTerm TyTerm RowTerm extend extend_none extend_some extend_comp_some)
open CommonEffectRequestGeneration (Computation RowExpr)
open CommonEffectMixedDeclarations (Declarations Declaration SemanticSignature)
open CommonEffectKindedFormula
open CommonEffectPresence (fresh₀ fresh₁ fresh₀₃ fresh₁₃ fresh₂₃ lift₂ lift₃)
open CommonEffectMixedDeclarations (renameAll interpretAll)
open CommonEffectMixedSource

variable {scopes : Nat}

def decl₂ (declarations : Declarations α) : Declarations (Option (Option α)) :=
  renameAll some (renameAll some declarations)

def decl₃ (declarations : Declarations α) : Declarations (Option (Option (Option α))) :=
  renameAll some (renameAll some (renameAll some declarations))

def declarationKeys (declarations : Declarations α) (operations : Fin count → Nat) : List Nat :=
  (List.finRange count).filterMap (fun i => (declarations[operations i]?).map (·.key))

theorem declarationKeys_interpret (declarations : Declarations α) (operations : Fin count → Nat)
    (assignment : α → Computation) :
    handlerKeys (interpretAll assignment declarations) operations = declarationKeys declarations operations := by
  unfold handlerKeys declarationKeys
  congr 1
  funext i
  rw [CommonEffectMixedDeclarations.lookup_interpretAll]
  cases declarations[operations i]? <;> rfl

def declarationPartialKeys (declarations : Declarations α) (arms : Fin count → CommonEffectArmCoverage.Arm) : List Nat :=
  (List.finRange count).filterMap (fun i =>
    if (arms i).total then (declarations[(arms i).operation]?).map (·.key) else none)

theorem declarationPartialKeys_interpret (declarations : Declarations α) (arms : Fin count → CommonEffectArmCoverage.Arm)
    (assignment : α → Computation) :
    partialKeys (interpretAll assignment declarations) arms = declarationPartialKeys declarations arms := by
  unfold partialKeys declarationPartialKeys
  congr 1
  funext i
  cases total : (arms i).total <;> simp only [Bool.false_eq_true, ↓reduceIte]
  rw [CommonEffectMixedDeclarations.lookup_interpretAll]
  cases declarations[(arms i).operation]? <;> rfl

def boundaryRow (boundary : Boundary scopes) (row : RowExpr scopes α) : RowExpr scopes α :=
  match boundary with
  | .protect scope permission => .protect scope permission row
  | .release scope permission => .release scope permission row

@[simp] theorem boundaryRow_eval (boundary : Boundary scopes) (row : RowExpr scopes α) (assignment : α → Computation) :
    (boundaryRow boundary row).eval assignment = boundary.eval (row.eval assignment) := by
  cases boundary <;> rfl

def handlerChecks (key : Nat) (input returned out : CompTerm α)
    (generated : Formula scopes (Option α)) : Formula scopes (Option α) :=
  .and generated
    (.and (.tyLe (.union (returned.ty.rename some) (.var none)) (out.ty.rename some))
      (.rowLe (.union (.residual [key] (RowExpr.fromPresence (input.row.rename some)))
        (.union (RowExpr.fromPresence (returned.row.rename some)) (.var none)))
        (RowExpr.fromPresence (out.row.rename some))))

theorem handlerChecks_holds (key : Nat) (input returned out : CompTerm α)
    (generated : Formula scopes (Option α)) (assignment : α → Computation) (operated : Computation) :
    (handlerChecks key input returned out generated).Holds (extend assignment operated) ↔
      generated.Holds (extend assignment operated) ∧
      Common.Subtype (.union (returned.eval Common.model assignment).1 operated.1) (out.eval Common.model assignment).1 ∧
      Common.rowLe (Common.rowJoin (CommonSignedRows.commonResidual [key] (input.eval Common.model assignment).2)
        (Common.rowJoin (returned.eval Common.model assignment).2 operated.2)) (out.eval Common.model assignment).2 := by
  simp only [handlerChecks, Formula.Holds, Formula.holds_tyLe, Formula.holds_rowLe,
    Core.PresenceGeneration.TyTerm.eval, RowExpr.eval, RowExpr.eval_fromPresence,
    Core.PresenceGeneration.TyTerm.eval_rename,
    Core.PresenceGeneration.RowTerm.eval_rename, extend_none, extend_comp_some]
  rfl

theorem andAll_fin (formulas : Fin count → Formula scopes α) (assignment : α → Computation) :
    (CommonEffectKindedFormula.andAll ((List.finRange count).map formulas)).Holds assignment ↔
      ∀ i, (formulas i).Holds assignment := by
  simp

def generate (declarations : Declarations α) (Γ : SchemeEnv scopes α) : Expr scopes → CompTerm α → Formula scopes α
  | .var n, out => Scheme.lookup Γ n out
  | .lit b, out => Formula.compLe (CompTerm.pure (.base b)) out
  | .lam body, out =>
      .existsSlot (.existsSlot (
        .and (generate (decl₂ declarations) (Scheme.mono fresh₀ :: env₂ Γ) body fresh₁)
          (Formula.compLe (CompTerm.pure (CompTerm.arrow fresh₀ fresh₁)) (lift₂ out))))
  | .app f x, out =>
      .existsSlot (.existsSlot (.existsSlot (
        .and (generate (decl₃ declarations) (env₃ Γ) f ⟨CompTerm.arrow fresh₀₃ fresh₁₃, fresh₂₃.row⟩)
          (.and (generate (decl₃ declarations) (env₃ Γ) x fresh₀₃)
            (Formula.compLe ⟨fresh₁₃.ty, .join fresh₂₃.row fresh₁₃.row⟩ (lift₃ out))))))
  | .letE v body, out =>
      let monomorphic := .existsSlot (.existsSlot (
        .and (generate (decl₂ declarations) (env₂ Γ) v fresh₀)
          (.and (generate (decl₂ declarations) (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ Γ) body fresh₁)
            (Formula.compLe ⟨fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ out)))))
      if v.isValue then
        let scheme : Scheme scopes α :=
          .and (generate (renameAll some declarations) Γ.lift v (CompTerm.pure (.var none)))
            (.rowLe .empty (.var none))
        .or (.and (.existsSlot (generate (renameAll some declarations) Γ.lift v (CompTerm.pure (.var none))))
          (generate declarations (scheme :: Γ) body out)) monomorphic
      else
        monomorphic
  | .branch g y n, out =>
      .existsSlot (.existsSlot (.existsSlot (
        .and (generate (decl₃ declarations) (env₃ Γ) g ⟨.base .bool, fresh₀₃.row⟩)
          (.and (generate (decl₃ declarations) (env₃ Γ) y fresh₁₃)
            (.and (generate (decl₃ declarations) (env₃ Γ) n fresh₂₃)
              (Formula.compLe ⟨.union fresh₁₃.ty fresh₂₃.ty,
                .join fresh₀₃.row (.join fresh₁₃.row fresh₂₃.row)⟩ (lift₃ out)))))))
  | .pair x y, out =>
      .existsSlot (.existsSlot (
        .and (generate (decl₂ declarations) (env₂ Γ) x fresh₀)
          (.and (generate (decl₂ declarations) (env₂ Γ) y fresh₁)
            (Formula.compLe ⟨.pair fresh₀.ty fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ out)))))
  | .fst x, out =>
      .existsSlot (.existsSlot (
        .and (generate (decl₂ declarations) (env₂ Γ) x ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩)
          (Formula.compLe ⟨fresh₀.ty, fresh₀.row⟩ (lift₂ out))))
  | .snd x, out =>
      .existsSlot (.existsSlot (
        .and (generate (decl₂ declarations) (env₂ Γ) x ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩)
          (Formula.compLe ⟨fresh₁.ty, fresh₀.row⟩ (lift₂ out))))
  | .emptyRecord, out => Formula.compLe (CompTerm.pure .exactEmpty) out
  | .record l x rest, out =>
      .existsSlot (.existsSlot (
        .and (generate (decl₂ declarations) (env₂ Γ) x fresh₀)
          (.and (generate (decl₂ declarations) (env₂ Γ) rest fresh₁)
            (.and (.tyLe fresh₁.ty .emptyRecord)
              (Formula.compLe ⟨.record l fresh₀.ty fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ out))))))
  | .recordDefault l source fallback, out =>
      .existsSlot (.existsSlot (
        .and (generate (decl₂ declarations) (env₂ Γ) source fresh₀)
          (.and (generate (decl₂ declarations) (env₂ Γ) fallback fresh₁)
            (.and (.tyLe fresh₀.ty .emptyRecord)
              (Formula.compLe ⟨.recordDefault l fresh₀.ty fresh₁.ty,
                .join fresh₀.row fresh₁.row⟩ (lift₂ out))))))
  | .field l x, out =>
      .existsSlot (
        .and (generate (renameAll some declarations) Γ.lift x ⟨.required l (.var none), .var none⟩)
          (Formula.compLe (CompTerm.var none) (out.rename some)))
  | .variant l x, out =>
      .existsSlot (
        .and (generate (renameAll some declarations) Γ.lift x (CompTerm.var none))
          (Formula.compLe ⟨.variant l (.var none), .var none⟩ (out.rename some)))
  | .request operation payload, out =>
      match declarations[operation]? with
      | none => .core .bot
      | some declaration =>
          .existsLocals declaration.types declaration.rows (.existsSlot (.and
            (generate (renameAll some (renameAll Sum.inl declarations)) (Γ.rename Sum.inl).lift payload
              ⟨declaration.input.rename some, .var none⟩)
            (.and (.tyLe (declaration.output.rename some) ((out.rename Sum.inl).ty.rename some))
              (.rowLe (.union (.var none) (.union (.head declaration.key) (RowExpr.heads declaration.extra)))
                (RowExpr.fromPresence ((out.rename Sum.inl).row.rename some))))))
  | .boundary boundary body, out =>
      .existsSlot (.and (generate (renameAll some declarations) Γ.lift body (CompTerm.var none))
        (.and (.tyLe (.var none) (out.ty.rename some))
          (.rowLe (boundaryRow boundary (.var none)) (RowExpr.fromPresence (out.row.rename some)))))
  | .handler permission operation action onReturn onOperation, out =>
      match declarations[operation]? with
      | none => .core .bot
      | some declaration =>
          if permission.allows declaration.key then
            let armInput := fresh₀.rename (β := Option (Option α) ⊕ Names declaration.types declaration.rows) Sum.inl
            let armReturned := fresh₁.rename (β := Option (Option α) ⊕ Names declaration.types declaration.rows) Sum.inl
            let armOut := (lift₂ out).rename (β := Option (Option α) ⊕ Names declaration.types declaration.rows) Sum.inl
            let payload := declaration.input.rename (Sum.map (fun name => some (some name)) id)
            let response := declaration.output.rename (Sum.map (fun name => some (some name)) id)
            let armEnv : SchemeEnv scopes (Option (Option α) ⊕ Names declaration.types declaration.rows) := Scheme.mono (CompTerm.pure payload) ::
              Scheme.mono (CompTerm.pure (CompTerm.arrow (CompTerm.pure response) armInput)) :: (env₂ Γ).rename Sum.inl
            let arm := handlerChecks declaration.key armInput armReturned armOut
              (generate (renameAll some (renameAll Sum.inl (decl₂ declarations))) armEnv.lift
                onOperation (CompTerm.var none))
            .existsSlot (.existsSlot (.and
              (generate (decl₂ declarations) (env₂ Γ) action fresh₀)
              (.and (generate (decl₂ declarations) (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ Γ) onReturn fresh₁)
                (.forallLocals declaration.types declaration.rows (.existsSlot arm)))))
          else .core .bot
  | .multiHandler permission operations action onReturn bodies, out =>
      .existsSlot (.existsSlot (.and
        (generate (decl₂ declarations) (env₂ Γ) action fresh₀)
        (.and (generate (decl₂ declarations) (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ Γ) onReturn fresh₁)
          (.and (.tyLe fresh₁.ty (lift₂ out).ty)
            (.and (.rowLe (.union (.residual (declarationKeys declarations operations) (RowExpr.fromPresence fresh₀.row))
              (RowExpr.fromPresence fresh₁.row)) (RowExpr.fromPresence (lift₂ out).row))
              (CommonEffectKindedFormula.andAll ((List.finRange _).map (fun i =>
                match declarations[operations i]? with
                | none => .core .bot
                | some declaration =>
                  if permission.allows declaration.key then
                    let armInput := fresh₀.rename (β := Option (Option α) ⊕ Names declaration.types declaration.rows) Sum.inl
                    let armOut := (lift₂ out).rename (β := Option (Option α) ⊕ Names declaration.types declaration.rows) Sum.inl
                    let payload := declaration.input.rename (Sum.map (fun name => some (some name)) id)
                    let response := declaration.output.rename (Sum.map (fun name => some (some name)) id)
                    let armEnv : SchemeEnv scopes (Option (Option α) ⊕ Names declaration.types declaration.rows) :=
                      Scheme.mono (CompTerm.pure payload) ::
                      Scheme.mono (CompTerm.pure (CompTerm.arrow (CompTerm.pure response) armInput)) :: (env₂ Γ).rename Sum.inl
                    .forallLocals declaration.types declaration.rows (.existsSlot (.and
                      (generate (renameAll some (renameAll Sum.inl (decl₂ declarations))) armEnv.lift
                        (bodies i) (CompTerm.var none))
                      (Formula.compLe (CompTerm.var none) (armOut.rename some))))
                  else .core .bot))))))))
  | .partialHandler permission operations action onReturn bodies, out =>
      .existsSlot (.existsSlot (.and
        (generate (decl₂ declarations) (env₂ Γ) action fresh₀)
        (.and (generate (decl₂ declarations) (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ Γ) onReturn fresh₁)
          (.and (.tyLe fresh₁.ty (lift₂ out).ty)
            (.and (.rowLe (.union (.residual (declarationPartialKeys declarations operations) (RowExpr.fromPresence fresh₀.row))
              (RowExpr.fromPresence fresh₁.row)) (RowExpr.fromPresence (lift₂ out).row))
              (CommonEffectKindedFormula.andAll ((List.finRange _).map (fun i =>
                match declarations[(operations i).operation]? with
                | none => .core .bot
                | some declaration =>
                  if permission.allows declaration.key then
                    let armInput := fresh₀.rename (β := Option (Option α) ⊕ Names declaration.types declaration.rows) Sum.inl
                    let armOut := (lift₂ out).rename (β := Option (Option α) ⊕ Names declaration.types declaration.rows) Sum.inl
                    let payload := declaration.input.rename (Sum.map (fun name => some (some name)) id)
                    let response := declaration.output.rename (Sum.map (fun name => some (some name)) id)
                    let armEnv : SchemeEnv scopes (Option (Option α) ⊕ Names declaration.types declaration.rows) :=
                      Scheme.mono (CompTerm.pure payload) ::
                      Scheme.mono (CompTerm.pure (CompTerm.arrow (CompTerm.pure response) armInput)) :: (env₂ Γ).rename Sum.inl
                    .forallLocals declaration.types declaration.rows (.existsSlot (.and
                      (generate (renameAll some (renameAll Sum.inl (decl₂ declarations))) armEnv.lift
                        (bodies i) (CompTerm.var none))
                      (Formula.compLe (CompTerm.var none) (armOut.rename some))))
                  else .core .bot))))))))

def SchemeLookup (assignment : α → Computation) (environment : SchemeEnv scopes α) (index : Nat) (out : Computation) : Prop :=
  match environment[index]? with
  | none => False
  | some scheme => scheme.Holds (extend assignment out)

def EnvRel (signatures : List SemanticSignature) (assignment : α → Computation) (environment : SchemeEnv scopes α)
    (bindings : List (Binding scopes)) : Prop :=
  ∀ index out, SchemeLookup assignment environment index out ↔
    BindingLookup signatures bindings index out

@[simp] theorem lookup_exact (environment : SchemeEnv scopes α) (index : Nat) (out : CompTerm α)
    (assignment : α → Computation) :
    (Scheme.lookup environment index out).Holds assignment ↔ SchemeLookup assignment environment index (out.eval Common.model assignment) := by
  unfold Scheme.lookup SchemeLookup
  cases environment[index]? <;> simp [Core.PresenceGeneration.Formula.Holds]
theorem EnvRel.nil (signatures : List SemanticSignature) (ρ : α → Comp Common.model) : EnvRel (scopes := scopes) signatures ρ [] [] := by
  intro n c
  simp [SchemeLookup, BindingLookup]

theorem EnvRel.cons {signatures : List SemanticSignature} {ρ : α → Comp Common.model} {sΓ : SchemeEnv scopes α}
    {Γ : List (Binding scopes)} {s : Scheme scopes α} {b : Binding scopes} (h : EnvRel signatures ρ sΓ Γ)
    (head : ∀ c, s.Holds (extend ρ c) ↔ BindingTyping signatures b c) :
    EnvRel signatures ρ (s :: sΓ) (b :: Γ) := by
  intro n c
  cases n with
  | zero => simpa [SchemeLookup, BindingLookup] using head c
  | succ n => simpa [SchemeLookup, BindingLookup] using h n c

theorem EnvRel.mono {signatures : List SemanticSignature} {ρ : α → Comp Common.model} {sΓ : SchemeEnv scopes α}
    {Γ : List (Binding scopes)} (h : EnvRel signatures ρ sΓ Γ) (a : CompTerm α) :
    EnvRel signatures ρ (Scheme.mono a :: sΓ) (.mono (a.eval Common.model ρ) :: Γ) := by
  apply h.cons
  intro c
  simp

theorem EnvRel.rename {signatures : List SemanticSignature} {ρ : α → Comp Common.model} {sΓ : SchemeEnv scopes α}
    {Γ : List (Binding scopes)} (h : EnvRel signatures ρ sΓ Γ) (f : α → β) (η : β → Comp Common.model)
    (he : η ∘ f = ρ) : EnvRel signatures η (sΓ.rename f) Γ := by
  intro n c
  have hn := h n c
  unfold SchemeLookup at hn ⊢
  simp only [SchemeEnv.rename, List.getElem?_map]
  cases hs : sΓ[n]? with
  | none => simpa [hs] using hn
  | some s =>
      simp only [Option.map_some, Formula.holds_rename]
      have he' : extend η c ∘ Option.map f = extend ρ c := by
        funext x
        cases x with
        | none => rfl
        | some x => exact congrFun he x
      simpa only [he', hs] using hn

theorem EnvRel.lift {signatures : List SemanticSignature} {ρ : α → Comp Common.model} {sΓ : SchemeEnv scopes α}
    {Γ : List (Binding scopes)} (h : EnvRel signatures ρ sΓ Γ) (a : Comp Common.model) :
    EnvRel signatures (extend ρ a) sΓ.lift Γ := by
  intro n c
  have hn := h n c
  unfold SchemeLookup at hn ⊢
  simp only [SchemeEnv.lift, SchemeEnv.rename, List.getElem?_map]
  cases hs : sΓ[n]? with
  | none => simpa [hs] using hn
  | some s =>
      simp only [Option.map_some, Formula.holds_rename]
      have he : extend (extend ρ a) c ∘ Option.map some = extend ρ c := by
        funext x
        cases x <;> rfl
      simpa only [he, hs] using hn


/-- Exactly the independent declaration interpretation and input-environment
correspondence required by finite generation. Neither field mentions solving. -/
structure ContextRel (signatures : List SemanticSignature) (declarations : Declarations α)
    (assignment : α → Computation) (environment : SchemeEnv scopes α) (bindings : List (Binding scopes)) : Prop where
  declarations : interpretAll assignment declarations = signatures
  environment : EnvRel signatures assignment environment bindings

theorem ContextRel.mono {signatures : List SemanticSignature} {declarations : Declarations α}
    {assignment : α → Computation} {environment : SchemeEnv scopes α} {bindings : List (Binding scopes)}
    (related : ContextRel signatures declarations assignment environment bindings) (value : CompTerm α) :
    ContextRel signatures declarations assignment (Scheme.mono value :: environment)
      (.mono (value.eval Common.model assignment) :: bindings) :=
  ⟨related.declarations, related.environment.mono value⟩

theorem ContextRel.cons {signatures : List SemanticSignature} {declarations : Declarations α}
    {assignment : α → Computation} {environment : SchemeEnv scopes α} {bindings : List (Binding scopes)}
    (related : ContextRel signatures declarations assignment environment bindings)
    {scheme : Scheme scopes α} {binding : Binding scopes}
    (head : ∀ value, scheme.Holds (extend assignment value) ↔ BindingTyping signatures binding value) :
    ContextRel signatures declarations assignment (scheme :: environment) (binding :: bindings) :=
  ⟨related.declarations, related.environment.cons head⟩

theorem ContextRel.lift {signatures : List SemanticSignature} {declarations : Declarations α}
    {assignment : α → Computation} {environment : SchemeEnv scopes α} {bindings : List (Binding scopes)}
    (related : ContextRel signatures declarations assignment environment bindings) (value : Computation) :
    ContextRel signatures (renameAll some declarations) (extend assignment value) environment.lift bindings := by
  refine ⟨?_, related.environment.lift value⟩
  rw [CommonEffectMixedDeclarations.interpretAll_extend]
  exact related.declarations

theorem ContextRel.rename {signatures : List SemanticSignature} {declarations : Declarations α}
    {assignment : α → Computation} {environment : SchemeEnv scopes α} {bindings : List (Binding scopes)}
    (related : ContextRel signatures declarations assignment environment bindings) (names : α → β)
    (next : β → Computation) (same : next ∘ names = assignment) :
    ContextRel signatures (renameAll names declarations) next (environment.rename names) bindings := by
  refine ⟨?_, related.environment.rename names next same⟩
  rw [CommonEffectMixedDeclarations.interpretAll_rename, same]
  exact related.declarations
end Yulang.CommonEffectMixedGeneration
