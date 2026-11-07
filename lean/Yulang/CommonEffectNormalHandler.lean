import Yulang.CommonEffectOutputWeakening

/-! Real finite handler formulas after uniform elimination of the arm-root
result slot. This is an exact projection, not retraction of valuations of
eliminated internal nodes. General operation-local universals remain. -/
namespace Yulang.CommonEffectNormalHandler
open Core.PresenceGeneration (Comp CompTerm TyTerm RowTerm extend extend_none extend_some)
open CommonEffectRequestGeneration (Computation Declaration Declarations RowExpr localEnv localEnv_comp_inl)
open CommonEffectFormula
open CommonEffectRecursiveSource
open CommonEffectRecursiveGeneration
open CommonEffectDeclarationInterpretation (rename renameAll interpret interpret_rename lookup_interpretAll)
open CommonEffectPresence (fresh₀ fresh₁ env₂ lift₂)

variable {scopes : Nat}

def armEnvironment (schemes : SchemeEnv scopes α) (declaration : Declaration α) (input : CompTerm α) :
    SchemeEnv scopes (α ⊕ Fin declaration.locals) :=
  Scheme.mono (CompTerm.pure declaration.input) ::
  Scheme.mono (CompTerm.pure (CompTerm.arrow (CompTerm.pure declaration.output) (input.rename Sum.inl))) ::
  schemes.rename Sum.inl

def generateArm (declarations : Declarations α) (schemes : SchemeEnv scopes α) (declaration : Declaration α)
    (input out : CompTerm α) (body : Expr scopes) : Formula scopes α :=
  .forallTypes declaration.locals
    (generate (renameAll Sum.inl declarations) (armEnvironment schemes declaration input) body (out.rename Sum.inl))

theorem generateArm_exact (signatures : List SemanticSignature) {declarations : Declarations α}
    (schemes : SchemeEnv scopes α) (environment : List (Binding scopes)) (assignment : α → Computation)
    (related : ContextRel signatures declarations assignment schemes environment)
    (declaration : Declaration α) (input out : CompTerm α) (body : Expr scopes) :
    (generateArm declarations schemes declaration input out body).Holds assignment ↔
      ∀ locals : Fin (interpret assignment declaration).locals → Common.Ty,
        Typing signatures
          (.mono (Comp.pure Common.model ((interpret assignment declaration).input locals)) ::
           .mono (Comp.pure Common.model (Comp.arrow Common.model
             (Comp.pure Common.model ((interpret assignment declaration).output locals)) (input.eval Common.model assignment))) ::
           environment) body (out.eval Common.model assignment) := by
  have each (locals : Fin declaration.locals → Common.Ty) :=
    CommonEffectRecursiveExact.generate_recursive_effect_exact signatures body
      (armEnvironment schemes declaration input) _ (localEnv assignment locals) (out.rename Sum.inl)
      ((((related.rename Sum.inl (localEnv assignment locals) rfl).mono
          (CompTerm.pure (CompTerm.arrow (CompTerm.pure declaration.output) (input.rename Sum.inl)))).mono
          (CompTerm.pure declaration.input)))
  simp only [armEnvironment, CompTerm.eval_pure, CompTerm.eval_rename, localEnv_comp_inl] at each
  simp only [generateArm, Formula.Holds]
  apply forall_congr'; intro locals
  simpa only [armEnvironment, CompTerm.arrow, CompTerm.pure, CompTerm.rename, CompTerm.eval,
    Comp.arrow, Comp.pure, interpret, TyTerm.eval, RowTerm.eval,
    TyTerm.eval_rename, RowTerm.eval_rename, localEnv_comp_inl] using each locals

def baseChecks (handled : List Nat) (input returned out : CompTerm α) : Formula scopes α :=
  .and (.tyLe returned.ty out.ty)
    (.rowLe (.union (.residual handled (RowExpr.fromPresence input.row)) (RowExpr.fromPresence returned.row))
      (RowExpr.fromPresence out.row))

theorem baseChecks_exact (handled : List Nat) (input returned out : CompTerm α) (assignment : α → Computation) :
    (baseChecks (scopes := scopes) handled input returned out).Holds assignment ↔
      Common.Subtype (returned.eval Common.model assignment).1 (out.eval Common.model assignment).1 ∧
      Common.rowLe (Common.rowJoin (CommonSignedRows.commonResidual handled (input.eval Common.model assignment).2)
        (returned.eval Common.model assignment).2) (out.eval Common.model assignment).2 := by
  simp only [baseChecks, Formula.Holds, Formula.holds_tyLe, RowExpr.eval, RowExpr.eval_fromPresence]
  rfl

def generateHandler (declarations : Declarations α) (schemes : SchemeEnv scopes α)
    (permission : CommonEffectRequestGeneration.Permission) (operation : Nat)
    (action onReturn onOperation : Expr scopes) (out : CompTerm α) : Formula scopes α :=
  match declarations[operation]? with
  | none => .core .bot
  | some declaration =>
    if permission.allows declaration.key then
      .existsSlot (.existsSlot (.and
        (generate (decl₂ declarations) (env₂ schemes) action fresh₀)
        (.and (generate (decl₂ declarations) (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ schemes) onReturn fresh₁)
          (.and (baseChecks [declaration.key] fresh₀ fresh₁ (lift₂ out))
            (generateArm (decl₂ declarations) (env₂ schemes) (rename (fun name => some (some name)) declaration)
              fresh₀ (lift₂ out) onOperation)))))
    else .core .bot

theorem generate_handler_exact (signatures : List SemanticSignature) {declarations : Declarations α}
    (schemes : SchemeEnv scopes α) (environment : List (Binding scopes)) (assignment : α → Computation)
    (related : ContextRel signatures declarations assignment schemes environment)
    (permission : CommonEffectRequestGeneration.Permission) (operation : Nat)
    (action onReturn onOperation : Expr scopes) (out : CompTerm α) :
    (generateHandler declarations schemes permission operation action onReturn onOperation out).Holds assignment ↔
      Typing signatures environment (.handler permission operation action onReturn onOperation) (out.eval Common.model assignment) := by
  cases found : declarations[operation]? with
  | none =>
    have absent : signatures[operation]? = none := by
      rw [← related.declarations, lookup_interpretAll, found]
      rfl
    simp [generateHandler, found, Formula.Holds, Core.PresenceGeneration.Formula.Holds,
      CommonEffectOutputWeakening.handler_at_output_iff, absent]
  | some declaration =>
    have resolved : signatures[operation]? = some (interpret assignment declaration) := by
      rw [← related.declarations, lookup_interpretAll, found]
      rfl
    have actionExact (a b : Computation) :=
      CommonEffectRecursiveExact.generate_recursive_effect_exact signatures action
        (env₂ schemes) environment (extend (extend assignment a) b) fresh₀ ((related.lift a).lift b)
    have returnExact (a b : Computation) :=
      CommonEffectRecursiveExact.generate_recursive_effect_exact signatures onReturn
        (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ schemes) _ (extend (extend assignment a) b) fresh₁
        (((related.lift a).lift b).mono (CompTerm.pure fresh₀.ty))
    have armExact (a b : Computation) := generateArm_exact signatures (env₂ schemes) environment
      (extend (extend assignment a) b) ((related.lift a).lift b)
      (rename (fun name => some (some name)) declaration) fresh₀ (lift₂ out) onOperation
    simp only [CompTerm.eval_var, fresh₀, fresh₁, extend_none, extend_some, CompTerm.eval_pure] at actionExact returnExact
    simp only [interpret, rename, TyTerm.eval_rename,
      CommonEffectDeclarationInterpretation.localEnv_names] at armExact
    have same (a b : Computation) : extend (extend assignment a) b ∘ (fun name => some (some name)) = assignment := rfl
    simp only [same, CompTerm.eval_var, fresh₀, extend_some, extend_none,
      lift₂, CompTerm.eval_rename] at armExact
    cases allowed : permission.allows declaration.key with
    | false =>
      simp [generateHandler, found, allowed, Formula.Holds, Core.PresenceGeneration.Formula.Holds,
        CommonEffectOutputWeakening.handler_at_output_iff, resolved, interpret]
    | true =>
      have shape :
          (generateHandler declarations schemes permission operation action onReturn onOperation out).Holds assignment ↔
            ∃ input returned,
              Typing signatures environment action input ∧
              Typing signatures (.mono (Comp.pure Common.model input.1) :: environment) onReturn returned ∧
              Common.Subtype returned.1 (out.eval Common.model assignment).1 ∧
              Common.rowLe (Common.rowJoin (CommonSignedRows.commonResidual [declaration.key] input.2) returned.2)
                (out.eval Common.model assignment).2 ∧
              ∀ locals : Fin (interpret assignment declaration).locals → Common.Ty,
                Typing signatures
                  (.mono (Comp.pure Common.model ((interpret assignment declaration).input locals)) ::
                   .mono (Comp.pure Common.model (Comp.arrow Common.model
                     (Comp.pure Common.model ((interpret assignment declaration).output locals)) input)) :: environment)
                  onOperation (out.eval Common.model assignment) := by
        simp only [generateHandler, found, allowed, ↓reduceIte, Formula.Holds]
        simp only [decl₂, env₂, fresh₀, fresh₁, lift₂, rename] at actionExact returnExact armExact ⊢
        simp only [actionExact, returnExact, armExact, baseChecks_exact]
        simp only [CompTerm.eval_var, CompTerm.eval_rename, extend_none, extend_some,
          same, and_assoc]
        rfl
      rw [shape, CommonEffectOutputWeakening.handler_at_output_iff]
      simp [resolved, interpret, allowed]
def checkedArm (declarations : Declarations α) (schemes : SchemeEnv scopes α)
    (permission : CommonEffectRequestGeneration.Permission) (operation : Nat)
    (input out : CompTerm α) (body : Expr scopes) : Formula scopes α :=
  match declarations[operation]? with
  | none => .core .bot
  | some declaration =>
    if permission.allows declaration.key then generateArm declarations schemes declaration input out body else .core .bot

theorem checkedArm_exact (signatures : List SemanticSignature) {declarations : Declarations α}
    (schemes : SchemeEnv scopes α) (environment : List (Binding scopes)) (assignment : α → Computation)
    (related : ContextRel signatures declarations assignment schemes environment)
    (permission : CommonEffectRequestGeneration.Permission) (operation : Nat)
    (input out : CompTerm α) (body : Expr scopes) :
    (checkedArm declarations schemes permission operation input out body).Holds assignment ↔
      ∃ signature, signatures[operation]? = some signature ∧ permission.allows signature.key = true ∧
        ∀ locals : Fin signature.locals → Common.Ty,
          Typing signatures
            (.mono (Comp.pure Common.model (signature.input locals)) ::
             .mono (Comp.pure Common.model (Comp.arrow Common.model
               (Comp.pure Common.model (signature.output locals)) (input.eval Common.model assignment))) :: environment)
            body (out.eval Common.model assignment) := by
  cases found : declarations[operation]? with
  | none =>
    have absent : signatures[operation]? = none := by
      rw [← related.declarations, lookup_interpretAll, found]
      rfl
    simp [checkedArm, found, Formula.Holds, Core.PresenceGeneration.Formula.Holds, absent]
  | some declaration =>
    have resolved : signatures[operation]? = some (interpret assignment declaration) := by
      rw [← related.declarations, lookup_interpretAll, found]
      rfl
    cases allowed : permission.allows declaration.key with
    | false => simp [checkedArm, found, allowed, Formula.Holds, Core.PresenceGeneration.Formula.Holds, resolved, interpret]
    | true =>
      simp only [checkedArm, found, allowed, ↓reduceIte,
        generateArm_exact signatures schemes environment assignment related]
      simp [resolved, interpret, allowed]

def generateMany (declarations : Declarations α) (schemes : SchemeEnv scopes α)
    (permission : CommonEffectRequestGeneration.Permission) (operations : Fin count → Nat)
    (action onReturn : Expr scopes) (bodies : Fin count → Expr scopes) (out : CompTerm α) : Formula scopes α :=
  .existsSlot (.existsSlot (.and
    (generate (decl₂ declarations) (env₂ schemes) action fresh₀)
    (.and (generate (decl₂ declarations) (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ schemes) onReturn fresh₁)
      (.and (baseChecks (declarationKeys declarations operations) fresh₀ fresh₁ (lift₂ out))
        (CommonEffectUniversalArms.andAll ((List.finRange count).map (fun i =>
          checkedArm (decl₂ declarations) (env₂ schemes) permission (operations i) fresh₀ (lift₂ out) (bodies i))))))))

theorem generate_many_exact (signatures : List SemanticSignature) {declarations : Declarations α}
    (schemes : SchemeEnv scopes α) (environment : List (Binding scopes)) (assignment : α → Computation)
    (related : ContextRel signatures declarations assignment schemes environment)
    (permission : CommonEffectRequestGeneration.Permission) (operations : Fin count → Nat)
    (action onReturn : Expr scopes) (bodies : Fin count → Expr scopes) (out : CompTerm α) :
    (generateMany declarations schemes permission operations action onReturn bodies out).Holds assignment ↔
      Typing signatures environment (.multiHandler permission operations action onReturn bodies) (out.eval Common.model assignment) := by
  have actionExact (a b : Computation) :=
    CommonEffectRecursiveExact.generate_recursive_effect_exact signatures action
      (env₂ schemes) environment (extend (extend assignment a) b) fresh₀ ((related.lift a).lift b)
  have returnExact (a b : Computation) :=
    CommonEffectRecursiveExact.generate_recursive_effect_exact signatures onReturn
      (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ schemes) _ (extend (extend assignment a) b) fresh₁
      (((related.lift a).lift b).mono (CompTerm.pure fresh₀.ty))
  have armExact (a b : Computation) (i : Fin count) :=
    checkedArm_exact signatures (env₂ schemes) environment (extend (extend assignment a) b)
      ((related.lift a).lift b) permission (operations i) fresh₀ (lift₂ out) (bodies i)
  have keys : handlerKeys signatures operations = declarationKeys declarations operations := by
    rw [← related.declarations, declarationKeys_interpret]
  have same (a b : Computation) : extend (extend assignment a) b ∘ (fun name => some (some name)) = assignment := rfl
  rw [CommonEffectOutputWeakening.multi_handler_at_output_iff]
  simp only [generateMany, Formula.Holds, andAll_fin]
  simp only [decl₂, env₂, fresh₀, fresh₁, lift₂] at actionExact returnExact armExact ⊢
  simp only [actionExact, returnExact, armExact, baseChecks_exact]
  simp only [CompTerm.eval_var, CompTerm.eval_rename, extend_none, extend_some,
    same, and_assoc, keys]
  rfl

theorem generate_many_same_holds (signatures : List SemanticSignature) {declarations : Declarations α}
    (schemes : SchemeEnv scopes α) (environment : List (Binding scopes)) (assignment : α → Computation)
    (related : ContextRel signatures declarations assignment schemes environment)
    (permission : CommonEffectRequestGeneration.Permission) (operations : Fin count → Nat)
    (action onReturn : Expr scopes) (bodies : Fin count → Expr scopes) (out : CompTerm α) :
    (generateMany declarations schemes permission operations action onReturn bodies out).Holds assignment ↔
      (generate declarations schemes (.multiHandler permission operations action onReturn bodies) out).Holds assignment :=
  (generate_many_exact signatures schemes environment assignment related permission operations action onReturn bodies out).trans
    (CommonEffectRecursiveExact.generate_recursive_effect_exact signatures
      (.multiHandler permission operations action onReturn bodies) schemes environment assignment out related).symm
end Yulang.CommonEffectNormalHandler
