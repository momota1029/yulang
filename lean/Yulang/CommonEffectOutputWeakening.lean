import Yulang.CommonEffectRecursiveExact
import Yulang.CommonEffectArmGeneration

/-! Output weakening of the independent recursive effect judgment. This
uniformly removes an arm's result witness by typing that same body at the
already-fixed outer output. The environment and shallow continuation input
are unchanged; no universal local check is assumed or discarded. -/
namespace Yulang.CommonEffectOutputWeakening
open Core.PresenceGeneration (Comp CompTerm)
open CommonEffectRequestGeneration (Computation)
open CommonEffectRecursiveSource
open CommonEffectRecursiveGeneration
open CommonEffectFormula

variable {scopes : Nat}

theorem comp_refl (value : Computation) : Comp.le Common.model value value :=
  ⟨Common.subtype_refl _, Common.rowLe_refl _⟩

theorem comp_trans {first middle last : Computation}
    (before : Comp.le Common.model first middle) (after : Comp.le Common.model middle last) :
    Comp.le Common.model first last :=
  ⟨Common.subtype_trans before.1 after.1, Common.rowLe_trans before.2 after.2⟩

theorem typing_weaken {signatures : List SemanticSignature} {environment : List (Binding scopes)}
    {body : Expr scopes} {source : Computation} (typed : Typing signatures environment body source) :
    ∀ target, Comp.le Common.model source target → Typing signatures environment body target := by
  induction typed using Typing.rec
      (motive_2 := fun binding source _ => ∀ target, Comp.le Common.model source target → BindingTyping signatures binding target) with
  | var found _ ih => intro target below; exact .var found (ih target below)
  | lit bound => intro target below; exact .lit (comp_trans bound below)
  | lam bodyTyped bound _ => intro target below; exact .lam bodyTyped (comp_trans bound below)
  | app functionTyped argumentTyped bound _ _ =>
    intro target below; exact .app functionTyped argumentTyped (comp_trans bound below)
  | letValue value pureTyped bodyTyped _ ih =>
    intro target below; exact .letValue value pureTyped (ih target below)
  | letComputed valueTyped bodyTyped bound _ _ =>
    intro target below; exact .letComputed valueTyped bodyTyped (comp_trans bound below)
  | branch conditionTyped yesTyped noTyped bound _ _ _ =>
    intro target below; exact .branch conditionTyped yesTyped noTyped (comp_trans bound below)
  | pair firstTyped lastTyped bound _ _ =>
    intro target below; exact .pair firstTyped lastTyped (comp_trans bound below)
  | fst bodyTyped bound _ => intro target below; exact .fst bodyTyped (comp_trans bound below)
  | snd bodyTyped bound _ => intro target below; exact .snd bodyTyped (comp_trans bound below)
  | emptyRecord bound => intro target below; exact .emptyRecord (comp_trans bound below)
  | record headTyped restTyped records bound _ _ =>
    intro target below; exact .record headTyped restTyped records (comp_trans bound below)
  | recordDefault sourceTyped fallbackTyped records bound _ _ =>
    intro target below; exact .recordDefault sourceTyped fallbackTyped records (comp_trans bound below)
  | field bodyTyped bound _ => intro target below; exact .field bodyTyped (comp_trans bound below)
  | variant bodyTyped bound _ => intro target below; exact .variant bodyTyped (comp_trans bound below)
  | request found payloadTyped valueBound rowBound _ =>
    intro target below
    exact .request found payloadTyped (Common.subtype_trans valueBound below.1) (Common.rowLe_trans rowBound below.2)
  | boundary bodyTyped valueBound rowBound _ =>
    intro target below
    exact .boundary bodyTyped (Common.subtype_trans valueBound below.1) (Common.rowLe_trans rowBound below.2)
  | handler found allowed actionTyped returnTyped arms values rows _ _ _ =>
    intro target below
    exact .handler found allowed actionTyped returnTyped arms
      (fun types => Common.subtype_trans (values types) below.1)
      (fun types => Common.rowLe_trans (rows types) below.2)
  | multiHandler found allowed actionTyped returnTyped arms values rows bounds _ _ _ =>
    intro target below
    exact .multiHandler found allowed actionTyped returnTyped arms
      (Common.subtype_trans values below.1) (Common.rowLe_trans rows below.2)
      (fun index types => comp_trans (bounds index types) below)
  | mono bound => rename_i target below; exact .mono (comp_trans bound below)
  | poly pureTyped rows ih =>
    rename_i target below
    exact .poly (ih (Comp.pure Common.model target.1) ⟨below.1, Common.rowLe_refl _⟩)
      (Common.rowLe_trans rows below.2)
  | signature bound => rename_i target below; exact .signature (comp_trans bound below)

theorem binding_weaken {signatures : List SemanticSignature} {binding : Binding scopes}
    {source target : Computation} (typed : BindingTyping signatures binding source)
    (below : Comp.le Common.model source target) : BindingTyping signatures binding target := by
  cases typed with
  | mono bound => exact .mono (comp_trans bound below)
  | poly pureTyped rows =>
    exact .poly (typing_weaken pureTyped (Comp.pure Common.model target.1) ⟨below.1, Common.rowLe_refl _⟩)
      (Common.rowLe_trans rows below.2)
  | signature bound => exact .signature (comp_trans bound below)

/-- Any source body, including recursively nested requests/handlers and
captured polymorphic lets, with the whole computation bound kept together. -/
theorem arm_result_exact (signatures : List SemanticSignature) (environment : List (Binding scopes))
    (body : Expr scopes) (out : Computation) :
    (∃ operated, Typing signatures environment body operated ∧ Comp.le Common.model operated out) ↔
      Typing signatures environment body out :=
  ⟨fun ⟨_, typed, below⟩ => typing_weaken typed out below,
    fun typed => ⟨out, typed, comp_refl out⟩⟩

theorem generated_arm_result_exact (signatures : List SemanticSignature) {declarations : CommonEffectRequestGeneration.Declarations α}
    (schemes : SchemeEnv scopes α) (environment : List (Binding scopes)) (assignment : α → Computation)
    (related : ContextRel signatures declarations assignment schemes environment) (body : Expr scopes) (out : CompTerm α) :
    (∃ operated, (generate (CommonEffectDeclarationInterpretation.renameAll some declarations) schemes.lift body (CompTerm.var none)).Holds
        (Core.PresenceGeneration.extend assignment operated) ∧ Comp.le Common.model operated (out.eval Common.model assignment)) ↔
      Typing signatures environment body (out.eval Common.model assignment) := by
  have each (operated : Computation) := CommonEffectRecursiveExact.generate_recursive_effect_exact signatures body
    schemes.lift environment (Core.PresenceGeneration.extend assignment operated) (CompTerm.var none) (related.lift operated)
  simp only [CompTerm.eval_var, Core.PresenceGeneration.extend_none] at each
  simp only [each]
  exact arm_result_exact signatures environment body (out.eval Common.model assignment)
theorem generated_arm_formula_exact (signatures : List SemanticSignature)
    {declarations : CommonEffectRequestGeneration.Declarations α}
    (schemes : SchemeEnv scopes α) (environment : List (Binding scopes)) (assignment : α → Computation)
    (related : ContextRel signatures declarations assignment schemes environment) (body : Expr scopes) (out : CompTerm α) :
    (Formula.existsSlot (.and
      (generate (CommonEffectDeclarationInterpretation.renameAll some declarations) schemes.lift body (CompTerm.var none))
      (Formula.compLe (CompTerm.var none) (out.rename some)))).Holds assignment ↔
      (generate declarations schemes body out).Holds assignment := by
  simp only [Formula.Holds, Formula.holds_compLe, CompTerm.eval_var, CompTerm.eval_rename,
    Core.PresenceGeneration.extend_none, Core.PresenceGeneration.extend_comp_some]
  exact (generated_arm_result_exact signatures schemes environment assignment related body out).trans
    (CommonEffectRecursiveExact.generate_recursive_effect_exact signatures body schemes environment assignment out related).symm

/-- The single-handler result witness is eliminated uniformly, for every
recursive arm body. Outer action/return/environment/output remain fixed. -/
theorem handler_at_output_iff (signatures : List SemanticSignature) (environment : List (Binding scopes))
    (permission : CommonEffectRequestGeneration.Permission) (operation : Nat)
    (action onReturn onOperation : Expr scopes) (out : Computation) :
    Typing signatures environment (.handler permission operation action onReturn onOperation) out ↔
      ∃ signature, signatures[operation]? = some signature ∧ permission.allows signature.key = true ∧
      ∃ input returned,
        Typing signatures environment action input ∧
        Typing signatures (.mono (Comp.pure Common.model input.1) :: environment) onReturn returned ∧
        Common.Subtype returned.1 out.1 ∧
        Common.rowLe (Common.rowJoin (CommonSignedRows.commonResidual [signature.key] input.2) returned.2) out.2 ∧
        ∀ locals : Fin signature.locals → Common.Ty,
          Typing signatures
            (.mono (Comp.pure Common.model (signature.input locals)) ::
             .mono (Comp.pure Common.model (Comp.arrow Common.model
               (Comp.pure Common.model (signature.output locals)) input)) :: environment) onOperation out := by
  rw [Typing.handler_iff]
  apply exists_congr; intro signature
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply exists_congr; intro input
  apply exists_congr; intro returned
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  constructor
  · intro arms
    obtain ⟨_, _, values, rows⟩ := arms (fun _ => .top)
    have valueParts := (CommonEffectUniversalArms.union_le_iff _ _ _).mp values
    have rowParts := (Common.rowJoin_le_iff _ _ _).mp rows
    have returnRows := (Common.rowJoin_le_iff _ _ _).mp rowParts.2
    refine ⟨valueParts.1, (Common.rowJoin_le_iff _ _ _).mpr ⟨rowParts.1, returnRows.1⟩, ?_⟩
    intro locals
    obtain ⟨operated, typed, valueBound, rowBound⟩ := arms locals
    have parts := (Common.rowJoin_le_iff _ _ _).mp rowBound
    exact typing_weaken typed out ⟨((CommonEffectUniversalArms.union_le_iff _ _ _).mp valueBound).2,
      ((Common.rowJoin_le_iff _ _ _).mp parts.2).2⟩
  · rintro ⟨returnValue, baseRows, typed⟩ locals
    have parts := (Common.rowJoin_le_iff _ _ _).mp baseRows
    refine ⟨out, typed locals,
      (CommonEffectUniversalArms.union_le_iff _ _ _).mpr ⟨returnValue, Common.subtype_refl _⟩, ?_⟩
    exact (Common.rowJoin_le_iff _ _ _).mpr ⟨parts.1,
      (Common.rowJoin_le_iff _ _ _).mpr ⟨parts.2, Common.rowLe_refl _⟩⟩

theorem multi_handler_at_output_iff (signatures : List SemanticSignature) (environment : List (Binding scopes))
    (permission : CommonEffectRequestGeneration.Permission) (operations : Fin count → Nat)
    (action onReturn : Expr scopes) (bodies : Fin count → Expr scopes) (out : Computation) :
    Typing signatures environment (.multiHandler permission operations action onReturn bodies) out ↔
      ∃ input returned,
        Typing signatures environment action input ∧
        Typing signatures (.mono (Comp.pure Common.model input.1) :: environment) onReturn returned ∧
        Common.Subtype returned.1 out.1 ∧
        Common.rowLe (Common.rowJoin (CommonSignedRows.commonResidual (handlerKeys signatures operations) input.2)
          returned.2) out.2 ∧
        ∀ i, ∃ signature, signatures[operations i]? = some signature ∧ permission.allows signature.key = true ∧
          ∀ locals : Fin signature.locals → Common.Ty,
            Typing signatures
              (.mono (Comp.pure Common.model (signature.input locals)) ::
               .mono (Comp.pure Common.model (Comp.arrow Common.model
                 (Comp.pure Common.model (signature.output locals)) input)) :: environment) (bodies i) out := by
  simp only [Typing.multiHandler_separate_iff, arm_result_exact]
end Yulang.CommonEffectOutputWeakening
