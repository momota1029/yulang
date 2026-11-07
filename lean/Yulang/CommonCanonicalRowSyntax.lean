import Yulang.CommonCanonicalRowGrid
import Yulang.CommonCanonicalRowConstraints
import Yulang.QualifiedGeneralization

/-!
# Finite signed-row interfaces and the existing public binding semantics

This is a fragment for an obstruction reduction, not a replacement for A2's
full grammar. Its only closed recursive rows are explicit finite `AsRow`
bodies generated from a list of coordinate shifts. Other row expressions are
the existing finite-mask `CommonEffectRequestGeneration.RowExpr` syntax.

The value grammar is unit, pair, union and general arrows. Generalized row
assignments are unrestricted Common rows. Meaning is the original
`QualifiedInference.BindingTyping`, not an alpha equivalence or a constrained
parameter interpretation. All role requirements are empty in this fragment.
-/

namespace Yulang.CommonCanonicalRowSyntax

structure ClosedRow (scopes : Nat) where
  enabled : List (Fin scopes)
  deriving DecidableEq, Repr

def ClosedRow.body (closed : ClosedRow scopes) : RowInference.RowExpr Nat (Fin scopes) Unit :=
  .union (.head 0) (closed.enabled.foldr
    (fun coordinate rest => .union (.protect coordinate Directed.allowNone (.var ())) rest) .empty)

def ClosedRow.binder (closed : ClosedRow scopes) : RecursiveRowDisplay.AsRow scopes Nat :=
  ⟨"grid", closed.body⟩

def ClosedRow.meaning (closed : ClosedRow scopes) : Common.Row :=
  CommonCanonicalRowGrid.embedSet closed.binder.Meaning

abbrev Row (scopes parameters : Nat) :=
  CommonEffectRequestGeneration.RowExpr scopes (Fin parameters ⊕ ClosedRow scopes)

def rowEval (parameters : Fin count → Common.Row) (row : Row scopes count) : Common.Row :=
  row.eval (Sum.elim (fun index => (.base .unit, parameters index))
    (fun closed => (.base .unit, closed.meaning)))

inductive Form (scopes parameters : Nat) where
  | unit : Form scopes parameters
  | pair : Form scopes parameters → Form scopes parameters → Form scopes parameters
  | union : Form scopes parameters → Form scopes parameters → Form scopes parameters
  | arrow : Form scopes parameters → Row scopes parameters →
      Form scopes parameters → Row scopes parameters → Form scopes parameters

def Form.eval (parameters : Fin count → Common.Row) : Form scopes count → Common.Ty
  | .unit => .base .unit
  | .pair first last => Common.pair (first.eval parameters) (last.eval parameters)
  | .union first last => .union (first.eval parameters) (last.eval parameters)
  | .arrow input incoming output outgoing =>
      Common.arrow (input.eval parameters) (rowEval parameters incoming)
        (output.eval parameters) (rowEval parameters outgoing)

def rowRename (mapping : Fin first → Fin last) : Row scopes first → Row scopes last
  | .var (.inl index) => .var (.inl (mapping index))
  | .var (.inr closed) => .var (.inr closed)
  | .empty => .empty
  | .head key => .head key
  | .union before after => .union (rowRename mapping before) (rowRename mapping after)
  | .protect scope permission source => .protect scope permission (rowRename mapping source)
  | .release scope permission source => .release scope permission (rowRename mapping source)
  | .residual handled source => .residual handled (rowRename mapping source)

def Form.rename (mapping : Fin first → Fin last) : Form scopes first → Form scopes last
  | .unit => .unit
  | .pair before after => .pair (before.rename mapping) (after.rename mapping)
  | .union before after => .union (before.rename mapping) (after.rename mapping)
  | .arrow input incoming output outgoing =>
      .arrow (input.rename mapping) (rowRename mapping incoming)
        (output.rename mapping) (rowRename mapping outgoing)

/-- Renaming preserves every finite row expression and its shared
parameters. The mapping need not be injective, surjective, or a bijection. -/
theorem rename_eval (mapping : Fin first → Fin last) (form : Form scopes first)
    (parameters : Fin last → Common.Row) :
    (form.rename mapping).eval parameters = form.eval (parameters ∘ mapping) := by
  have rows (row : Row scopes first) :
      rowEval parameters (rowRename mapping row) = rowEval (parameters ∘ mapping) row := by
    induction row with
    | var index => cases index <;> rfl
    | empty | head => rfl
    | union before after ihb iha =>
        exact congr (congrArg Common.rowJoin ihb) iha
    | protect scope permission source ih =>
        exact congrArg (CommonSignedRows.commonProtect scope.val permission.allows) ih
    | release scope permission source ih =>
        exact congrArg (CommonSignedRows.commonRelease scope.val permission.allows) ih
    | residual handled source ih =>
        exact congrArg (CommonSignedRows.commonResidual handled) ih
  induction form <;> simp_all [Form.rename, Form.eval]

structure Interface where
  scopes : Nat
  parameters : Nat
  value : Form scopes parameters

abbrev model := Common.model.toModel

def Interface.binding (interface : Interface) : QualifiedInference.Binding model :=
  .qualified interface.parameters (fun _ => [])
    (fun parameters => Inference.Comp.pure model
      (interface.value.eval (fun index => (parameters index).2)))

/-- Every finite syntax value is read through the existing public binding
judgment. Both directions quantify all rows and all targets; no finite-support
or parameter-satisfaction premise is introduced. -/
theorem binding_instances_exact (interface : Interface) (theory : RoleConstraints.Theory model)
    (target : Inference.Comp model) :
    QualifiedInference.BindingTyping model theory interface.binding target ↔
      ∃ parameters : Fin interface.parameters → Common.Row,
        Common.Subtype (interface.value.eval parameters) target.1 := by
  unfold Interface.binding
  rw [QualifiedInference.BindingTyping.qualified_iff]
  constructor
  · rintro ⟨parameters, _, below⟩
    exact ⟨fun index => (parameters index).2, below.1⟩
  · rintro ⟨parameters, below⟩
    exact ⟨fun index => (.base .unit, parameters index), by simp [RoleConstraints.Satisfies],
      below, Common.rowEmpty_le target.2⟩

end Yulang.CommonCanonicalRowSyntax
