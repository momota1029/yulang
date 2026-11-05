import Yulang.OperationalTyping
import Yulang.FreshRowInference

/-!
# Checked computations across fresh effect boundaries

This connects the executable resolved-program checker to the existing signed
boundary allocation and inferred-row syntax. Operational bounds are derived
from checker success. Zero origin is then derived either from the inferred
row's fresh-coordinate representation or from explicit tree allocation.

The boundary acts on immediate requests and keeps returned values opaque.
In particular, this module does not claim a type-directed transformation of
latent closures, source scope allocation, or safety for arbitrary source ASTs.
-/

namespace Yulang.CheckedHygiene

open Directed
open OperationalTyping (Expr CTy Env Tree Value EnvValid infer eval)
open RowInference (RowExpr signedAlgebra)
open FreshBoundaries (fresh liftOccurrence liftTree)
open FreshRowInference (liftRow liftEnvironment)

/-- A checked program whose inferred row is represented over the old scopes
cannot emit a request carrying a nonzero weight at the fresh coordinate. -/
theorem inferred_fresh_origin [DecidableEq Key]
    (expression : Expr (n + 1) Key Atom Γ s) (types : Env (CTy (n + 1) Key) Γ)
    (output : CTy (n + 1) Key s) (accepted : infer types expression = some output)
    (runtime : Env (Tree (n + 1) Key Atom) Γ) (environment : EnvValid types runtime)
    (row : RowExpr Key (Fin n) α) (rows : α → Row n Key)
    (representation : output.row = (liftRow row).eval (signedAlgebra (n + 1) Key)
      (liftEnvironment rows)) :
    Computation.ZeroAt fresh (eval runtime expression) := by
  have bounded := (OperationalTyping.inferred_operationally_valid
    expression types output accepted runtime environment).1
  rw [representation] at bounded
  exact FreshRowInference.bounded_fresh_origin row rows (eval runtime expression) bounded

/-- The row representation and checker result replace an operational ZeroAt
or per-handler-arm bound hypothesis. All request branches are covered. -/
theorem inferred_fresh_noncapture [DecidableEq Key]
    (expression : Expr (n + 1) Key Atom Γ s) (types : Env (CTy (n + 1) Key) Γ)
    (output : CTy (n + 1) Key s) (accepted : infer types expression = some output)
    (runtime : Env (Tree (n + 1) Key Atom) Γ) (environment : EnvValid types runtime)
    (row : RowExpr Key (Fin n) α) (rows : α → Row n Key)
    (representation : output.row = (liftRow row).eval (signedAlgebra (n + 1) Key)
      (liftEnvironment rows))
    (handled : List Key)
    (onReturn : Value (n + 1) Key Atom s → Computation (n + 1) Key Atom Atom Result)
    (onOperation : Occurrence (n + 1) Key → Atom →
      (Atom → Tree (n + 1) Key Atom s) → Computation (n + 1) Key Atom Atom Result) :
    Computation.shallowHandle handled onReturn onOperation
      (Computation.mapRequests (protect fresh allowNone) (eval runtime expression)) =
        (Computation.mapRequests (protect fresh allowNone) (eval runtime expression)).bind onReturn :=
  Computation.default_zero_boundary_noncapture handled fresh onReturn onOperation
    (eval runtime expression)
    (inferred_fresh_origin expression types output accepted runtime environment row rows representation)

/-- Explicit allocation always supplies an appropriate fresh interface,
preserving old negative debts and the checked computation's row bound. -/
theorem allocated_inferred_bound [DecidableEq Key]
    (expression : Expr n Key Atom Γ s) (types : Env (CTy n Key) Γ)
    (output : CTy n Key s) (accepted : infer types expression = some output)
    (runtime : Env (Tree n Key Atom) Γ) (environment : EnvValid types runtime)
    (permission : Permission Key) :
    Computation.BoundedBy
      (output.row.map (fun occurrence => protect fresh permission (liftOccurrence occurrence)))
      (Computation.mapRequests (protect fresh permission) (liftTree (eval runtime expression))) := by
  have bounded := (OperationalTyping.inferred_operationally_valid
    expression types output accepted runtime environment).1
  have lifted := (FreshBoundaries.reindexTree_bounded_iff Fin.succ
    FreshBoundaries.succ_injective output.row (eval runtime expression)).mpr bounded
  have guarded := Computation.mapRequests_bounded (protect fresh permission) _ _ lifted
  simpa only [liftTree, liftOccurrence, List.map_map, Function.comp_def] using guarded

/-- Closed checker success entails a sound fresh row and noncapture by every
inner shallow handler. No external environment or operational bound is given. -/
theorem closed_checked_boundary [DecidableEq Key]
    (expression : Expr n Key Atom [] s) (output : CTy n Key s)
    (accepted : infer Env.nil expression = some output)
    (handled : List Key)
    (onReturn : Value n Key Atom s → Computation (n + 1) Key Atom Atom Result)
    (onOperation : Occurrence (n + 1) Key → Atom →
      (Atom → Computation (n + 1) Key Atom Atom (Value n Key Atom s)) →
        Computation (n + 1) Key Atom Atom Result) :
    Computation.BoundedBy
      (output.row.map (fun occurrence => protect fresh allowNone (liftOccurrence occurrence)))
      (Computation.mapRequests (protect fresh allowNone) (liftTree (eval Env.nil expression))) ∧
    Computation.shallowHandle handled onReturn onOperation
      (Computation.mapRequests (protect fresh allowNone) (liftTree (eval Env.nil expression))) =
        (Computation.mapRequests (protect fresh allowNone) (liftTree (eval Env.nil expression))).bind
          onReturn :=
  ⟨allocated_inferred_bound expression Env.nil output accepted Env.nil
      (fun index => nomatch index) allowNone,
    FreshBoundaries.fresh_noncapture handled onReturn onOperation (eval Env.nil expression)⟩

end Yulang.CheckedHygiene
