import Yulang.CommonEffectMixedChecked
import Yulang.CommonPresence

/-!
A nonvacuous checked model of the mixed recursive generator. The operation
signature mentions a captured value, a captured row, a local value and a
local row. Its request payload contains another request, and one shallow
handler encloses both. The handler's result is fixed before either local is
universally quantified. The proof constructs the independent Typing tree;
it does not evaluate a metadata-only success test.
-/
namespace Yulang.CommonEffectMixedWitness
open Core.PresenceGeneration (Comp CompTerm TyTerm)
open CommonEffectRequestGeneration (Computation)
open CommonEffectKindedFormula (Names Locals localEnv)
open CommonEffectMixedDeclarations (Declaration interpret interpretAll)
open CommonEffectMixedKinds (Kind DeclarationsKinded)
open CommonEffectMixedSource (Expr Binding Typing BindingTyping)

/-- `(captured a) -> [captured e, local f] (local b)`. Both independent
operation-local kinds occur, and neither captured name is rebound. -/
def callback : TyTerm (Nat ⊕ Names 1 1) :=
  .arrow (.var (.inl 0)) .empty (.var (.inr (.inl 0)))
    (.join (.var (.inl 1)) (.var (.inr (.inr 0))))

def declaration : Declaration Nat where
  types := 1
  rows := 1
  key := 7
  input := callback
  output := callback

def declarations := [declaration]
def capturedKinds : List Kind := [.value, .row]

theorem declarations_kinded : DeclarationsKinded capturedKinds declarations :=
  (CommonEffectMixedKinds.check_declarations_exact capturedKinds declarations).mp rfl

def chosen (assignment : Nat → Computation) : Locals 1 1 where
  values _ := (assignment 0).1
  effects _ := (assignment 1).2

def signatures (assignment : Nat → Computation) := interpretAll assignment declarations
def callbackType (assignment : Nat → Computation) : Common.Ty :=
  (interpret assignment declaration).input (chosen assignment)

def head : Common.Row := (CommonSignedRows.commonAlgebra 1).head 7
def result : Computation := Comp.pure Common.model (.base .unit)
def output : CompTerm Nat := CompTerm.pure (.base .unit)

def identity : Expr 1 := .lam (.var 0)
def action : Expr 1 := .request 0 (.request 0 identity)
def body : Expr 1 := .handler (.only [7]) 0 action (.lit .unit) (.lit .unit)

private theorem le_self (computation : Computation) : Comp.le Common.model computation computation :=
  ⟨Common.subtype_refl _, Common.rowLe_refl _⟩

theorem identity_typed (assignment : Nat → Computation) :
    Typing (signatures assignment) [] identity (Comp.pure Common.model (callbackType assignment)) := by
  apply Typing.lam (a := Comp.pure Common.model (assignment 0).1)
    (b := ((assignment 0).1, Common.rowJoin (assignment 1).2 (assignment 1).2))
  · apply Typing.var (b := .mono (Comp.pure Common.model (assignment 0).1)) rfl
    exact BindingTyping.mono ⟨Common.subtype_refl _, Common.rowEmpty_le _⟩
  · exact le_self _

private theorem request_typed (assignment : Nat → Computation) (payload : Expr 1) (row : Common.Row)
    (payloadTyped : Typing (signatures assignment) [] payload (callbackType assignment, row))
    (below : Common.rowLe row head) :
    Typing (signatures assignment) [] (.request 0 payload) (callbackType assignment, head) := by
  apply Typing.request (signature := interpret assignment declaration) (locals := chosen assignment)
  · rfl
  · exact payloadTyped
  · exact Common.subtype_refl _
  · intro occurrence present
    rcases present with fromPayload | fromDeclaration
    · exact below occurrence fromPayload
    · rcases fromDeclaration with own | extra
      · exact own
      · exact False.elim extra

theorem action_typed (assignment : Nat → Computation) :
    Typing (signatures assignment) [] action (callbackType assignment, head) :=
  request_typed assignment _ head
    (request_typed assignment identity Common.rowEmpty (identity_typed assignment) (Common.rowEmpty_le _))
    (Common.rowLe_refl _)

private theorem handled_head_empty :
    Common.rowLe (CommonSignedRows.commonResidual [7] head) Common.rowEmpty := by
  rintro occurrence ⟨⟨source, included, rfl⟩, denied⟩
  have same : source = Directed.raw (n := 1) 7 := by simpa using included
  subst source
  exact denied ((CommonSignedRows.encode_capturable_iff [7] (Directed.raw (n := 1) 7)).mpr
    ⟨by simp [Directed.raw], fun _ => rfl⟩)

private theorem unit_typed (assignment : Nat → Computation) (environment : List (Binding 1)) :
    Typing (signatures assignment) environment (.lit .unit) result := Typing.lit (le_self _)

/-- The action input and return result are fixed outside the universal local
binder. Every local type and every arbitrary signed local row is admitted;
the shallow continuation retains this same original action input. -/
theorem body_typed (assignment : Nat → Computation) :
    Typing (signatures assignment) [] body result := by
  apply Typing.handler (signature := interpret assignment declaration)
    (input := (callbackType assignment, head)) (returned := result) (operated := fun _ => result)
  · rfl
  · rfl
  · exact action_typed assignment
  · exact unit_typed assignment _
  · intro locals
    exact unit_typed assignment _
  · intro locals
    exact (Common.common_union_is_join _ _ _).mpr ⟨Common.subtype_refl _, Common.subtype_refl _⟩
  · intro locals occurrence present
    rcases present with residual | arm
    · exact handled_head_empty occurrence residual
    · exact arm.elim False.elim False.elim

/-- An actual model of the actual checked recursively generated formula,
for every captured assignment, including arbitrary signed captured rows.
No input environment, successful solver, support bound or local-kind premise
is assumed. Both local namespaces occur in the checked declaration. -/
theorem checked_nested_model (assignment : Nat → Computation) :
    (CommonEffectMixedChecked.generateChecked capturedKinds declarations [] body output).Holds assignment :=
  (CommonEffectMixedChecked.generate_closed_checked_exact capturedKinds declarations assignment body output).mpr
    ⟨declarations_kinded, body_typed assignment⟩

end Yulang.CommonEffectMixedWitness
