import Yulang.OperationalTransport

/-!
# Checked types are preserved by higher-order boundary wrappers

The runtime wrappers from `OperationalTransport` act on the same computation
arguments and returned closures as `OperationalTyping.eval`. This module maps
every immediate and latent row of a checked type by the same signed request
action and proves exact preservation of its operational logical relation.

The static action has one direction throughout the type. At function types,
the runtime wrapper reverses direction on the argument, so a computation with
the transported input type is converted back to the original input interface.
This is not an extra contravariant action on the type's input row.

Checker success therefore bounds the explicitly wrapped evaluation, including
later calls through returned or stored callbacks. No action/arm bound or origin
condition is a premise. As with the checker, shapes and lambda input types are
already resolved. The source pass choosing boundary locations and permissions,
and zero-origin obligations for noncapture, are separate from this theorem.
The existing immediate-only `Expr.boundary` constructor is unchanged.
-/

namespace Yulang.OperationalTransportTyping

open Directed OperationalTyping
open OperationalTransport (Direction request value tree)

def row (scope : Fin n) (permission : Key → Bool) (direction : Direction)
    (original : Row n Key) : Row n Key :=
  original.map (request scope permission direction)

/-- A boundary has the same static action at all latent row positions. -/
def vtype (scope : Fin n) (permission : Key → Bool) (direction : Direction) :
    {shape : Shape} → VTy n Key shape → VTy n Key shape
  | _, .atom => .atom
  | _, .pair left right =>
      .pair (vtype scope permission direction left) (vtype scope permission direction right)
  | _, .arrow input inputRow output outputRow =>
      .arrow (vtype scope permission direction input) (row scope permission direction inputRow)
        (vtype scope permission direction output) (row scope permission direction outputRow)

def ctype (scope : Fin n) (permission : Key → Bool) (direction : Direction)
    (original : CTy n Key shape) : CTy n Key shape :=
  ⟨vtype scope permission direction original.value, row scope permission direction original.row⟩

@[simp] theorem row_opposite (scope : Fin n) (permission : Key → Bool)
    (direction : Direction) (original : Row n Key) :
    row scope permission direction.opposite (row scope permission direction original) =
      original := by
  simp only [row, List.map_map]
  apply List.map_id''
  exact OperationalTransport.request_opposite scope permission direction

@[simp] theorem vtype_opposite (scope : Fin n) (permission : Key → Bool)
    (direction : Direction) (original : VTy n Key shape) :
    vtype scope permission direction.opposite (vtype scope permission direction original) =
      original := by
  induction original with
  | atom => rfl
  | pair left right ihl ihr => simp only [vtype, ihl, ihr]
  | arrow input inputRow output outputRow ihi iho =>
      simp only [vtype, ihi, iho, row_opposite]

@[simp] theorem ctype_opposite (scope : Fin n) (permission : Key → Bool)
    (direction : Direction) (original : CTy n Key shape) :
    ctype scope permission direction.opposite (ctype scope permission direction original) =
      original := by
  cases original
  simp only [ctype, vtype_opposite, row_opposite]

theorem request_injective (scope : Fin n) (permission : Key → Bool)
    (direction : Direction) : Function.Injective (request scope permission direction) := by
  intro left right equal
  have restored := congrArg (request scope permission direction.opposite) equal
  simpa only [OperationalTransport.request_opposite] using restored

@[simp] theorem request_mem_row_iff (scope : Fin n) (permission : Key → Bool)
    (direction : Direction) (occurrence : Occurrence n Key) (original : Row n Key) :
    request scope permission direction occurrence ∈ row scope permission direction original ↔
      occurrence ∈ original := by
  constructor
  · intro member
    obtain ⟨old, present, equal⟩ := List.mem_map.mp member
    have restored := request_injective scope permission direction equal
    exact restored ▸ present
  · intro member
    exact List.mem_map.mpr ⟨occurrence, member, rfl⟩

theorem rowLe_iff (scope : Fin n) (permission : Key → Bool) (direction : Direction)
    (left right : Row n Key) :
    RowLe (row scope permission direction left) (row scope permission direction right) ↔
      RowLe left right := by
  constructor
  · intro included occurrence member
    exact (request_mem_row_iff scope permission direction occurrence right).mp
      (included _ ((request_mem_row_iff scope permission direction occurrence left).mpr member))
  · intro included occurrence member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    exact (request_mem_row_iff scope permission direction old right).mpr (included old present)

theorem vLe_iff (scope : Fin n) (permission : Key → Bool) (direction : Direction)
    (left right : VTy n Key shape) :
    VLe (vtype scope permission direction left) (vtype scope permission direction right) ↔
      VLe left right := by
  induction shape with
  | atom => cases left; cases right; rfl
  | pair a b iha ihb =>
      cases left
      cases right
      simp only [vtype, VLe, iha, ihb]
  | arrow a b iha ihb =>
      cases left
      cases right
      simp only [vtype, VLe, iha, ihb, rowLe_iff]

theorem cLe_iff (scope : Fin n) (permission : Key → Bool) (direction : Direction)
    (left right : CTy n Key shape) :
    CLe (ctype scope permission direction left) (ctype scope permission direction right) ↔
      CLe left right := by
  simp only [CLe, ctype, vLe_iff, rowLe_iff]

theorem tree_bounded_iff (scope : Fin n) (permission : Key → Bool) (direction : Direction)
    (original : Row n Key) (computation : Tree n Key Atom shape) :
    Computation.BoundedBy (row scope permission direction original)
      (tree scope permission shape direction computation) ↔
        Computation.BoundedBy original computation := by
  rw [Computation.BoundedBy, tree, OperationalTransport.allRequests_mapBoth]
  simp only [request_mem_row_iff]
  rfl

private theorem allReturns_tree_iff (scope : Fin n) (permission : Key → Bool)
    (direction : Direction) (source target : Value n Key Atom shape → Prop)
    (values : ∀ original, target (value scope permission shape direction original) ↔ source original)
    (computation : Tree n Key Atom shape) :
    AllReturns target (tree scope permission shape direction computation) ↔
      AllReturns source computation := by
  rw [tree, OperationalTransport.allReturns_mapBoth]
  have equal : (fun original => target (value scope permission shape direction original)) =
      source := funext (fun original => propext (values original))
  rw [equal]

private theorem valid_tree_iff_of_value (scope : Fin n) (permission : Key → Bool)
    (direction : Direction) (type : CTy n Key shape)
    (values : ∀ original : Value n Key Atom shape,
      ValidValue (vtype scope permission direction type.value)
        (value scope permission shape direction original) ↔ ValidValue type.value original)
    (computation : Tree n Key Atom shape) :
    Valid (ctype scope permission direction type)
      (tree scope permission shape direction computation) ↔ Valid type computation :=
  and_congr (tree_bounded_iff scope permission direction type.row computation)
    (allReturns_tree_iff scope permission direction _ _ values computation)

/-- Exact logical-relation transport includes arbitrary higher-order functions,
with suspended effectful arguments. No origin condition is needed for validity. -/
theorem validValue_iff (scope : Fin n) (permission : Key → Bool)
    (type : VTy n Key shape) (direction : Direction) (original : Value n Key Atom shape) :
    ValidValue (vtype scope permission direction type)
      (value scope permission shape direction original) ↔ ValidValue type original := by
  induction shape generalizing direction with
  | atom => cases type; rfl
  | pair a b iha ihb =>
      cases type with
      | pair left right =>
          exact and_congr (iha left direction original.1) (ihb right direction original.2)
  | arrow a b iha ihb =>
      cases type with
      | arrow input inputRow output outputRow =>
          have inputExact (computation : Tree n Key Atom a) :
              Valid (ctype scope permission direction (⟨input, inputRow⟩ : CTy n Key a))
                (tree scope permission a direction computation) ↔
                  Valid (⟨input, inputRow⟩ : CTy n Key a) computation :=
            valid_tree_iff_of_value scope permission direction _ (iha input direction) computation
          have outputExact (computation : Tree n Key Atom b) :
              Valid (ctype scope permission direction (⟨output, outputRow⟩ : CTy n Key b))
                (tree scope permission b direction computation) ↔
                  Valid (⟨output, outputRow⟩ : CTy n Key b) computation :=
            valid_tree_iff_of_value scope permission direction _ (ihb output direction) computation
          constructor
          · intro transformed argument bounded returned
            have good := (inputExact argument).mpr ⟨bounded, returned⟩
            have called := transformed (tree scope permission a direction argument) good.1 good.2
            rw [OperationalTransport.value_apply_tree] at called
            exact (outputExact (original argument)).mp called
          · intro untransformed argument bounded returned
            have good : Valid (⟨input, inputRow⟩ : CTy n Key a)
                (tree scope permission a direction.opposite argument) := by
              apply (inputExact _).mp
              have restored := OperationalTransport.tree_opposite scope permission a
                direction.opposite argument
              simp only [HigherOrder.Direction.opposite_opposite] at restored
              rw [restored]
              exact ⟨bounded, returned⟩
            exact (outputExact _).mpr (untransformed _ good.1 good.2)

/-- Both immediate effects and every latent callback keep exactly their
transported checked interface. -/
theorem valid_iff (scope : Fin n) (permission : Key → Bool) (direction : Direction)
    (type : CTy n Key shape) (computation : Tree n Key Atom shape) :
    Valid (ctype scope permission direction type)
      (tree scope permission shape direction computation) ↔ Valid type computation :=
  valid_tree_iff_of_value scope permission direction type
    (validValue_iff scope permission type.value direction) computation

/-- The original executable checker supplies every operational premise; the
wrapper may be applied to an open computation with a valid external interface. -/
theorem inferred_transport_valid [DecidableEq Key]
    (expression : Expr n Key Atom Γ shape) (types : Env (CTy n Key) Γ)
    (output : CTy n Key shape) (accepted : infer types expression = some output)
    (runtime : Env (Tree n Key Atom) Γ) (environment : EnvValid types runtime)
    (scope : Fin n) (permission : Key → Bool) (direction : Direction) :
    Valid (ctype scope permission direction output)
      (tree scope permission shape direction (eval runtime expression)) :=
  (valid_iff scope permission direction output _).mpr
    (inferred_operationally_valid expression types output accepted runtime environment)

/-- Closed checker acceptance alone establishes the boundary-transformed
interface, including all subsequent calls allowed by its latent function types. -/
theorem closed_inferred_transport_valid [DecidableEq Key]
    (expression : Expr n Key Atom [] shape) (output : CTy n Key shape)
    (accepted : infer Env.nil expression = some output)
    (scope : Fin n) (permission : Key → Bool) (direction : Direction) :
    Valid (ctype scope permission direction output)
      (tree scope permission shape direction (eval Env.nil expression)) :=
  inferred_transport_valid expression Env.nil output accepted Env.nil
    (fun index => nomatch index) scope permission direction

end Yulang.OperationalTransportTyping
