import YulangClosure.NativeContextTables

/-!
R304: operation payload retention in the existing native View constructors.

The input is the original NativeContextTables.ViewInput, and the output is
computed by Store.constructView / copyInput. No target map or output equation
is assumed. The operation copy input is derived from the published cell; the
two-copy run uses the original reserveCopy transition at both allocations.

Source owners: candidate_effect.rs::candidate_signature_view,
candidate_copy_effect_view, candidate_remapped_effect_view;
candidate_extrusion.rs::Work::EffectView and
candidate_scheme.rs::prepare_candidate_fresh_use effect_operands pass.

BOUNDARY: Rust operation_trace currently supplies no serialization into these
native tables, no retained view-remap events, and no tail semantic transport.
The theorem does not authenticate those missing inputs. It proves neither
R293 branch membership nor R159 admission. The exact missing certificate
equations and original consumer are recorded in the assignment handoff.
-/
namespace YulangClosure.SourceEffectRetentionR304

open NativeContextTables

/-- For a published operation view, the actual copyInput succeeds and keeps
the ordered content, owner, position and entire operation origin. Operation
views carry no annotation attachment. Only the explicitly supplied tail changes.
-/
theorem operation_copy_input (s : Store) (input : ViewInput)
    (origin : OperationOrigin) (operation : input.operation = some origin)
    (tail : Option Nat) :
    copyInput (s.constructView input) s.views.length tail =
      some { input with tail := tail, attachment := none } := by
  rw [copyInput, (construct_view_readback s input).1]
  simp [viewRecord, weightedDraft, reservedDraft, ViewInput.needsWeight, operation]

/-- Other successful native allocations may intervene before capture or a
later use. The original published operation cell, including birth identity,
survives the actual existing Run relation. -/
theorem operation_copy_input_after_run (s before : Store) (input : ViewInput)
    (origin : OperationOrigin) (operation : input.operation = some origin)
    (history : Run (s.constructView input) before) (tail : Option Nat) :
    copyInput before s.views.length tail =
      some { input with tail := tail, attachment := none } := by
  have found := (run_extends history).2.2.1 _ _ (construct_view_readback s input).1
  rw [copyInput, found]
  simp [viewRecord, weightedDraft, reservedDraft, ViewInput.needsWeight, operation]

/-- Direct native consumer application after any successful intervening run.
The source view and copied payload are computed from the constructor history;
the only remaining inputs are native idle/capacity and the independent tail. -/
theorem operation_copy_run_after_run (s before : Store) (input : ViewInput)
    (origin : OperationOrigin) (operation : input.operation = some origin)
    (history : Run (s.constructView input) before) (tail : Option Nat)
    (idle : before.pending = none) (fits : IndexFits before.views.length) :
    Run before (before.constructView { input with tail := tail, attachment := none }) := by
  apply construct_copy_run _ s.views.length tail _ idle
    (operation_copy_input_after_run s before input origin operation history tail) fits
  simp [ViewInput.needsWeight, operation]

/-- The fresh result cell is computed, including its original allocation birth.
No output record is supplied as a premise. -/
theorem operation_copy_readback (s : Store) (input : ViewInput)
    (origin : OperationOrigin) (operation : input.operation = some origin)
    (tail : Option Nat) :
    let before := s.constructView input
    let copied := { input with tail := tail, attachment := none }
    (before.constructView copied).views[before.views.length]? =
      some ⟨before.clock,
        { payload := ⟨input.allowed, tail, none, input.owner, input.position⟩,
          sourceWeight := none, origin := .operation origin }⟩ := by
  dsimp only
  rw [(construct_view_readback _ _).1]
  simp [viewRecord, weightedDraft, reservedDraft, ViewInput.needsWeight, operation]

/-- Applies the derived copy equation to the existing native transition
constructor. Capacity is still the original successful-allocation premise. -/
theorem operation_copy_run (s : Store) (input : ViewInput)
    (origin : OperationOrigin) (operation : input.operation = some origin)
    (tail : Option Nat)
    (fits : IndexFits (s.constructView input).views.length) :
    Run (s.constructView input)
      ((s.constructView input).constructView { input with tail := tail, attachment := none }) := by
  apply construct_copy_run _ s.views.length tail _
    (construct_view_readback s input).2.1
    (operation_copy_input s input origin operation tail) fits
  simp [ViewInput.needsWeight, operation]

/-- The actual two-copy path, suitable for an extrusion copy followed by one
FreshUse copy once their source trace is authenticated. The intermediate and
final tails are independent; no equality of distinct use rows is inferred. -/
theorem operation_two_copy_run (s : Store) (input : ViewInput)
    (origin : OperationOrigin) (operation : input.operation = some origin)
    (extrudedTail freshTail : Option Nat)
    (firstFits : IndexFits (s.constructView input).views.length)
    (secondFits : IndexFits ((s.constructView input).constructView
      { input with tail := extrudedTail, attachment := none }).views.length) :
    let emitted := s.constructView input
    let rewritten := emitted.constructView { input with tail := extrudedTail, attachment := none }
    let fresh := rewritten.constructView { input with tail := freshTail, attachment := none }
    Run emitted fresh ∧
      fresh.views[rewritten.views.length]? =
        some ⟨rewritten.clock,
          { payload := ⟨input.allowed, freshTail, none, input.owner, input.position⟩,
            sourceWeight := none, origin := .operation origin }⟩ := by
  dsimp only
  constructor
  · exact run_trans (operation_copy_run s input origin operation extrudedTail firstFits)
      (operation_copy_run (s.constructView input)
        { input with tail := extrudedTail, attachment := none }
        origin operation freshTail secondFits)
  · exact operation_copy_readback (s.constructView input)
      { input with tail := extrudedTail, attachment := none } origin operation freshTail

end YulangClosure.SourceEffectRetentionR304
