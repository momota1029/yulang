import Yulang.SignatureRequests

/-!
# Abortive error wrapping and conversion

`spec/05-effects.md` §5.7 fixes `wrap` as error-effect-to-result and `up`
as error-effect-to-error-effect conversion without resuming. A `Cases` value
describes the operations of an error declaration and their value constructors;
an `Encoding` describes the reverse value-to-operation direction. The response
types of those operations are empty. Unrelated operations remain freely typed.

The executable helpers use the existing signed capture test. `wrapFrom` handles
both the target error and the declared incoming error. Its fusion theorem is
valid for every request tree; it assumes only disjoint declaration keys and the
constructor/operation agreement, not an effect bound or successful inference.
Appending mapped case tables handles several directly declared `from` sources.
No nominal representation, transitive `from` search, or source elaboration is
chosen here.
-/

namespace Yulang.ErrorEffects

open Directed SignatureRequests

variable {Key Error Narrow Wide Value : Type} {n : Nat} {signature : Signature Key}

/-- Error constructors and their abortive operation signatures. Membership
proofs only select a declared constructor; they do not restrict computations. -/
structure Cases (signature : Signature Key) (Error : Type) where
  keys : List Key
  decode : (key : Key) → key ∈ keys → signature.Payload key → Error
  noResponse : (key : Key) → key ∈ keys → signature.Response key → Empty

/-- Every error value chooses its corresponding declared operation, and
converting that operation back into a value recovers the original error. -/
structure Encoding (cases : Cases signature Error) where
  operation : Error → Key
  payload : (error : Error) → signature.Payload (operation error)
  declared : ∀ error, operation error ∈ cases.keys
  decoded : ∀ error, cases.decode (operation error) (declared error) (payload error) = error

def wrap [DecidableEq Key] (cases : Cases signature Error) (action : Tree n signature Value) :
    Tree n signature (Except Error Value) :=
  Tree.shallowHandle cases.keys (fun value => .pure (.ok value))
    (fun occurrence captured payload _ =>
      .pure (.error (cases.decode occurrence.key captured.1 payload))) action

/-- The response is impossible. This request contains no original resumption
and requires no arbitrary inhabitant of the eventual result type. -/
def raise {cases : Cases signature Error} (encoding : Encoding cases) (error : Error) : Tree n signature Value :=
  .request (raw (encoding.operation error)) (encoding.payload error)
    (fun response => (cases.noResponse _ (encoding.declared error) response).elim)

def up [DecidableEq Key] (source : Cases signature Narrow)
    (target : Encoding (signature := signature) (Error := Wide) cases)
    (convert : Narrow → Wide) (action : Tree n signature Value) : Tree n signature Value :=
  Tree.shallowHandle source.keys Tree.pure
    (fun occurrence captured payload _ =>
      raise target (convert (source.decode occurrence.key captured.1 payload))) action

def Cases.map (convert : Narrow → Wide) (source : Cases signature Narrow) : Cases signature Wide where
  keys := source.keys
  decode := fun key member payload => convert (source.decode key member payload)
  noResponse := source.noResponse

/-- Composition of declaration tables. The language-facing fusion theorem
below requires disjoint source/target families, so it introduces no rule for
ambiguous or repeated `from` declarations. -/
def Cases.append [DecidableEq Key] (first last : Cases signature Error) : Cases signature Error where
  keys := first.keys ++ last.keys
  decode := fun key member payload =>
    if present : key ∈ first.keys then first.decode key present payload
    else last.decode key ((List.mem_append.mp member).resolve_left present) payload
  noResponse := fun key member response => False.elim ((List.mem_append.mp member).elim
    (fun present => (first.noResponse key present response).elim)
    (fun present => (last.noResponse key present response).elim))

def wrapFrom [DecidableEq Key] (target : Cases signature Wide) (source : Cases signature Narrow)
    (convert : Narrow → Wide) (action : Tree n signature Value) : Tree n signature (Except Wide Value) :=
  wrap (target.append (source.map convert)) action

@[simp] theorem wrap_pure [DecidableEq Key] (cases : Cases signature Error) (value : Value) :
    wrap (n := n) cases (.pure value) = .pure (.ok value) := rfl

theorem wrap_captured [DecidableEq Key] (cases : Cases signature Error)
    (occurrence : Occurrence n Key) (payload : signature.Payload occurrence.key)
    (resume : signature.Response occurrence.key → Tree n signature Value)
    (captured : Capturable cases.keys occurrence) :
    wrap cases (.request occurrence payload resume) =
      .pure (.error (cases.decode occurrence.key captured.1 payload)) := by
  simp [wrap, Tree.shallowHandle, captured]

theorem wrap_forwarded [DecidableEq Key] (cases : Cases signature Error)
    (occurrence : Occurrence n Key) (payload : signature.Payload occurrence.key)
    (resume : signature.Response occurrence.key → Tree n signature Value)
    (hidden : ¬ Capturable cases.keys occurrence) :
    wrap cases (.request occurrence payload resume) =
      .request occurrence payload (fun response => wrap cases (resume response)) := by
  simp [wrap, Tree.shallowHandle, hidden]

/-- Old positive guards and negative release debt both remain effective. -/
theorem wrap_nonzero [DecidableEq Key] (cases : Cases signature Error)
    (occurrence : Occurrence n Key) (payload : signature.Payload occurrence.key)
    (resume : signature.Response occurrence.key → Tree n signature Value)
    (scope : Fin n) (nonzero : occurrence.weights scope ≠ 0) :
    wrap cases (.request occurrence payload resume) =
      .request occurrence payload (fun response => wrap cases (resume response)) :=
  wrap_forwarded cases occurrence payload resume
    (Directed.nonzero_not_capturable cases.keys occurrence scope nonzero)

theorem wrap_uncaptured [DecidableEq Key] (cases : Cases signature Error)
    (action : Tree n signature Value)
    (hidden : Tree.AllRequests (fun occurrence => ¬ Capturable cases.keys occurrence) action) :
    wrap cases action = action.map Except.ok :=
  Tree.noncapture _ _ _ action hidden

theorem wrap_requests [DecidableEq Key] (cases : Cases signature Error)
    (predicate : Occurrence n Key → Prop) (action : Tree n signature Value)
    (holds : Tree.AllRequests predicate action) :
    Tree.AllRequests (fun occurrence => predicate occurrence ∧ ¬ Capturable cases.keys occurrence)
      (wrap cases action) := by
  induction action with
  | pure value => trivial
  | request occurrence payload resume ih =>
      by_cases captured : Capturable cases.keys occurrence
      · rw [wrap_captured cases occurrence payload resume captured]
        trivial
      · rw [wrap_forwarded cases occurrence payload resume captured]
        exact ⟨⟨holds.1, captured⟩, fun response => ih response (holds.2 response)⟩

theorem wrap_bounded [DecidableEq Key] (cases : Cases signature Error)
    (input : Row n Key) (action : Tree n signature Value) (bound : Tree.BoundedBy input action) :
    Tree.BoundedBy (residual cases.keys input) (wrap cases action) := by
  apply Tree.allRequests_mono _ _ ?_ _ (wrap_requests cases (fun occurrence => occurrence ∈ input) action bound)
  intro occurrence observed
  simpa [residual] using observed

/-- When every possible request is a visible error of this declaration,
the actual helper returns a result, for every input tree and result type. -/
theorem wrap_returns [DecidableEq Key] (cases : Cases signature Error)
    (action : Tree n signature Value)
    (closed : Tree.AllRequests (Capturable cases.keys) action) :
    ∃ result, wrap cases action = .pure result :=
  Tree.no_requests_pure _ (Tree.allRequests_mono _ _
    (fun _ contradiction => contradiction.2 contradiction.1) _ (wrap_requests cases _ action closed))

@[simp] theorem wrap_raise [DecidableEq Key] (cases : Cases signature Error)
    (encoding : Encoding cases) (error : Error) :
    wrap cases (raise (n := n) (Value := Value) encoding error) = .pure (.error error) := by
  simp [wrap, raise, Tree.shallowHandle, Capturable, raw, encoding.declared, encoding.decoded]

/-- Sequencing cannot reach code after a typed abortive request. -/
theorem raise_bind {Result : Type} (cases : Cases signature Error) (encoding : Encoding cases)
    (error : Error) (next : Value → Tree n signature Result) :
    (raise encoding error).bind next = raise encoding error := by
  simp only [raise, raw, Tree.bind]
  congr 1
  funext response
  exact (cases.noResponse _ (encoding.declared error) response).elim

@[simp] theorem up_pure [DecidableEq Key] (source : Cases signature Narrow)
    (target : Encoding (signature := signature) (Error := Wide) cases)
    (convert : Narrow → Wide) (value : Value) :
    up source target convert (n := n) (.pure value) = .pure value := rfl

theorem up_captured [DecidableEq Key] (source : Cases signature Narrow)
    (target : Encoding (signature := signature) (Error := Wide) cases) (convert : Narrow → Wide)
    (occurrence : Occurrence n Key) (payload : signature.Payload occurrence.key)
    (resume : signature.Response occurrence.key → Tree n signature Value)
    (captured : Capturable source.keys occurrence) :
    up source target convert (.request occurrence payload resume) =
      raise target (convert (source.decode occurrence.key captured.1 payload)) := by
  simp [up, Tree.shallowHandle, captured]

@[simp] theorem up_raise [DecidableEq Key] (source : Cases signature Narrow)
    (sourceEncoding : Encoding source)
    (target : Encoding (signature := signature) (Error := Wide) cases)
    (convert : Narrow → Wide) (error : Narrow) :
    up source target convert (raise (n := n) (Value := Value) sourceEncoding error) =
      raise target (convert error) := by
  exact (up_captured (Value := Value) source target convert
    (raw (n := n) (sourceEncoding.operation error)) (sourceEncoding.payload error)
    (fun response => (source.noResponse _ (sourceEncoding.declared error) response).elim)
    ⟨sourceEncoding.declared error, fun _ => rfl⟩).trans
      (congrArg (fun value => raise target (convert value)) (sourceEncoding.decoded error))

theorem up_forwarded [DecidableEq Key] (source : Cases signature Narrow)
    (target : Encoding (signature := signature) (Error := Wide) cases) (convert : Narrow → Wide)
    (occurrence : Occurrence n Key) (payload : signature.Payload occurrence.key)
    (resume : signature.Response occurrence.key → Tree n signature Value)
    (hidden : ¬ Capturable source.keys occurrence) :
    up source target convert (.request occurrence payload resume) =
      .request occurrence payload (fun response => up source target convert (resume response)) := by
  simp [up, Tree.shallowHandle, hidden]

theorem up_nonzero [DecidableEq Key] (source : Cases signature Narrow)
    (target : Encoding (signature := signature) (Error := Wide) cases) (convert : Narrow → Wide)
    (occurrence : Occurrence n Key) (payload : signature.Payload occurrence.key)
    (resume : signature.Response occurrence.key → Tree n signature Value)
    (scope : Fin n) (nonzero : occurrence.weights scope ≠ 0) :
    up source target convert (.request occurrence payload resume) =
      .request occurrence payload (fun response => up source target convert (resume response)) :=
  up_forwarded source target convert occurrence payload resume
    (Directed.nonzero_not_capturable source.keys occurrence scope nonzero)

theorem raise_bounded (cases : Cases signature Error) (encoding : Encoding cases) (error : Error) :
    Tree.BoundedBy (cases.keys.map (raw (n := n))) (raise (Value := Value) encoding error) := by
  refine ⟨List.mem_map.mpr ⟨encoding.operation error, encoding.declared error, rfl⟩, ?_⟩
  intro response
  exact (cases.noResponse _ (encoding.declared error) response).elim

theorem up_bounded [DecidableEq Key] (source : Cases signature Narrow)
    (targetCases : Cases signature Wide) (target : Encoding targetCases) (convert : Narrow → Wide)
    (input : Row n Key) (action : Tree n signature Value) (bound : Tree.BoundedBy input action) :
    Tree.BoundedBy (residual source.keys input ++ targetCases.keys.map raw)
      (up source target convert action) := by
  exact Tree.shallowHandle_bounded source.keys input (targetCases.keys.map raw)
    Tree.pure (fun occurrence captured payload _ =>
      raise target (convert (source.decode occurrence.key captured.1 payload)))
    (fun _ => trivial) (fun _ _ _ _ _ => raise_bounded targetCases target _) action bound

theorem wrapFrom_target [DecidableEq Key] (target : Cases signature Wide)
    (source : Cases signature Narrow) (convert : Narrow → Wide)
    (occurrence : Occurrence n Key) (payload : signature.Payload occurrence.key)
    (resume : signature.Response occurrence.key → Tree n signature Value)
    (captured : Capturable target.keys occurrence) :
    wrapFrom target source convert (.request occurrence payload resume) =
      .pure (.error (target.decode occurrence.key captured.1 payload)) := by
  have combined : Capturable (target.append (source.map convert)).keys occurrence :=
    ⟨List.mem_append.mpr (Or.inl captured.1), captured.2⟩
  rw [wrapFrom, wrap_captured _ _ _ _ combined]
  simp [Cases.append, captured.1]

theorem wrapFrom_source [DecidableEq Key] (target : Cases signature Wide)
    (source : Cases signature Narrow) (convert : Narrow → Wide)
    (occurrence : Occurrence n Key) (payload : signature.Payload occurrence.key)
    (resume : signature.Response occurrence.key → Tree n signature Value)
    (absent : occurrence.key ∉ target.keys) (captured : Capturable source.keys occurrence) :
    wrapFrom target source convert (.request occurrence payload resume) =
      .pure (.error (convert (source.decode occurrence.key captured.1 payload))) := by
  have combined : Capturable (target.append (source.map convert)).keys occurrence :=
    ⟨List.mem_append.mpr (Or.inr captured.1), captured.2⟩
  rw [wrapFrom, wrap_captured _ _ _ _ combined]
  simp [Cases.append, Cases.map, absent]

/-- Direct wrapping of the target and its declared `from` source is exactly
conversion followed by target wrapping, including all unrelated/protected
requests and every original shared continuation. -/
theorem wrap_up_exact [DecidableEq Key] (source : Cases signature Narrow)
    (targetCases : Cases signature Wide) (target : Encoding targetCases) (convert : Narrow → Wide)
    (apart : ∀ key, key ∈ targetCases.keys → key ∈ source.keys → False)
    (action : Tree n signature Value) :
    wrap targetCases (up source target convert action) = wrapFrom targetCases source convert action := by
  induction action with
  | pure value => rfl
  | request occurrence payload resume ih =>
      by_cases sourceCaptured : Capturable source.keys occurrence
      · rw [up_captured _ _ _ _ _ _ sourceCaptured, wrap_raise,
          wrapFrom_source _ _ _ _ _ _
            (fun member => apart _ member sourceCaptured.1) sourceCaptured]
      · rw [up_forwarded _ _ _ _ _ _ sourceCaptured]
        by_cases targetCaptured : Capturable targetCases.keys occurrence
        · rw [wrap_captured _ _ _ _ targetCaptured,
            wrapFrom_target _ _ _ _ _ _ targetCaptured]
        · have hidden : ¬ Capturable (targetCases.append (source.map convert)).keys occurrence := by
            rintro ⟨member, zero⟩
            rcases List.mem_append.mp member with member | member
            · exact targetCaptured ⟨member, zero⟩
            · exact sourceCaptured ⟨member, zero⟩
          rw [wrap_forwarded _ _ _ _ targetCaptured, wrapFrom, wrap_forwarded _ _ _ _ hidden]
          exact congrArg (Tree.request occurrence payload) (funext ih)

end Yulang.ErrorEffects
