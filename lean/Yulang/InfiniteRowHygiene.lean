import Yulang.RecursiveRows
import Yulang.FreshRowInference

/-!
# Hygiene of arbitrary signed rows and recursive least solutions

Rows here are exactly `RecursiveRows.SetRow`, with the existing signed set
algebra. Neither an occurrence set nor an incoming row assignment is required
to be finite. Protection and matching release are mutually inverse row maps;
handler subtraction still removes only matching zero-weight occurrences.

Scope embeddings commute with every row constructor and with the least solution
of a recursive lower-bound problem. A new coordinate therefore supplies zero
origin even for an infinite inferred tail containing old positive or negative
weights. Operational bounds use the existing `Computation.AllRequests` predicate
over the same row sets and cover every response branch of the same request tree.

These results do not assume or construct a decision procedure for infinite-row
membership. They do not insert source-level boundaries or transform latent
closures inside returned values, payloads, or responses.
-/

namespace Yulang.InfiniteRowHygiene

open Directed
open RecursiveRows (SetRow algebra ofList)
open RowInference (RowExpr)

abbrev Included (left right : SetRow n Key) : Prop := (algebra n Key).le left right
abbrev emptyRow : SetRow n Key := (algebra n Key).empty
abbrev joinRow (left right : SetRow n Key) : SetRow n Key := (algebra n Key).join left right
abbrev protectRow (scope : Fin n) (permission : Permission Key) (row : SetRow n Key) : SetRow n Key :=
  (algebra n Key).protect scope permission row
abbrev releaseRow (scope : Fin n) (permission : Permission Key) (row : SetRow n Key) : SetRow n Key :=
  (algebra n Key).release scope permission row
abbrev residualRow (handled : List Key) (row : SetRow n Key) : SetRow n Key :=
  (algebra n Key).residual handled row

/-- An image of a possibly infinite occurrence set, with no enumeration. -/
def image (transform : Occurrence n Key → Occurrence m Other) (row : SetRow n Key) : SetRow m Other :=
  fun occurrence => ∃ original, row original ∧ transform original = occurrence

theorem image_identity (row : SetRow n Key) : image id row = row := by
  funext occurrence
  apply propext
  constructor
  · rintro ⟨original, member, equal⟩
    exact equal ▸ member
  · intro member
    exact ⟨occurrence, member, rfl⟩

theorem image_comp (first : Occurrence n Key → Occurrence m Middle)
    (second : Occurrence m Middle → Occurrence k Other) (row : SetRow n Key) :
    image second (image first row) = image (second ∘ first) row := by
  funext occurrence
  apply propext
  constructor
  · rintro ⟨middle, ⟨original, member, rfl⟩, rfl⟩
    exact ⟨original, member, rfl⟩
  · rintro ⟨original, member, rfl⟩
    exact ⟨first original, ⟨original, member, rfl⟩, rfl⟩

theorem image_inverse (first : Occurrence n Key → Occurrence m Other)
    (second : Occurrence m Other → Occurrence n Key)
    (inverse : ∀ occurrence, second (first occurrence) = occurrence) (row : SetRow n Key) :
    image second (image first row) = row := by
  rw [image_comp]
  have identity : second ∘ first = id := funext inverse
  rw [identity, image_identity]

theorem image_mono (transform : Occurrence n Key → Occurrence m Other)
    (left right : SetRow n Key) (included : Included left right) :
    Included (image transform left) (image transform right) := by
  rintro occurrence ⟨original, member, equal⟩
  exact ⟨original, included original member, equal⟩

theorem image_apply_iff (transform : Occurrence n Key → Occurrence m Other)
    (injective : Function.Injective transform) (row : SetRow n Key) (occurrence : Occurrence n Key) :
    image transform row (transform occurrence) ↔ row occurrence := by
  constructor
  · rintro ⟨original, member, equal⟩
    exact (injective equal) ▸ member
  · intro member
    exact ⟨occurrence, member, rfl⟩

theorem image_included_iff (transform : Occurrence n Key → Occurrence m Other)
    (injective : Function.Injective transform) (left right : SetRow n Key) :
    Included (image transform left) (image transform right) ↔ Included left right := by
  constructor
  · intro included occurrence member
    exact (image_apply_iff transform injective right occurrence).mp
      (included (transform occurrence) ⟨occurrence, member, rfl⟩)
  · exact image_mono transform left right

theorem image_empty (transform : Occurrence n Key → Occurrence m Other) :
    image transform emptyRow = emptyRow := by
  funext occurrence
  apply propext
  constructor
  · rintro ⟨_, impossible, _⟩
    exact impossible
  · intro impossible
    exact False.elim impossible

theorem image_join (transform : Occurrence n Key → Occurrence m Other)
    (left right : SetRow n Key) :
    image transform (joinRow left right) = joinRow (image transform left) (image transform right) := by
  funext occurrence
  apply propext
  constructor
  · rintro ⟨original, member, equal⟩
    exact member.elim (fun h => Or.inl ⟨original, h, equal⟩) (fun h => Or.inr ⟨original, h, equal⟩)
  · intro member
    rcases member with ⟨original, h, equal⟩ | ⟨original, h, equal⟩
    · exact ⟨original, Or.inl h, equal⟩
    · exact ⟨original, Or.inr h, equal⟩

theorem image_ofList (transform : Occurrence n Key → Occurrence m Other) (row : Directed.Row n Key) :
    image transform (ofList row) = ofList (row.map transform) := by
  funext occurrence
  apply propext
  exact List.mem_map.symm

/-- Both signed cancellation orders hold for every row, finite or infinite. -/
theorem release_protect (scope : Fin n) (permission : Permission Key) (row : SetRow n Key) :
    releaseRow scope permission (protectRow scope permission row) = row :=
  image_inverse _ _ (Directed.release_protect scope permission) row

theorem protect_release (scope : Fin n) (permission : Permission Key) (row : SetRow n Key) :
    protectRow scope permission (releaseRow scope permission row) = row :=
  image_inverse _ _ (Directed.protect_release scope permission) row

theorem protect_injective (scope : Fin n) (permission : Permission Key) :
    Function.Injective (Directed.protect scope permission) := by
  intro left right equal
  have restored := congrArg (Directed.release scope permission) equal
  simpa only [Directed.release_protect] using restored

theorem release_injective (scope : Fin n) (permission : Permission Key) :
    Function.Injective (Directed.release scope permission) := by
  intro left right equal
  have restored := congrArg (Directed.protect scope permission) equal
  simpa only [Directed.protect_release] using restored

theorem protect_included_iff (scope : Fin n) (permission : Permission Key) (left right : SetRow n Key) :
    Included (protectRow scope permission left) (protectRow scope permission right) ↔ Included left right :=
  image_included_iff _ (protect_injective scope permission) left right

theorem release_included_iff (scope : Fin n) (permission : Permission Key) (left right : SetRow n Key) :
    Included (releaseRow scope permission left) (releaseRow scope permission right) ↔ Included left right :=
  image_included_iff _ (release_injective scope permission) left right

/-- A glob mask adds no shift and does not remove old signed weights. -/
theorem glob_protect (scope : Fin n) (row : SetRow n Key) : protectRow scope allowAll row = row := by
  change image (Directed.protect scope allowAll) row = row
  have identity : Directed.protect scope allowAll = (id : Occurrence n Key → Occurrence n Key) :=
    funext (glob_has_no_transport scope 1)
  rw [identity, image_identity]

theorem glob_release (scope : Fin n) (row : SetRow n Key) : releaseRow scope allowAll row = row := by
  change image (Directed.release scope allowAll) row = row
  have identity : Directed.release scope allowAll = (id : Occurrence n Key → Occurrence n Key) :=
    funext (glob_has_no_transport scope (-1))
  rw [identity, image_identity]

theorem residual_mono (handled : List Key) (left right : SetRow n Key) (included : Included left right) :
    Included (residualRow handled left) (residualRow handled right) :=
  fun occurrence member => ⟨included occurrence member.1, member.2⟩

/-- The residual is exactly the greatest uncapturable subset of the input. -/
theorem residual_greatest (handled : List Key) (input candidate : SetRow n Key) :
    Included candidate (residualRow handled input) ↔
      Included candidate input ∧ ∀ occurrence, candidate occurrence → ¬ Capturable handled occurrence := by
  constructor
  · intro included
    exact ⟨fun occurrence member => (included occurrence member).1,
      fun occurrence member => (included occurrence member).2⟩
  · rintro ⟨included, blocked⟩ occurrence member
    exact ⟨included occurrence member, blocked occurrence member⟩

theorem residual_image (transform : Occurrence n Key → Occurrence m Other)
    (handled : List Other) (originalHandled : List Key)
    (capture : ∀ occurrence, Capturable handled (transform occurrence) ↔
      Capturable originalHandled occurrence) (row : SetRow n Key) :
    residualRow handled (image transform row) = image transform (residualRow originalHandled row) := by
  funext occurrence
  apply propext
  constructor
  · rintro ⟨⟨original, member, rfl⟩, blocked⟩
    exact ⟨original, ⟨member, fun visible => blocked ((capture original).mpr visible)⟩, rfl⟩
  · rintro ⟨original, ⟨member, blocked⟩, rfl⟩
    exact ⟨⟨original, member, rfl⟩, fun visible => blocked ((capture original).mp visible)⟩

theorem residual_ofList [DecidableEq Key] (handled : List Key) (row : Directed.Row n Key) :
    residualRow handled (ofList row) = ofList (Directed.residual handled row) := by
  funext occurrence
  apply propext
  simp [residualRow, algebra, ofList, Directed.residual]

/-! ## Scope embeddings preserve the complete inferred set-row algebra -/

def reindexRow (embedding : Fin n → Fin m) (row : SetRow n Key) : SetRow m Key :=
  image (FreshBoundaries.reindex embedding) row

theorem reindex_recover (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (row : SetRow n Key) :
    image (FreshBoundaries.restrict embedding) (reindexRow embedding row) = row :=
  image_inverse _ _ (FreshBoundaries.restrict_reindex embedding injective) row

theorem reindex_included_iff (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (left right : SetRow n Key) :
    Included (reindexRow embedding left) (reindexRow embedding right) ↔ Included left right :=
  image_included_iff _ (FreshBoundaries.reindex_injective embedding injective) left right

theorem reindex_protect (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (scope : Fin n) (permission : Permission Key) (row : SetRow n Key) :
    reindexRow embedding (protectRow scope permission row) =
      protectRow (embedding scope) permission (reindexRow embedding row) := by
  change image _ (image _ row) = image _ (image _ row)
  rw [image_comp, image_comp]
  apply congrArg (fun transform => image transform row)
  funext occurrence
  exact FreshBoundaries.reindex_protect embedding injective scope permission occurrence

theorem reindex_release (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (scope : Fin n) (permission : Permission Key) (row : SetRow n Key) :
    reindexRow embedding (releaseRow scope permission row) =
      releaseRow (embedding scope) permission (reindexRow embedding row) := by
  change image _ (image _ row) = image _ (image _ row)
  rw [image_comp, image_comp]
  apply congrArg (fun transform => image transform row)
  funext occurrence
  exact FreshBoundaries.reindex_release embedding injective scope permission occurrence

theorem reindex_residual (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (handled : List Key) (row : SetRow n Key) :
    residualRow handled (reindexRow embedding row) = reindexRow embedding (residualRow handled row) :=
  residual_image _ handled handled (FreshBoundaries.capturable_reindex_iff embedding injective handled) row

theorem reindex_head (embedding : Fin n → Fin m) (key : Key) :
    reindexRow embedding ((algebra n Key).head key) = (algebra m Key).head key := by
  funext occurrence
  apply propext
  constructor
  · rintro ⟨original, member, equal⟩
    change original = raw key at member
    subst original
    exact equal.symm.trans (FreshRowInference.reindex_raw embedding key)
  · intro member
    change occurrence = raw key at member
    exact ⟨raw key, rfl, (FreshRowInference.reindex_raw embedding key).trans member.symm⟩

/-- Arbitrary substituted tails may already be infinite; every existing row
constructor still commutes with an injective change of boundary coordinates. -/
theorem eval_mapScopes (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (row : RowExpr Key (Fin n) Slot) (rows : Slot → SetRow n Key) :
    (FreshRowInference.mapScopes embedding row).eval (algebra m Key)
      (fun slot => reindexRow embedding (rows slot)) =
        reindexRow embedding (row.eval (algebra n Key) rows) := by
  induction row with
  | empty => exact (image_empty _).symm
  | head key => exact (reindex_head embedding key).symm
  | var _ => rfl
  | union left right ihLeft ihRight =>
      change joinRow _ _ = reindexRow embedding (joinRow _ _)
      rw [ihLeft, ihRight]
      exact (image_join _ _ _).symm
  | protect scope permission row ih =>
      change protectRow (embedding scope) permission _ = reindexRow embedding (protectRow scope permission _)
      rw [ih]
      exact (reindex_protect embedding injective scope permission (row.eval (algebra n Key) rows)).symm
  | release scope permission row ih =>
      change releaseRow (embedding scope) permission _ = reindexRow embedding (releaseRow scope permission _)
      rw [ih]
      exact (reindex_release embedding injective scope permission (row.eval (algebra n Key) rows)).symm
  | residual handled row ih =>
      change residualRow handled _ = reindexRow embedding (residualRow handled _)
      rw [ih]
      exact reindex_residual embedding injective handled (row.eval (algebra n Key) rows)

/-- Keep every rule and slot; only its boundary coordinates change. -/
def reindexRule (embedding : Fin n → Fin m) (rule : RecursiveRows.Rule n Key Slot) :
    RecursiveRows.Rule m Key Slot :=
  ⟨rule.target, FreshRowInference.mapScopes embedding rule.lower⟩

def reindexProblem (embedding : Fin n → Fin m) (problem : RecursiveRows.Problem n Key Slot) :
    RecursiveRows.Problem m Key Slot := problem.map (reindexRule embedding)

theorem derives_reindex (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (problem : RecursiveRows.Problem n Key Slot) (slot : Slot) (occurrence : Occurrence n Key)
    (derived : RecursiveRows.Derives problem slot occurrence) :
    RecursiveRows.Derives (reindexProblem embedding problem) slot (FreshBoundaries.reindex embedding occurrence) := by
  exact RecursiveRows.Derives.rec
    (motive_1 := fun slot occurrence _ => RecursiveRows.Derives (reindexProblem embedding problem)
      slot (FreshBoundaries.reindex embedding occurrence))
    (motive_2 := fun row occurrence _ => RecursiveRows.ExprDerives (reindexProblem embedding problem)
      (FreshRowInference.mapScopes embedding row) (FreshBoundaries.reindex embedding occurrence))
    (fun member _ ih => .rule (List.mem_map.mpr ⟨_, member, rfl⟩) ih)
    (fun key => by simpa only [FreshRowInference.mapScopes, FreshRowInference.reindex_raw] using
      RecursiveRows.ExprDerives.head (problem := reindexProblem embedding problem) key)
    (fun _ ih => .var ih)
    (fun _ ih => .left ih)
    (fun _ ih => .right ih)
    (fun _ ih => by
      rw [FreshBoundaries.reindex_protect embedding injective]
      exact .protect ih)
    (fun _ ih => by
      rw [FreshBoundaries.reindex_release embedding injective]
      exact .release ih)
    (fun _ blocked ih => .residual ih (fun capture =>
      blocked ((FreshBoundaries.capturable_reindex_iff embedding injective _ _).mp capture)))
    derived

theorem reindexed_model (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (problem : RecursiveRows.Problem n Key Slot) (rows : Slot → SetRow n Key)
    (model : RecursiveRows.Models problem rows) :
    RecursiveRows.Models (reindexProblem embedding problem) (fun slot => reindexRow embedding (rows slot)) := by
  intro rule member occurrence fact
  obtain ⟨originalRule, originalMember, rfl⟩ := List.mem_map.mp member
  change (FreshRowInference.mapScopes embedding originalRule.lower).eval (algebra m Key)
    (fun slot => reindexRow embedding (rows slot)) occurrence at fact
  rw [eval_mapScopes embedding injective] at fact
  obtain ⟨original, originalFact, equal⟩ := fact
  exact ⟨original, model originalRule originalMember original originalFact, equal⟩

/-- The entire recursive least solution is preserved, including infinitely
many different weights. No new target-coordinate occurrences are introduced. -/
theorem least_reindex (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (problem : RecursiveRows.Problem n Key Slot) (slot : Slot) :
    RecursiveRows.Derives (reindexProblem embedding problem) slot =
      reindexRow embedding (RecursiveRows.Derives problem slot) := by
  funext occurrence
  apply propext
  constructor
  · exact RecursiveRows.least_below _ _
      (reindexed_model embedding injective problem _ (RecursiveRows.least_models problem)) slot occurrence
  · rintro ⟨original, derived, rfl⟩
    exact derives_reindex embedding injective problem slot original derived

/-! ## A fresh boundary, without a restriction on old signed weights -/

abbrev liftRow (row : SetRow n Key) : SetRow (n + 1) Key := reindexRow Fin.succ row

def ZeroAt (scope : Fin n) (row : SetRow n Key) : Prop :=
  ∀ occurrence, row occurrence → occurrence.weights scope = 0

theorem liftRow_zero (row : SetRow n Key) : ZeroAt FreshBoundaries.fresh (liftRow row) := by
  rintro occurrence ⟨original, _, rfl⟩
  exact FreshBoundaries.liftOccurrence_fresh original

theorem least_fresh_zero (problem : RecursiveRows.Problem n Key Slot) (slot : Slot) :
    ZeroAt FreshBoundaries.fresh (RecursiveRows.Derives (reindexProblem Fin.succ problem) slot) := by
  rw [least_reindex Fin.succ FreshBoundaries.succ_injective]
  exact liftRow_zero _

theorem default_protect_noncapturable (handled : List Key) (scope : Fin n)
    (row : SetRow n Key) (origin : ZeroAt scope row) (occurrence : Occurrence n Key)
    (member : protectRow scope allowNone row occurrence) : ¬ Capturable handled occurrence := by
  obtain ⟨original, originalMember, rfl⟩ := member
  exact protected_not_capturable handled scope allowNone original rfl (origin original originalMember)

theorem fresh_protect_residual (handled : List Key) (permission : Permission Key) (row : SetRow n Key) :
    residualRow handled (protectRow FreshBoundaries.fresh permission (liftRow row)) =
      protectRow FreshBoundaries.fresh permission (liftRow (residualRow (handled.filter permission) row)) := by
  change residualRow handled (image _ (image _ row)) = image _ (image _ (residualRow _ row))
  rw [image_comp, image_comp]
  apply residual_image
  intro occurrence
  change Capturable handled (Directed.protect FreshBoundaries.fresh permission
    (FreshBoundaries.liftOccurrence occurrence)) ↔ Capturable (handled.filter permission) occurrence
  rw [FreshBoundaries.fresh_protect_capture_iff]
  simp only [Capturable, List.mem_filter]
  exact ⟨fun ⟨⟨member, zero⟩, allowed⟩ => ⟨⟨member, allowed⟩, zero⟩,
    fun ⟨⟨member, allowed⟩, zero⟩ => ⟨⟨member, zero⟩, allowed⟩⟩

theorem fresh_release_residual (handled : List Key) (permission : Permission Key) (row : SetRow n Key) :
    residualRow handled (releaseRow FreshBoundaries.fresh permission (liftRow row)) =
      releaseRow FreshBoundaries.fresh permission (liftRow (residualRow (handled.filter permission) row)) := by
  change residualRow handled (image _ (image _ row)) = image _ (image _ (residualRow _ row))
  rw [image_comp, image_comp]
  apply residual_image
  intro occurrence
  change Capturable handled (Directed.release FreshBoundaries.fresh permission
    (FreshBoundaries.liftOccurrence occurrence)) ↔ Capturable (handled.filter permission) occurrence
  rw [FreshBoundaries.fresh_release_capture_iff]
  simp only [Capturable, List.mem_filter]
  exact ⟨fun ⟨⟨member, zero⟩, allowed⟩ => ⟨⟨member, allowed⟩, zero⟩,
    fun ⟨⟨member, allowed⟩, zero⟩ => ⟨⟨member, zero⟩, allowed⟩⟩

/-- `[key, 'e]` can contain the same key in its arbitrary infinite tail.
Handling the exposed head preserves that protected tail in full. -/
theorem explicit_head_protected_tail (key : Key) (tail : SetRow n Key) :
    residualRow [key] (joinRow ((algebra (n + 1) Key).head key)
      (protectRow FreshBoundaries.fresh allowNone (liftRow tail))) =
        protectRow FreshBoundaries.fresh allowNone (liftRow tail) := by
  funext occurrence
  apply propext
  constructor
  · rintro ⟨member, blocked⟩
    rcases member with head | tailMember
    · change occurrence = raw key at head
      subst occurrence
      exact False.elim (blocked ⟨by simp [raw], fun _ => rfl⟩)
    · exact tailMember
  · intro member
    exact ⟨Or.inr member, default_protect_noncapturable [key] FreshBoundaries.fresh
      (liftRow tail) (liftRow_zero tail) occurrence member⟩

/-! ## Operational bounds by arbitrary, possibly infinite, rows -/

/-- This is the same request-tree predicate as the finite bound, with the row
itself as a membership predicate rather than a finite membership test. -/
abbrev BoundedBy (row : SetRow n Key) (computation : Computation n Key Payload Response Value) : Prop :=
  Computation.AllRequests row computation

theorem bounded_ofList (row : Directed.Row n Key) (computation : Computation n Key Payload Response Value) :
    BoundedBy (ofList row) computation ↔ Computation.BoundedBy row computation := Iff.rfl

theorem bounded_mono (left right : SetRow n Key) (included : Included left right)
    (computation : Computation n Key Payload Response Value) (bound : BoundedBy left computation) :
    BoundedBy right computation :=
  Computation.allRequests_mono left right included computation bound

theorem image_bounded (transform : Occurrence n Key → Occurrence m Other) (row : SetRow n Key)
    (computation : Computation n Key Payload Response Value) (bound : BoundedBy row computation) :
    BoundedBy (image transform row) (FreshBoundaries.mapRequests transform computation) := by
  apply (FreshBoundaries.allRequests_map transform (image transform row) computation).mpr
  exact Computation.allRequests_mono row _ (fun occurrence member => ⟨occurrence, member, rfl⟩)
    computation bound

theorem image_bounded_iff (transform : Occurrence n Key → Occurrence m Other)
    (injective : Function.Injective transform) (row : SetRow n Key)
    (computation : Computation n Key Payload Response Value) :
    BoundedBy (image transform row) (FreshBoundaries.mapRequests transform computation) ↔
      BoundedBy row computation := by
  change Computation.AllRequests _ (FreshBoundaries.mapRequests transform computation) ↔ _
  rw [FreshBoundaries.allRequests_map]
  have same : (image transform row) ∘ transform = row :=
    funext (fun occurrence => propext (image_apply_iff transform injective row occurrence))
  rw [same]

theorem protect_bounded_iff (scope : Fin n) (permission : Permission Key) (row : SetRow n Key)
    (computation : Computation n Key Payload Response Value) :
    BoundedBy (protectRow scope permission row)
      (Computation.mapRequests (Directed.protect scope permission) computation) ↔ BoundedBy row computation := by
  rw [← FreshBoundaries.mapRequests_same]
  exact image_bounded_iff _ (protect_injective scope permission) row computation

theorem release_bounded_iff (scope : Fin n) (permission : Permission Key) (row : SetRow n Key)
    (computation : Computation n Key Payload Response Value) :
    BoundedBy (releaseRow scope permission row)
      (Computation.mapRequests (Directed.release scope permission) computation) ↔ BoundedBy row computation := by
  rw [← FreshBoundaries.mapRequests_same]
  exact image_bounded_iff _ (release_injective scope permission) row computation

theorem reindexTree_bounded_iff (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (row : SetRow n Key) (computation : Computation n Key Payload Response Value) :
    BoundedBy (reindexRow embedding row) (FreshBoundaries.reindexTree embedding computation) ↔
      BoundedBy row computation :=
  image_bounded_iff _ (FreshBoundaries.reindex_injective embedding injective) row computation

theorem bounded_zeroAt (scope : Fin n) (row : SetRow n Key) (origin : ZeroAt scope row)
    (computation : Computation n Key Payload Response Value) (bound : BoundedBy row computation) :
    Computation.ZeroAt scope computation :=
  Computation.allRequests_mono row _ origin computation bound

/-- An infinite inferred upper bound supplies zero origin just as a finite
one does. No source-level allocation claim is hidden in this conditional bound. -/
theorem inferred_fresh_origin (row : RowExpr Key (Fin n) Slot) (rows : Slot → SetRow n Key)
    (computation : Computation (n + 1) Key Payload Response Value)
    (bound : BoundedBy ((FreshRowInference.mapScopes Fin.succ row).eval (algebra (n + 1) Key)
      (fun slot => liftRow (rows slot))) computation) :
    Computation.ZeroAt FreshBoundaries.fresh computation := by
  rw [eval_mapScopes Fin.succ FreshBoundaries.succ_injective] at bound
  exact bounded_zeroAt FreshBoundaries.fresh _ (liftRow_zero _) computation bound

/-- Shallow handling keeps the original input bound on resumptions. Effects
from either arm are joined after subtraction, for arbitrary infinite rows. -/
theorem shallowHandle_bounded [DecidableEq Key] (handled : List Key) (input armEffects : SetRow n Key)
    (onReturn : Value → Computation n Key Payload Response Result)
    (onOperation : Occurrence n Key → Payload →
      (Response → Computation n Key Payload Response Value) → Computation n Key Payload Response Result)
    (returnBound : ∀ value, BoundedBy armEffects (onReturn value))
    (operationBound : ∀ occurrence payload resume, Capturable handled occurrence →
      (∀ response, BoundedBy input (resume response)) → BoundedBy armEffects (onOperation occurrence payload resume))
    (computation : Computation n Key Payload Response Value) (inputBound : BoundedBy input computation) :
    BoundedBy (joinRow (residualRow handled input) armEffects)
      (Computation.shallowHandle handled onReturn onOperation computation) := by
  induction computation with
  | pure value => exact bounded_mono _ _ (fun _ member => Or.inr member) _ (returnBound value)
  | request occurrence payload resume ih =>
      by_cases captured : Capturable handled occurrence
      · simp only [Computation.shallowHandle, captured, ↓reduceIte]
        exact bounded_mono _ _ (fun _ member => Or.inr member) _
          (operationBound occurrence payload resume captured inputBound.2)
      · simp only [Computation.shallowHandle, captured, ↓reduceIte]
        exact ⟨Or.inl ⟨inputBound.1, captured⟩, fun response => ih response (inputBound.2 response)⟩

/-- Every tree bounded by a fresh row has the same default-boundary
noncapture property. The infinite row need not have a finite enumeration. -/
theorem bounded_fresh_noncapture [DecidableEq Key] (row : SetRow n Key) (handled : List Key)
    (onReturn : Value → Computation (n + 1) Key Payload Response Result)
    (onOperation : Occurrence (n + 1) Key → Payload →
      (Response → Computation (n + 1) Key Payload Response Value) →
        Computation (n + 1) Key Payload Response Result)
    (computation : Computation (n + 1) Key Payload Response Value)
    (bound : BoundedBy (liftRow row) computation) :
    Computation.shallowHandle handled onReturn onOperation
      (Computation.mapRequests (Directed.protect FreshBoundaries.fresh allowNone) computation) =
        (Computation.mapRequests (Directed.protect FreshBoundaries.fresh allowNone) computation).bind onReturn :=
  Computation.default_zero_boundary_noncapture handled FreshBoundaries.fresh onReturn onOperation computation
    (bounded_zeroAt FreshBoundaries.fresh _ (liftRow_zero row) computation bound)

/-- Explicit allocation preserves an arbitrary infinite bound and supplies
noncapture without assuming zero weights anywhere in the old interface. -/
theorem fresh_boundary [DecidableEq Key] (row : SetRow n Key)
    (computation : Computation n Key Payload Response Value) (bound : BoundedBy row computation)
    (handled : List Key)
    (onReturn : Value → Computation (n + 1) Key Payload Response Result)
    (onOperation : Occurrence (n + 1) Key → Payload →
      (Response → Computation (n + 1) Key Payload Response Value) →
        Computation (n + 1) Key Payload Response Result) :
    BoundedBy (protectRow FreshBoundaries.fresh allowNone (liftRow row))
      (Computation.mapRequests (Directed.protect FreshBoundaries.fresh allowNone)
        (FreshBoundaries.liftTree computation)) ∧
    Computation.shallowHandle handled onReturn onOperation
      (Computation.mapRequests (Directed.protect FreshBoundaries.fresh allowNone)
        (FreshBoundaries.liftTree computation)) =
      (Computation.mapRequests (Directed.protect FreshBoundaries.fresh allowNone)
        (FreshBoundaries.liftTree computation)).bind onReturn :=
  ⟨(protect_bounded_iff FreshBoundaries.fresh allowNone _ _).mpr
      ((reindexTree_bounded_iff Fin.succ FreshBoundaries.succ_injective row computation).mpr bound),
    FreshBoundaries.fresh_noncapture handled onReturn onOperation computation⟩

namespace Examples

open RecursiveRows (Derives)
open RecursiveRows.Examples (growing raised every_weight_derived)

/-- The known infinite least solution participates in both-order cancellation. -/
theorem infinite_least_roundtrip (scope : Fin 1) (permission : Permission Nat) :
    releaseRow scope permission (protectRow scope permission (Derives growing ())) = Derives growing () ∧
    protectRow scope permission (releaseRow scope permission (Derives growing ())) = Derives growing () :=
  ⟨release_protect scope permission _, protect_release scope permission _⟩

theorem every_old_weight_kept (count : Nat) :
    protectRow FreshBoundaries.fresh allowNone (liftRow (Derives growing ()))
      (Directed.protect FreshBoundaries.fresh allowNone (FreshBoundaries.liftOccurrence (raised count))) :=
  ⟨_, ⟨_, every_weight_derived count, rfl⟩, rfl⟩

theorem infinite_least_fresh_origin :
    ZeroAt FreshBoundaries.fresh (Derives (reindexProblem Fin.succ growing) ()) :=
  least_fresh_zero growing ()

/-- A depth-two request tree can have infinitely many signed alternatives,
because an operation response may select an arbitrarily large old weight. -/
def infinitelyBranching : Computation 1 Nat Unit Nat Unit :=
  .request (raw 0) () (fun count => .request (raised count) () (fun _ => .pure ()))

theorem infinite_tree_bound : BoundedBy (Derives growing ()) infinitelyBranching :=
  ⟨every_weight_derived 0, fun count => ⟨every_weight_derived count, fun _ => trivial⟩⟩

/-- The arbitrary-row operational theorem is not merely a finite support
theorem with a larger row: this tree admits no finite request upper bound. -/
theorem infinite_tree_has_no_finite_bound (row : Directed.Row 1 Nat) :
    ¬ Computation.BoundedBy row infinitelyBranching := by
  intro bounded
  have member : raised (RecursiveRows.Examples.weightBound row + 1) ∈ row :=
    (bounded.2 (RecursiveRows.Examples.weightBound row + 1)).1
  have impossible := RecursiveRows.Examples.member_weight_le row _ member
  change RecursiveRows.Examples.weightBound row + 1 ≤ RecursiveRows.Examples.weightBound row at impossible
  omega

end Examples

end Yulang.InfiniteRowHygiene
