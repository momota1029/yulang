import Yulang.CommonNominalFullModel
import Yulang.CorePresenceGeneration

/-! # Result subsumption for all nominal Common presence source types

The proof includes captured polymorphic bindings and prescribed signatures.
It reuses no solver, residual predicate or old-carrier type restriction.
-/

namespace Yulang.CommonNominalFullSourceSubsumption

open Core.PresenceGeneration
open Inference (Expr)

private theorem comp_trans {a b c : Comp CommonNominalFullCarrier.model}
    (first : Comp.le CommonNominalFullCarrier.model a b) (last : Comp.le CommonNominalFullCarrier.model b c) :
    Comp.le CommonNominalFullCarrier.model a c :=
  ⟨CommonNominalFullCarrier.subtype_trans first.1 last.1, Common.rowLe_trans first.2 last.2⟩

/-- Result subsumption for the independent common presence judgment. The
proof includes captured value schemes and prescribed signatures and does not
use generation or inference. -/
theorem typing_subsume {environment : List (Binding CommonNominalFullCarrier.model)} {expression : Expr}
    {result : Comp CommonNominalFullCarrier.model} (typed : Typing CommonNominalFullCarrier.model environment expression result) :
    ∀ target, Comp.le CommonNominalFullCarrier.model result target → Typing CommonNominalFullCarrier.model environment expression target := by
  induction typed using Typing.rec
    (motive_2 := fun binding result _ =>
      ∀ target, Comp.le CommonNominalFullCarrier.model result target → BindingTyping CommonNominalFullCarrier.model binding target) with
  | var found _ ih => exact fun target below => .var found (ih target below)
  | lit bounded => exact fun _ below => .lit (comp_trans bounded below)
  | lam body bounded _ => exact fun _ below => .lam body (comp_trans bounded below)
  | app function argument bounded _ _ => exact fun _ below => .app function argument (comp_trans bounded below)
  | letValue value definition _ _ body => exact fun target below => .letValue value definition (body target below)
  | letComputed definition body bounded _ _ =>
      exact fun _ below => .letComputed definition body (comp_trans bounded below)
  | branch condition yes no bounded _ _ _ =>
      exact fun _ below => .branch condition yes no (comp_trans bounded below)
  | pair left right bounded _ _ => exact fun _ below => .pair left right (comp_trans bounded below)
  | fst pair bounded _ => exact fun _ below => .fst pair (comp_trans bounded below)
  | snd pair bounded _ => exact fun _ below => .snd pair (comp_trans bounded below)
  | emptyRecord bounded => exact fun _ below => .emptyRecord (comp_trans bounded below)
  | record head tail shape bounded _ _ => exact fun _ below => .record head tail shape (comp_trans bounded below)
  | recordDefault source fallback shape bounded _ _ =>
      exact fun _ below => .recordDefault source fallback shape (comp_trans bounded below)
  | field record bounded _ => exact fun _ below => .field record (comp_trans bounded below)
  | variant payload bounded _ => exact fun _ below => .variant payload (comp_trans bounded below)
  | mono bounded target below => exact .mono (comp_trans bounded below)
  | poly _ row body target below =>
      exact .poly (body (Comp.pure CommonNominalFullCarrier.model target.1) ⟨below.1, Common.rowLe_refl _⟩)
        (Common.rowLe_trans row below.2)
  | signature bounded target below => exact .signature (comp_trans bounded below)

end Yulang.CommonNominalFullSourceSubsumption
