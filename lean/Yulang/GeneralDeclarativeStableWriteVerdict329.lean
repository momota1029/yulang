import Yulang.GeneralDeclarativeStableRejected329
import Yulang.GeneralDeclarativeStableReplay329

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableWriteVerdict329
open GeneralDeclarativeStableAttempt329 (Attempt RejectedByWrite)
open GeneralDeclarativeStableRejected329 (actual_rejection attempt)
open GeneralDeclarativeRepeatDecl327 (root)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeDemand320 (Demand)
open CommonRoleOutermostResolver (Frontier Classify)

inductive Fate where
  | conflicting
  | continueReading

/-- This is a semantic judgment about one actual elected write,
not a constraint satisfiability algorithm or a candidate classifier.
ContinueReading includes ordinary successful constraints only; where
children can still wait or be rejected independently. -/
inductive Commit (a : Attempt s r i p tests wanted impl) : Fate → Prop where
  | conflict : RejectedByWrite a → Commit a .conflicting
  | continueReading : (∃ m, Models a.after m) → Commit a .continueReading

theorem incompatible (a : Attempt s r i p tests d impl)
    (rejected : Commit a .conflicting) (continueReading : Commit a .continueReading) : False := by
  cases rejected with
  | conflict rejected =>
    cases continueReading with
    | continueReading succeeded => exact rejected.2 succeeded

theorem conflicting_exact (a : Attempt s r i p tests d impl) :
    Commit a .conflicting ↔ RejectedByWrite a :=
  ⟨fun h => by cases h with | conflict why => exact why,.conflict⟩

/-- Current proof-facing tie-error case of the selected source attempt.
Its returned diagnostic is an outright rejected leaf, never pending.
This does not claim totality or disjointness of the other cases. -/
def Rejection (a : Attempt s r i p tests d impl) (actual : Demand) (out : Frontier Demand) : Prop :=
  actual = d ∧ out = .rejected ∧ Commit a .conflicting

theorem error_tree (a : Attempt s r i p tests d impl) (refused : RejectedByWrite a) :
    Classify (Rejection a) d .rejected :=
  ⟨.rejected,.rejected ⟨rfl,rfl,.conflict refused⟩,.rejected⟩

theorem not_pending (a : Attempt s r i p tests d impl) :
    ¬Rejection a d .pending := by
  rintro ⟨_,bad,_⟩
  cases bad

theorem genuine_type_error (done : Nat → Prop) :
    Classify (Rejection (attempt done)) root .rejected :=
  error_tree (attempt done) (actual_rejection done)

end Yulang.GeneralDeclarativeStableWriteVerdict329
