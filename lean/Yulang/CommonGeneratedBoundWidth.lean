import Yulang.CommonGeneratedWidth
import Yulang.CommonGeneratedBoundInspection

/-!
# The generated pool width invariant discharges local optional-bound premises

The dedicated optional inspector requires width only for a record's tail or
a whole default's source. Both are original shared nodes. `PoolWidth` supplies
exactly those facts, with no change of IDs or reconstruction of a field.

The bridge is independent of how the pool width invariant was obtained. In
particular it can be reused by an all-parameter family, without assuming that
the original graph edges already hold.
-/

namespace Yulang.CommonGeneratedBoundWidth

open Common (Ty Row Subtype)
open Core.PresenceGeneration (TyTerm)
open PresenceOpenTailGenerationLowering (Pool)
open CommonPresenceConstraintGraph (rowEval Realizes)
open CommonGeneratedWidth (PoolWidth)
open CommonGeneratedBoundInspection
open CommonSymbolicBoundInspection (Holds BoundRef)
open PresenceGeneratedRigidShape (lower)

variable {m : Nat}

theorem nodeWidth_of_poolWidth (pool : Pool m) (values : Fin pool.size → Ty)
    (widths : PoolWidth pool values) (term : TyTerm (Fin m))
    (member : term ∈ pool.terms) (shape : lower term = true) :
    NodeWidth pool term member values := by
  cases term with
  | record label head tail => exact widths.record label head tail member
  | recordDefault label source fallback => exact widths.recordDefault label source fallback member
  | required label payload => exact nodeWidth_required pool label payload member values
  | inter => cases shape
  | _ => trivial

/-- Every original shared source node in the lower grammar, every independent
row/node assignment realizing the constructor equations, and any optional
payload reference. Only the pool-wide width invariant is needed. -/
theorem optional_exact_of_poolWidth (pool : Pool m) (term : TyTerm (Fin m))
    (member : term ∈ pool.terms) (shape : lower term = true)
    (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (realizes : Realizes pool rows values) (widths : PoolWidth pool values)
    (label : Nat) (payload : Option (Fin pool.size)) :
    Holds (rowEval rows) values (optional pool term member label payload) ↔
      Subtype (values (pool.reference term member)) ((BoundRef.optional label payload).eval values) :=
  optional_realized_exact pool term member shape rows values realizes
    (nodeWidth_of_poolWidth pool values widths term member shape) label payload

end Yulang.CommonGeneratedBoundWidth
