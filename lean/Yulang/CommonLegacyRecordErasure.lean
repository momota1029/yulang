import Yulang.CommonLegacyEmbeddedWitnesses

/-!
# The record-only part of legacy witness erasure

This projection retains field observations and gives the result a record head.
It is a proof construction for arbitrary intermediate witnesses; it does not
change source typing or identify exact emptiness with width in Common.
-/

namespace Yulang.CommonLegacyRecordErasure

universe u
variable {Row : Type u}

open StructuralBase (Ty)
open ProducerContextual (Environment Observation ProbeStep)

def recordView : Ty Row → Ty Row
  | .bottom => .record 0 .bottom .bottom
  | .union first last => .union (recordView first) (recordView last)
  | .inter first last => .inter (recordView first) (recordView last)
  | .record label payload rest => .record label payload rest
  | _ => .emptyRecord

/-- For every row relation, environment, argument comparison, finite old
type and observation, projection retains exactly the old field response and
replaces all other observations by those of a record head. -/
theorem recordView_probe (leRow : Row → Row → Prop) (env : Environment Row)
    (argumentOrder : Ty Row → Ty Row → Prop) (type : Ty Row) (obs : Observation Row) :
    ProbeStep leRow env argumentOrder (recordView type) obs ↔
      match obs with
      | .trivial | .records => True
      | .role name => .records ∈ env.roles name
      | .field label payload => ProbeStep leRow env argumentOrder type (.field label payload)
      | _ => False := by
  induction type generalizing obs with
  | union first last ihf ihl =>
      cases obs <;> simp [recordView, ProducerContextual.probeStep_union, ihf, ihl]
  | inter first last ihf ihl =>
      cases obs <;> simp [recordView, ProducerContextual.probeStep_inter, ihf, ihl]
  | bottom =>
      cases obs <;> simp [recordView, ProbeStep]
  | _ => cases obs <;> simp [recordView, ProbeStep]

end Yulang.CommonLegacyRecordErasure
