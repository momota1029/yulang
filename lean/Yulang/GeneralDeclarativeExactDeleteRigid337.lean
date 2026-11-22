import Yulang.GeneralDeclarativeExactDelete337

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeExactDeleteRigid337
open GeneralDeclarativeExactDelete337 (subtract recordShell monotone)
open GeneralDeclarativeExactDeleteFinite337 (remaining)
open CommonNominalFullCarrier (Ty Equivalent Subtype observeTy mask record subtype_trans exactEmpty emptyRecord)
open CommonNominalFullDemand (Environment ProbeAt ProbeStep MaskedProbeStep)

abbrev Fields := List (Nat × Ty)

inductive Terminal : Ty → Prop where
  | width : Terminal emptyRecord
  | exact : Terminal exactEmpty

def literal : Fields → Ty → Ty
  | [],e => e
  | (k,p)::rest,e => record k p (literal rest e)

def surviving (removed : List Nat) (fields : Fields) : Fields :=
  fields.filter fun e => !removed.contains e.1

private theorem record_shell (fields : Fields) (term : Terminal e) :
    recordShell (literal fields e) = literal fields e := by
  cases fields with
  | nil => cases term <;> rfl
  | cons x rest => cases x; rfl

/-- On every finite independently supported literal spine this is
actual field removal, keeping the original standalone terminal. It
does not replace an exact remainder by a masked approximation. -/
theorem deletes_literal (keys : List Nat) (fields : Fields) (term : Terminal e) :
    subtract keys (literal fields e) = literal (surviving keys fields) e := by
  induction fields with
  | nil => cases term <;> rfl
  | cons current more ih =>
    obtain ⟨label,payload⟩ := current
    by_cases gone : label ∈ keys
    · have dropped : surviving keys ((label,payload)::more) = surviving keys more := by
        simp [surviving,gone]
      rw [dropped]
      change (if label ∈ keys then recordShell (subtract keys (literal more e)) else _) = _
      rw [ite_eq_left gone,ih,record_shell _ term]
    · have stays : surviving keys ((label,payload)::more) = (label,payload)::surviving keys more := by
        simp [surviving,gone]
      rw [stays]
      change (if label ∈ keys then recordShell (subtract keys (literal more e)) else
        record label payload (subtract keys (literal more e))) = record label payload (literal (surviving keys more) e)
      rw [ite_eq_right gone,ih]

theorem interval (keys : List Nat) (first last : Fields) (lo : Terminal left) (hi : Terminal right)
    (bounded : Subtype (literal first left) actual ∧ Subtype actual (literal last right)) :
    Subtype (literal (surviving keys first) left) (subtract keys actual) ∧
      Subtype (subtract keys actual) (literal (surviving keys last) right) := by
  have below := monotone keys bounded.1
  have above := monotone keys bounded.2
  rw [deletes_literal keys first lo] at below
  rw [deletes_literal keys last hi] at above
  exact ⟨below,above⟩

theorem exact_if_both_empty (keys : List Nat) (first last : Fields)
    (l : surviving keys first = []) (r : surviving keys last = [])
    (bounded : Subtype (literal first exactEmpty) actual ∧ Subtype actual (literal last exactEmpty)) :
    Equivalent (subtract keys actual) exactEmpty := by
  have both := interval keys first last .exact .exact bounded
  rw [l,r] at both
  exact ⟨both.2,both.1⟩

private def env : Environment CommonNominalFullCarrier.Row := ⟨fun _ => .bottom,fun _ => []⟩
private def sample (key : Nat) := record key (.base .int) exactEmpty

theorem closed_real (key : Nat) :
    subtract [key] (sample key) = exactEmpty := by
  simpa [sample,literal,surviving] using deletes_literal [key] [(key,.base .int)] .exact

theorem consumed_optional (key : Nat) :
    ProbeAt Common.rowLe 0 env (observeTy 0 (subtract [key] (sample key))) (.optional key (.base .int)) ∧
    ¬ProbeAt Common.rowLe 0 env (observeTy 0 (mask [key] (sample key))) (.optional key (.base .int)) := by
  rw [closed_real]
  simp [sample,ProbeAt,ProbeStep,MaskedProbeStep,observeTy,CommonNominalSyntax.Layer.evalAt,record,mask,exactEmpty]

end Yulang.GeneralDeclarativeExactDeleteRigid337
