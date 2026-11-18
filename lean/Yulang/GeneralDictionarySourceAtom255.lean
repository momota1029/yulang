import Yulang.GeneralDictionaryOutputDepth252
import Yulang.GeneralNominalPublicBasis253
import Yulang.GeneralPresenceCheckedNormal252
import Yulang.GeneralNominalRebaseRawView243
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionarySourceAtom255
open Core.PresenceGeneration
open GeneralDictionaryOutputDepth252
open GeneralNominalPublicBasis253
open GeneralPresenceCheckedNormal252

theorem constant_not_basis (keys : List (Nat × Nat)) :
 (TyTerm.base .int : TyTerm Nat) ∉ basis registry context keys := by
 simp [basis]

theorem prepare_constant_none (keys : List (Nat × Nat)) (side : Side) :
 prepare side (basis registry context keys) (.base .int) = none := by
 cases side <;> simp [prepare,check,GeneralPresenceCheckedNormal252.atoms,GeneralPresenceUnionNormal252.atoms,
   GeneralPresenceInterNormal252.atoms,constant_not_basis]

/-- The constant is an actual initial raw View consumer, not an invented
postulated journal atom or an arbitrary replacement term. -/
theorem ordinary_member :
 PresenceNormalForm.Atom.tyLe (.var 0) (.base .int) ∈
 (GeneralNominalRebaseRawView243.compile snapshot CompTerm.var).ordinary := by
 simp [GeneralNominalRebaseRawView243.compile,GeneralNominalRebaseRawView243.atom,
   GeneralNominalRebaseRawView243.slot,CompTerm.var,TyTerm.subst,GeneralSourceState.equationAtoms]

/-- Actual source formation and a current model coexist with the rejected
normalizer input. This is a var-only basis diagnostic, not Step divergence. -/
theorem actual_source_failure :
 (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root initial ∧
 GeneralNominalVersionedJournal232.Models initial model ∧
 (PresenceNormalForm.Atom.tyLe (.var 0) (.base .int) ∈
   (GeneralNominalRebaseRawView243.compile snapshot CompTerm.var).ordinary) ∧
 ∀ keys, prepare .upper (basis registry context keys) (.base .int) = none :=
 ⟨initial_source,initial_model,ordinary_member,fun keys => prepare_constant_none keys .upper⟩
end Yulang.GeneralDictionarySourceAtom255
