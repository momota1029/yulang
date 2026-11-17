import Yulang.GeneralNominalJournalSubst249
import Yulang.GeneralNominalOrderedJournalExpansion249
/-! Model congruence is proved from actual compilation and finite substitution
constructors, rather than supplied as an abstract stability premise. -/
namespace Yulang.GeneralNominalMaterializedDomain249
open Core.PresenceGeneration (CompTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseRawView243 (read)
open GeneralNominalRebaseJournalView243 (Journal)
open CommonNominalFullCarrier
open GeneralPresenceModelCongruence245 GeneralPresenceCommonLaws245

inductive Materialized : Journal → Prop where
 | source {roles : Roles.RoleDecls} (state : GeneralNominalVersionedJournal232.State roles)
   (empty : GeneralNominalVersionedMixedRegistry234.LegacyEmpty state) (mapping : Nat → CompTerm Nat) :
   Materialized (GeneralNominalRebaseJournalView243.compile state mapping)
 | substituted {journal : Journal} (made : Materialized journal) (mapping : Nat → CompTerm Nat) :
   Materialized (GeneralNominalJournalSubst249.subst mapping journal)

theorem read_compatible (mapping : Nat → CompTerm Nat) (first last : Assignment)
 (same : Compatible model first last) : Compatible model (read mapping first) (read mapping last) := by
 intro name
 exact ⟨type_eval_equiv model common_laws first last same (mapping name).ty,
   row_eval_equal model first last (fun name => (same name).2) (mapping name).row⟩

theorem models_iff {journal : Journal} (made : Materialized journal) (first last : Assignment)
 (same : Compatible model first last) : journal.Models first ↔ journal.Models last := by
 induction made generalizing first last with
 | source state empty mapping =>
   rw [GeneralNominalRebaseJournalView243.compile_exact _ empty,
     GeneralNominalRebaseJournalView243.compile_exact _ empty]
   exact GeneralNominalVersionedSourceCongruence238.models_iff (read_compatible mapping first last same) state empty
 | substituted made mapping ih =>
   rw [GeneralNominalJournalSubst249.models_exact,GeneralNominalJournalSubst249.models_exact]
   exact ih _ _ (read_compatible mapping first last same)

theorem recovered {journal : Journal} (made : Materialized journal)
 (old : List (GeneralPresenceDefinitionRewrite244.Entry Nat)) (assignment : Assignment)
 (valid : PresenceNormalForm.All model assignment (GeneralPresenceDefinitionRewrite244.block old)) :
 journal.Models (GeneralPresenceOrderedBlock247.solve model old assignment) ↔ journal.Models assignment :=
 models_iff made _ assignment (GeneralPresenceOrderedRecovery247.solve_compatible model common_laws old assignment valid)
end Yulang.GeneralNominalMaterializedDomain249
