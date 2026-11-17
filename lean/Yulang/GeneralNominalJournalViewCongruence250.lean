import Yulang.GeneralNominalViewCongruence250
import Yulang.GeneralNominalSchemaViewCongruence250
import Yulang.GeneralNominalExprViewCongruence250
import Yulang.GeneralNominalRebaseJournalView243
/-! Every finite materialized Journal field respects full nominal equivalence.
No compilation provenance or assumed metadata stability is needed. -/
namespace Yulang.GeneralNominalJournalViewCongruence250
open GeneralNominalAssignmentCongruence238 (Same all_iff)
open GeneralNominalOriginViewCongruence250 (observes inhabited_iff)
open GeneralNominalSchemaViewCongruence250 (argument_iff site_iff schema_iff)
open GeneralNominalExprViewCongruence250 (equation_iff)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseJournalView243
variable {first last : Assignment}

theorem equations_iff (same : Same first last) (equations : List GeneralNominalRebaseEffectView243.Equation) :
 GeneralNominalRebasePacketView243.AllEquations equations first ↔
 GeneralNominalRebasePacketView243.AllEquations equations last :=
 forall_congr' fun equation => forall_congr' fun _ => equation_iff same equation

theorem child_iff (same : Same first last) (child : GeneralNominalRebasePacketView243.Child) :
 child.Holds first ↔ child.Holds last :=
 and_congr (site_iff same child.site) (equations_iff same child.equations)

theorem packet_iff (same : Same first last) (packet : GeneralNominalRebasePacketView243.Packet) :
 packet.Holds first ↔ packet.Holds last :=
 and_congr (GeneralNominalViewCongruence250.models_iff packet.raw same)
 (and_congr (all_iff same packet.ordinary)
 (and_congr (GeneralNominalProjectionViewCongruence250.projection_iff same packet.projection)
 (and_congr (site_iff same packet.input)
 (and_congr (forall_congr' fun a => forall_congr' fun _ => argument_iff same a)
 (and_congr (schema_iff same packet.head)
 (and_congr (forall_congr' fun child => forall_congr' fun _ => child_iff same child)
 (equations_iff same packet.outputs)))))))

theorem class_iff (same : Same first last) (view : GeneralNominalRebaseClassView243.View) :
 view.Holds first ↔ view.Holds last :=
 and_congr (equations_iff same view.equations) (all_iff same view.equalities)

theorem effect_iff (same : Same first last) (effect : Effect) : effect.Holds first ↔ effect.Holds last :=
 and_congr (GeneralNominalViewCongruence250.models_iff effect.raw same)
 (and_congr (GeneralNominalProjectionViewCongruence250.projection_iff same effect.projection)
 (and_congr (class_iff same effect.historical) (class_iff same effect.live)))

theorem observed_forward (same : Same first last) (a : GeneralNominalRebaseObservedSite243.Argument)
 (valid : a.Holds first) : a.Holds last := by
 intro origin found
 refine ⟨(inhabited_iff same _).mp (valid origin found).1,?_⟩
 intro value seen
 obtain ⟨old,observed,equal⟩ := observes (GeneralNominalAssignmentCongruence238.symm same) seen
 exact (GeneralNominalProjectionViewCongruence250.fits_iff same ⟨equal.2,equal.1⟩ a.bounds).mp
   ((valid origin found).2 old observed)

theorem observed_iff (same : Same first last) (a : GeneralNominalRebaseObservedSite243.Argument) :
 a.Holds first ↔ a.Holds last :=
 ⟨observed_forward same a,observed_forward (GeneralNominalAssignmentCongruence238.symm same) a⟩

theorem observations_iff (same : Same first last) (arguments : List GeneralNominalRebaseObservedSite243.Argument) :
 GeneralNominalRebaseObservedSite243.Holds arguments first ↔
 GeneralNominalRebaseObservedSite243.Holds arguments last :=
 forall_congr' fun a => forall_congr' fun _ => observed_iff same a

theorem models_iff (same : Same first last) (journal : Journal) : journal.Models first ↔ journal.Models last :=
 and_congr (GeneralNominalViewCongruence250.models_iff journal.current same)
 (and_congr (GeneralNominalViewCongruence250.models_iff journal.source same)
 (and_congr (forall_congr' fun arguments => forall_congr' fun _ => observations_iff same arguments)
 (and_congr (forall_congr' fun site => forall_congr' fun _ => site_iff same site)
 (and_congr (forall_congr' fun packet => forall_congr' fun _ => packet_iff same packet)
 (forall_congr' fun effect => forall_congr' fun _ => effect_iff same effect)))))
end Yulang.GeneralNominalJournalViewCongruence250
