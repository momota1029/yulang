import Yulang.GeneralDeclarativeWitnessNode334

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessClassify334
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativePriority321 (Local)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeStableAttempt329 (Elected independent_election)
open GeneralDeclarativeUnfinishedRoot330 (Local59 UnfinishedRoot)
open GeneralDeclarativeWitnessNode334 (Witness)
open GeneralDeclarativeWitnessHead334 (CurrentArgument current_heads)
open GeneralDeclarativeCurrentReceipt330 (Staged complete)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeEvidenceFold325 (LocalWitness same_model)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂ Frontier Classify)

/-- I-60 declarative classification. Positive selections carry
actual supported reads, an actual compiler calculation, and a
current ordinary receipt. The old rules here are only permitted
non-generating verdicts. Missing observation is not the same thing
as missing a tie or failing to check a chosen output receipt. -/
inductive Rule {s : State} (p : Supported s done) (r : Registry) (i : Interpretation)
    (waiting : Demand → Declaration → Prop) : Demand → Frontier Demand → Prop where
  | selected : Witness p r i waiting d impl kids → Rule p r i waiting d (.selected impl.id kids)
  | existing : Local s r i p (candidates p r i waiting) (fun _ _ _ => False) d result →
      Rule p r i waiting d result
  | rootK2 : UnfinishedRoot p d → Rule p r i waiting d .rejected
  | unread : Elected s r i p (candidates p r i waiting) d impl →
      (¬All₂ (CurrentArgument p r.constructors i) d.arguments impl.head) →
      Rule p r i waiting d .pending

theorem selected_witness {s : State} {p : Supported s done}
    (seen : Rule p r i waiting d (.selected key kids)) :
    ∃ impl, impl.id = key ∧ Nonempty (Witness p r i waiting d impl kids) := by
  cases seen with
  | selected w => exact ⟨_,rfl,⟨w⟩⟩
  | existing falseBuild =>
    obtain ⟨_,_,_,no⟩ := GeneralDeclarativePriority321.selected_generated falseBuild
    exact no.elim

theorem selected_center_reads {s : State} {p : Supported s done}
    (seen : Rule p r i waiting d (.selected key kids)) :
    ∃ impl : Declaration, impl.id = key ∧ All₂ (CurrentArgument p r.constructors i) d.arguments impl.head := by
  obtain ⟨impl,which,⟨w⟩⟩ := selected_witness seen
  exact ⟨impl,which,current_heads w.slice w.source⟩

theorem local_sound {s : State} {p : Supported s done}
    (checked : Checked r) (coverage : Coverage r i) :
    LocalWitness r i s (Rule p r i waiting) := by
  intro m fit d declared key kids seen
  obtain ⟨impl,which,⟨w⟩⟩ := selected_witness seen
  obtain ⟨frame,_,_,_⟩ := w.frame checked coverage declared
  obtain ⟨_,meaning,children⟩ := complete checked coverage w.chosen.viable.1.1 w.chosen.viable.1.2 declared frame w.receipt
  exact ⟨⟨impl,frame.capture,which,meaning m fit⟩,children⟩

/-- B4(4), at the I-60 boundary. This quantifies over all declarative
states, support relations, frontiers and models. The induction keeps
one current model through every ordered child, and needs no old-Local
correspondence, solver execution or termination hypothesis. -/
theorem dictionary_sound {s : State} {p : Supported s done}
    (checked : Checked r) (coverage : Coverage r i) (declared : Declared r d)
    (classified : Classify (Rule p r i waiting) d (.selected dict)) :
    ∀ (m : Assignment), Models s m → Evidence r i m d dict :=
  fun _m fit => same_model (local_sound checked coverage) fit declared classified

theorem selected_to_old {s : State} {p : Supported s done}
    (checked : Checked r) (coverage : Coverage r i) (declared : Declared r d)
    (seen : Rule p r i waiting d (.selected key kids)) :
    Local59 s r i p (candidates p r i waiting) (Staged s r i) d (.selected key kids) := by
  obtain ⟨impl,id,⟨w⟩⟩ := selected_witness seen
  rw [← id]
  exact .prior (independent_election w.chosen (w.staged checked coverage declared))

end Yulang.GeneralDeclarativeWitnessClassify334
