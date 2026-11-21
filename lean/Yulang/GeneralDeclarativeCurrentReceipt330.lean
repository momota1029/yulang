import Yulang.GeneralDeclarativeObserverSource330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCurrentReceipt330
open GeneralDeclarations (Checked Registry Declaration)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeBounds319 (Bound bound_sound)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeEqualities322 (Derives semantic)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeStableCompiler329 (Frame read)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeNFComplete324 (facts)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativePriority321 (Candidates Local selected_generated)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeStableAttempt329 (Elected independent_election)
open GeneralDeclarativeEvidenceFold325 (LocalWitness same_model)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeOpaqueBatch328 (check check_exact)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (Classify Frontier)

/-- A checked ordinary derivation in the current state replaces a
syntactic row of the independently computed frame. This is same-name
readback: it does not rename fixed outputs, manufacture origins,
or quantify over chosen model extensions. -/
structure Receipt (expected current : State) : Prop where
  constraints : expected.normal.ordinary ⊆ current.normal.ordinary
  intervals : ∀ p ∈ expected.normal.intervals, Bound current.normal p.1 p.2
  rows : ∀ row ∈ expected.equations, Derives current (.variable row.left) row.right

theorem literal {s t : State} (known : Extends s t) : Receipt s t :=
  ⟨known.constraints,fun _ x => .interval (known.intervals x),fun _ x => .row (known.equations x)⟩

theorem relays_models {s t : State} (r : Receipt s t) (m) (fit : Models t m) : Models s m := by
  refine ⟨⟨fun _ member => fit.1.1 _ (r.constraints member),?_⟩,?_⟩
  · intro pair used
    exact bound_sound m fit.1 (r.intervals pair used)
  · intro row used
    exact semantic (r.rows row used) m fit

theorem complete {s t : State} {d : Demand} (checked : Checked r) (coverage : Coverage r i)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (declared : Declared r d)
    (chosen : Frame s r i d impl kids) (receipt : Receipt s t) :
    Result t (facts r i chosen.capture impl d kids) ∧
      (∀ m, Models t m → Meaning r i m d impl chosen.capture kids) ∧
      ∀ child ∈ kids, Declared r child := by
  obtain ⟨⟨write,printed,closure⟩,cert,children⟩ := read checked coverage visible role declared chosen
  exact ⟨⟨write,printed,fun row used m fit => closure row used m (relays_models receipt m fit)⟩,
    fun m fit => cert m (relays_models receipt m fit),children⟩

def Staged (current : State) (r : Registry) (i : Interpretation)
    (d : Demand) (impl : Declaration) (kids : List Demand) : Prop :=
  ∃ expected, Nonempty (Frame expected r i d impl kids) ∧ Receipt expected current

abbrev Rule (s : State) (r : Registry) (i : Interpretation)
    {done : Nat → Prop} (p : Supported s done) (tests : Candidates) : Demand → Frontier Demand → Prop :=
  Local s r i p tests (Staged s r i)

theorem exact_proposal {s t : State} {d : Demand} {p : Supported t done}
    (checked : Checked r) (coverage : Coverage r i) (declared : Declared r d)
    (chosen : Frame s r i d impl kids) (receipt : Receipt s t)
    (currentChoice : Elected t r i p tests d impl) (ordered : check kids proposed = true) :
    Rule t r i p tests d (.selected impl.id proposed) ∧
      Result t (facts r i chosen.capture impl d proposed) ∧
      (∀ m, Models t m → Meaning r i m d impl chosen.capture proposed) := by
  have exactList := check_exact.mp ordered
  subst proposed
  have available := complete checked coverage currentChoice.viable.1.1 currentChoice.viable.1.2 declared chosen receipt
  exact ⟨independent_election currentChoice ⟨s,⟨chosen⟩,receipt⟩,available.1,available.2.1⟩

/-- The candidate guards are for the actual current source view. The
ordinary receipt only yields meaning after the same ordered child
list and fixed output targets were taken from actual compilation. -/
theorem local_witness {s : State} {p : Supported s done}
    (checked : Checked r) (coverage : Coverage r i) : LocalWitness r i s (Rule s r i p tests) := by
  intro m fit d declared key kids selected
  obtain ⟨impl,identity,⟨⟨visible,role⟩,_⟩,_,⟨frame⟩,receipt⟩ := selected_generated selected
  obtain ⟨_,meaning,children⟩ := complete checked coverage visible role declared frame receipt
  exact ⟨⟨impl,frame.capture,identity,meaning m fit⟩,children⟩

theorem dictionary {s : State} {p : Supported s done}
    (checked : Checked r) (coverage : Coverage r i) (declared : Declared r d)
    (model : Models s m) (tree : Classify (Rule s r i p tests) d (.selected dict)) :
    Evidence r i m d dict :=
  same_model (local_witness checked coverage) model declared tree

end Yulang.GeneralDeclarativeCurrentReceipt330
