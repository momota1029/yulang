import Yulang.GeneralRebaseProjectedEdgeCount279
import Yulang.GeneralNominalVersionedMixedCompletionRequests235

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 9800000
namespace Yulang.GeneralRebaseClosedChildShape279
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State initial)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedTrace235 (generated_registered)
open GeneralNominalCenteredHeadMatCompletionRequests (formed_above)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralSourceState (Interval)

def ClosedArguments (r : Registry) : Prop :=
  ∀ d ∈ r.declarations, ∀ c ∈ d.requirements, ∀ p ∈ c.arguments, ∀ name, normalize p ≠ .var name

def argList (roles : Roles.RoleDecls) (seed parent declaration : Nat) (c : Clause) : List Interval :=
  List.ofFn fun index : Fin (roles c.role).arity =>
    (GeneralNominalIdentities.source seed (GeneralNominalAllocation.origin parent declaration 3 c.id index.val),
     GeneralNominalIdentities.source seed (GeneralNominalAllocation.origin parent declaration 4 c.id index.val))

def Canonical (r : Registry) (seed : Nat) (root focus : Occurrence roles) : Prop :=
  focus = root ∨ ∃ parent d, d ∈ r.declarations ∧ ∃ c ∈ d.requirements,
    root.identity ≤ parent ∧
    focus.identity = GeneralNominalIdentities.source seed (GeneralNominalAllocation.origin parent d.id 6 c.id 0) ∧
    focus.demand.role = c.role ∧ List.ofFn focus.demand.arguments = argList roles seed parent d.id c

theorem input_is_port (capture : GeneralDeclarationDemands.Capture) (allocated : Interval) (p : Pattern)
    (nonvar : ∀ binder, normalize p ≠ .var binder) :
    GeneralDeclarationDemands.inputInterval capture allocated p = allocated := by
  unfold GeneralDeclarationDemands.inputInterval
  cases h : normalize p
  case var name => exact False.elim (nonvar name h)
  all_goals rfl

theorem clause_arguments {r : Registry} {p : Plan roles}
    (closed : ClosedArguments r) (visible : p.packet.declaration ∈ r.declarations)
    (c : Clause) (member : c ∈ p.packet.declaration.requirements) (valid : c.Signature roles) :
    List.ofFn (GeneralNominalVersionedFrame231.clauseChild p.packet c valid).demand.arguments =
      argList roles p.packet.context.state.seed p.packet.site.occurrence.identity p.packet.declaration.id c := by
  unfold argList
  apply congrArg List.ofFn
  funext i
  let pos : Nat := i.val
  have within : pos < c.arguments.length := by rw [valid.1]; exact i.isLt
  have closedHere := closed p.packet.declaration visible c member (c.arguments[pos]'within)
    (List.getElem_mem within)
  change GeneralDeclarationDemands.inputInterval (GeneralNominalVersionedFrame231.capture p.packet)
    ((GeneralNominalVersionedFrame231.frame p.packet).allocation p.packet.declaration.id c |>.arguments i)
    (c.arguments[pos]'within) = _
  rw [input_is_port _ _ _ closedHere]
  rfl

theorem emitted {r : Registry} {root : Occurrence roles} {state : State roles} {p : Plan roles}
    (closed : ClosedArguments r)
    (inv : GeneralNominalCenteredHeadMatCompletionRequests.Invariant r seed root state.core)
    (frame : GeneralNominalVersionedEvidence231.Frame r state.core p.packet.site.occurrence p.packet.declaration.id p)
    (member : site ∈ GeneralNominalVersionedChildren232.emitted p) : Canonical r seed root site.occurrence := by
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp member
  have real := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr c.property
  have seedEq : p.packet.context.state.seed = seed := by rw [frame.context_eq,inv.seed_eq]
  refine Or.inr ⟨p.packet.site.occurrence.identity,p.packet.declaration,frame.visible,c.val,real,
    formed_above (inv.raw _ frame.raw_recorded),?_,rfl,?_⟩
  · change GeneralNominalIdentities.source p.packet.context.state.seed _ = _
    rw [seedEq]
    rfl
  · rw [← seedEq]
    exact clause_arguments closed frame.visible c.val real _

theorem trace {r : Registry} {root : Occurrence roles} {state : State roles}
    (closed : ClosedArguments r) (path : B4Target.Steps (Step r root) (initial context root) state) :
    ∀ raw ∈ state.core.erased.current.sites, Canonical r context.state.seed root raw.occurrence := by
  induction path with
  | refl =>
    intro raw recorded
    have eq := List.mem_singleton.mp recorded
    exact Or.inl (by subst raw; rfl)
  | tail path action ih =>
    obtain ⟨focus,generated,step⟩ := action
    cases step with
    | administrative admin =>
      cases admin with
      | enqueue linked absent =>
        obtain ⟨raw,present,same⟩ := generated_registered
          (GeneralNominalVersionedMixedTrace235.steps (GeneralNominalVersionedMixedTrace235.initial context) path).1 generated
        exact False.elim (absent raw present same)
      | refresh | equate | reobserve => exact ih
    | refresh | merge => exact ih
    | install e enabled _ =>
      intro raw recorded
      rcases List.mem_append.mp recorded with old | new
      · exact ih raw old
      · obtain ⟨site,member,rfl⟩ := List.mem_map.mp new
        exact emitted closed (GeneralNominalVersionedMixedCompletionRequests235.trace path)
          (GeneralNominalVersionedMixedAncestry237.frame enabled) member

end Yulang.GeneralRebaseClosedChildShape279
