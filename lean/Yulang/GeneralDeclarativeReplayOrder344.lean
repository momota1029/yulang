import Yulang.GeneralDeclarativeRawReplayArgs344

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeReplayOrder344
open GeneralNominalCenters (Plan Site)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Registry Clause)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeClauseBatch327 (Port Input prepare read_order)
open GeneralDeclarativeClausePlacement327 (portAt located)
open GeneralDeclarativeCommitPosition344 (clauses signature current_stamp)
open GeneralDeclarativeRawCapture344 (rawCap keep base)
open GeneralDeclarativeRawReplayArgs344 (emittedDemand arguments literal_outputs)
open GeneralWhereVersionInstall317 (Journal InstallStep install emitted Models ordered)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralWhereVersionCompiler317 (child children)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralStoppedOrdinarySite335 (demand)
open GeneralStoppedPlacement335 (Meaning)
open CommonRoleOutermostResolver (All₂)

/-- Ports are prepared in source order and retrieved by checked unique
clause key. The returned list is explicitly in the raw canonical
order, not silently equated to an arbitrary source-ordered list. -/
def inputAt (p : Plan rs) (ports : List Port) (c : Clause) (pos : Nat) : Capture :=
  ((portAt p.packet.declaration.requirements ports c).map (fun x => x.input pos)).getD ⟨0,0,0⟩

def logicalChildren (p : Plan rs) (ports : List Port) : List Demand :=
  (clauses p).map fun c => emittedDemand p c.val (inputAt p ports c.val)

structure SameBirth {rs : Roles.RoleDecls} (m : Assignment) (site : Site rs) (logical : Demand) : Prop where
  role : (demand site).role = logical.role
  arguments : All₂ (Meaning m) (demand site).arguments logical.arguments
  targets : (demand site).outputs = logical.outputs

theorem map_pair {rel : β → γ → Prop} (ls : List α) (a : α → β) (b : α → γ)
    (paired : ∀ x ∈ ls, rel (a x) (b x)) : All₂ rel (ls.map a) (ls.map b) := by
  induction ls with
  | nil => exact .nil
  | cons x xs ih =>
    exact .cons (paired x List.mem_cons_self) (ih (fun y h => paired y (List.mem_cons_of_mem _ h)))

theorem actual_ports (p : Plan rs) {s t : State} {protect : List Nat} {ports : List Port}
    (actual : prepare p.packet.registry.constructors p.packet.context.interpretation protect (rawCap p) s
      p.packet.declaration.requirements = some (t,ports))
    (c : Clause) (there : c ∈ p.packet.declaration.requirements) :
    ∃ port, portAt p.packet.declaration.requirements ports c = some port ∧
      Input t p.packet.registry.constructors p.packet.context.interpretation (rawCap p) c port ∧
      inputAt p ports c = port.input := by
  obtain ⟨port,found,witness⟩ := located (read_order actual).2 p.packet.checked.identified.1 there
  exact ⟨port,found,witness,by funext j; simp [inputAt,found]⟩

theorem paired (p : Plan rs) (m : Assignment) (valid : Holds p m)
    {s t : State} {protect : List Nat} {ports : List Port}
    (ran : prepare p.packet.registry.constructors p.packet.context.interpretation protect (rawCap p) s
      p.packet.declaration.requirements = some (t,ports))
    (fits : GeneralDeclarativeHead320.Models t m) :
    All₂ (SameBirth m) (emitted p) (logicalChildren p ports) := by
  unfold emitted logicalChildren
  apply map_pair
  intro c _
  have need := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr c.property
  obtain ⟨port,_,checked,reads⟩ := actual_ports p ran c.val need
  rw [reads]
  exact ⟨rfl,arguments p c.val need (signature p c) m valid fits checked,
    (literal_outputs p c.val (signature p c) port.input).symm⟩

/-- Generic ordered producer for all birth demands of an actual
versioned commit, with both bare and compound inputs. Literal birth
targets are kept. Subsequent alias-class requests are not silently
identified with those birth targets. -/
theorem committed_order (r : Registry) (before : Journal rs) (ctx : GeneralNominalCandidates.Context)
    (p : Plan rs) (step : InstallStep r before (install before ctx p))
    (m : Assignment) (fit : Models (install before ctx p) m) (more : List Nat) :
    ∃ s ports n,
      prepare p.packet.registry.constructors p.packet.context.interpretation
        (keep p (install before ctx p) more) (rawCap p) (base p)
        p.packet.declaration.requirements = some (s,ports) ∧
      GeneralDeclarativeHead320.Models s n ∧ Models (install before ctx p) n ∧
      (∀ k ∈ journalSources (install before ctx p), n k = m k) ∧
      (∀ k ∈ more, n k = m k) ∧
      All₂ (SameBirth n) (emitted p) (logicalChildren p ports) := by
  obtain ⟨s,ports,n,ran,ordinary,raw,foot,localKeep⟩ :=
    GeneralDeclarativeRawCapture344.replay r before ctx p step m fit more
  have receipt := current_stamp r before ctx p step n raw
  exact ⟨s,ports,n,ran,ordinary,raw,foot,localKeep,paired p n receipt.typed ran ordinary⟩

end Yulang.GeneralDeclarativeReplayOrder344
