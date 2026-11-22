import Yulang.GeneralDeclarativeStoppedStructural339
import Yulang.GeneralDeclarativeStoppedOrigins339

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoppedLower339
open GeneralNominalState (State Descriptor Denotes)
open Core.PresenceGeneration (CompTerm TyTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseRawView243 (atom all_exact slot)
open GeneralDeclarativeHead320 (Equation Models environment)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralStoppedShape335 (headExpr descriptorExpr descriptor_semantics)
open GeneralStoppedLower335 (record record_exact holds descriptorAt collect collect_exact normal)
open GeneralDeclarativeStoppedStructural339 (encode meaning)
open CommonNominalFullCarrier (Equivalent Subtype)

abbrev headAt (raw : State) (k : Fin raw.base.slots) :=
  record (raw.base.source k) (encode raw.base) (raw.base.heads k).equation

def slotRows (raw : State) (k : Fin raw.base.slots) : Option (List Equation) := do
  let h ← headAt raw k
  let d ← descriptorAt raw k
  pure (h++d)

theorem at_exact (raw : State) (k : Fin raw.base.slots) (m : Assignment)
    (computed : slotRows raw k = some es) :
    holds m es ↔
      (∀ t, (raw.base.heads k).equation = some t →
        Equivalent (m (raw.base.source k)).1
          (t.eval CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment raw.base m))) ∧
      (∀ d, raw.nominals k = some d → Denotes raw.base m k d) := by
  cases first : headAt raw k with
  | none => simp [slotRows,first] at computed
  | some hs =>
    cases next : descriptorAt raw k with
    | none => simp [slotRows,first,next] at computed
    | some ds =>
      have same : hs++ds = es := by simpa [slotRows,first,next] using computed
      subst es
      have a := record_exact (recorded := (raw.base.heads k).equation)
        (check := fun t => Equivalent (m (raw.base.source k)).1
          (t.eval CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment raw.base m)))
        (m := m) (fun t expr e => by rw [meaning raw.base m t e]) first
      have b := record_exact (recorded := raw.nominals k) (check := Denotes raw.base m k)
        (m := m) (fun d expr e => descriptor_semantics raw.base k d m e) next
      rw [← a,← b]
      constructor
      · intro all
        exact ⟨fun e used => all e (List.mem_append_left _ used),fun e used => all e (List.mem_append_right _ used)⟩
      · rintro ⟨a,b⟩ e used
        exact (List.mem_append.mp used).elim (a e) (b e)

def lower (raw : State) : Option GeneralDeclarativeHead320.State :=
  (collect (slotRows raw) (List.ofFn (fun k : Fin raw.base.slots => k))).map (fun es => ⟨normal raw,es⟩)

theorem exact_models (raw : State) (m : Assignment) (ok : lower raw = some s) :
    GeneralDeclarativeHead320.Models s m ↔ GeneralNominalState.Models raw m := by
  unfold lower at ok
  obtain ⟨es,found,rfl⟩ := Option.map_eq_some_iff.mp ok
  have checked := collect_exact (f := slotRows raw) (m := m) _ (fun k _ proof => at_exact raw k m proof) found
  unfold GeneralDeclarativeHead320.Models GeneralDeclarativeWhere319.Models
    GeneralNominalState.Models GeneralNominalCommonBridge.Models
  change ((PresenceNormalForm.All _ m ((raw.base.ordinary.map _) ++ raw.ordinary) ∧ _) ∧ holds m es) ↔ _
  rw [PresenceNormalForm.all_append,all_exact,checked]
  change ((_ ∧ _) ∧ _) ↔ _
  constructor
  · rintro ⟨⟨⟨ordinary,extra⟩,intervals⟩,shapes⟩
    refine ⟨⟨ordinary,fun k => (shapes k (List.mem_ofFn.mpr ⟨k,rfl⟩)).1,?_⟩,fun k => (shapes k (List.mem_ofFn.mpr ⟨k,rfl⟩)).2,extra⟩
    intro pair member
    exact intervals (raw.base.source pair.1,raw.base.source pair.2) (List.mem_map_of_mem member)
  · rintro ⟨⟨ordinary,heads,intervals⟩,desc,extra⟩
    refine ⟨⟨⟨ordinary,extra⟩,?_⟩,fun k _ => ⟨heads k,desc k⟩⟩
    intro pair member
    obtain ⟨ab,there,rfl⟩ := List.mem_map.mp member
    exact intervals ab there


theorem agrees_head {raw : State} {k : Fin raw.base.slots}
    (old : GeneralStoppedLower335.headAt raw k = some rows) : headAt raw k = some rows := by
  cases what : (raw.base.heads k).equation with
  | none =>
    change record (raw.base.source k) headExpr _ = some rows at old
    rw [what] at old
    have exact := Option.some.inj old
    cases exact
    show record (raw.base.source k) (encode raw.base) _ = some []
    rw [what]
    rfl
  | some term =>
    change record (raw.base.source k) headExpr _ = some rows at old
    rw [what] at old
    cases term <;> simp [record,headExpr] at old
    case base tag =>
      cases old
      show record (raw.base.source k) (encode raw.base) _ = some _
      rw [what]
      rfl

theorem agrees_slot {raw : State} {k : Fin raw.base.slots}
    (old : GeneralStoppedLower335.slotRows raw k = some rows) : slotRows raw k = some rows := by
  cases x : GeneralStoppedLower335.headAt raw k with
  | none => simp [GeneralStoppedLower335.slotRows,x] at old
  | some heads =>
    have same := agrees_head x
    simpa [slotRows,GeneralStoppedLower335.slotRows,x,same] using old

theorem agrees_collect (raw : State) (positions : List (Fin raw.base.slots))
    (old : collect (GeneralStoppedLower335.slotRows raw) positions = some rows) :
    collect (slotRows raw) positions = some rows := by
  induction positions generalizing rows with
  | nil => exact old
  | cons head tail ih =>
    cases x : GeneralStoppedLower335.slotRows raw head with
    | none => simp [collect,x] at old
    | some front =>
      cases y : collect (GeneralStoppedLower335.slotRows raw) tail with
      | none => simp [collect,x,y] at old
      | some last => simpa [collect,x,y,agrees_slot x,ih y] using old

/-- The old successful projection is byte-for-byte the same ordinary
state; this is a conservative extension, not a replacement of stored
provenance or a refinement of every solver step. -/
theorem agrees_older {raw : State} (old : GeneralStoppedLower335.lower raw = some s) : lower raw = some s := by
  obtain ⟨rows,found,rfl⟩ := Option.map_eq_some_iff.mp old
  exact Option.map_eq_some_iff.mpr ⟨rows,agrees_collect _ _ found,rfl⟩

/-- The structural projection recognizes a strict extension of the old
head fragment, while exact ordered output receipts still originate in
the real current effect and keep their literal target. -/
theorem installed_outputs {roles : Roles.RoleDecls}
    {root : GeneralSourceDictionaries.Occurrence roles}
    {start final : GeneralNominalVersionedJournal232.State roles}
    {effect : GeneralNominalVersionedJournal232.Effect roles}
    (path : B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) start final)
    (empty : start.effects = []) (retained : effect ∈ final.effects)
    (projected : lower (GeneralStoppedProjectedTrace335.current final) = some base)
    (ready : GeneralNominalCenteredHeadMatEffects.Ready final.core effect.plan.packet.site.occurrence effect.plan)
    (m : Assignment) (fit : GeneralNominalVersionedJournal232.Models final m) :
    ∃ rows, GeneralDeclarativeStoppedOrder339.compileRequests effect.plan
        (GeneralNominalCenteredHeadOutputs.requests final.core effect.plan.packet.site.occurrence) = some rows ∧
      rows.map Equation.left =
        (GeneralNominalCenteredHeadOutputs.requests final.core effect.plan.packet.site.occurrence).map GeneralSourceState.Output.target ∧
      Models (GeneralDeclarativeEntailment320.appendFacts base rows) m ∧
      GeneralStoppedInstallHistory335.InstalledBetween registry root start final effect ∧
      CommonRoleOutermostResolver.All₂ (GeneralDeclarativeStoppedOutput339.Receipt final effect)
        (GeneralNominalCenteredHeadOutputs.requests final.core effect.plan.packet.site.occurrence) rows := by
  obtain ⟨rows,computed⟩ := GeneralDeclarativeStoppedOrder339.complete_known ready (fun _ h => h)
  obtain ⟨each,ordered⟩ := GeneralDeclarativeStoppedOrder339.checked_order (fun _ h => h) computed
  have valid := (exact_models _ m projected).mpr fit.1.1
  have origin := GeneralStoppedInstallHistory335.installed_origin path empty retained
  refine ⟨rows,computed,ordered,(GeneralDeclarativeEntailment320.model_append m).mpr ⟨valid,?_⟩,origin,each⟩
  intro row present
  obtain ⟨_,_,found⟩ := GeneralDeclarativeStoppedOrder339.member_authored each present
  exact (GeneralDeclarativeStoppedOutput339.row_present retained found fit).1

end Yulang.GeneralDeclarativeStoppedLower339
