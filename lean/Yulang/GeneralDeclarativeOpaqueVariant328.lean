import Yulang.GeneralDeclarativeOpaqueChannel328
import Yulang.CommonNominalFullConstructors

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 8000000
namespace Yulang.GeneralDeclarativeOpaqueVariant328
open CommonNominalFullCarrier (Ty Row variant observeTy Subtype Equivalent subtype_trans common_variant_iff)
open GeneralDeclarativeOpaqueChannel328 (union meet tests tests_union tests_meet)
open CommonNominalFullDemand (Environment Observation ProbeAt ProbeStep MaskedProbeStep)
open CommonNominalSyntax (Layer graph observe)

def project (tag : Nat) : Ty → Option Ty
  | .variant label p => if label = tag then some (graph Row p) else none
  | .union a b => union (project tag a) (project tag b)
  | .inter a b => meet (project tag a) (project tag b)
  | .mask _ e => project tag e
  | .bottom => some .bottom
  | _ => none

theorem probe_step (tag depth : Nat) (env) (order) (o) (s : Ty) (hidden : List Nat) :
    MaskedProbeStep Common.rowLe env order hidden (observeTy (depth+1) s) (.variant tag o) ↔
      tests depth env order o (project tag s) := by
  induction s generalizing hidden with
  | union a b i j =>
    rw [project,tests_union]
    exact and_congr (i hidden) (j hidden)
  | inter a b i j =>
    rw [project,tests_meet]
    exact or_congr (i hidden) (j hidden)
  | mask hs e ih => exact ih (hidden ++ hs)
  | bottom => cases o <;> simp [project,tests,observeTy,Layer.evalAt,MaskedProbeStep]
  | variant lbl ty =>
    by_cases eq : lbl = tag
    · subst lbl
      simp only [project,ite_true,tests]
      change (tag = tag ∧ MaskedProbeStep Common.rowLe env order []
        (observeTy depth (graph Row ty)) o) ↔ _
      simp
    · simp [project,eq,tests,observeTy,Layer.evalAt,MaskedProbeStep]
  | recordDefault name source fallback => rfl
  | base | float | top | pair | emptyRecord | exactEmpty | record | arrow | nominal => rfl

theorem read (tag depth rank : Nat) (env : Environment Row) (o : Observation Row)
    (s a : Ty) (someRead : project tag s = some a) :
    ProbeAt Common.rowLe rank env (observeTy (depth+1) s) (.variant tag o) ↔
      ProbeAt Common.rowLe rank env (observeTy depth a) o := by
  cases rank
  · simpa only [ProbeAt,ProbeStep,someRead,tests] using
      probe_step tag depth env (fun _ _ => True) o s []
  · rename_i rank
    simpa only [ProbeAt,ProbeStep,someRead,tests] using
      probe_step tag depth env (fun expected input =>
        ∀ next obs, ProbeAt Common.rowLe rank next input obs → ProbeAt Common.rowLe rank next expected obs) o s []

def onTag (tag : Nat) : Observation Row → Prop
  | .variant expected _ => expected = tag
  | _ => False

theorem off_tag (tag depth rank : Nat) (env : Environment Row) (o : Observation Row)
    (elsewhere : ¬onTag tag o) (a b : Ty) :
    ProbeAt Common.rowLe rank env (observeTy depth (variant tag a)) o ↔
      ProbeAt Common.rowLe rank env (observeTy depth (variant tag b)) o := by
  cases o <;> cases rank <;>
    simp_all [onTag,ProbeAt,ProbeStep,MaskedProbeStep,variant,observeTy,Layer.evalAt,eq_comm]

theorem constructed_project (tag : Nat) (a : Ty) : project tag (variant tag a) = some a := by
  simp [project,variant,graph]

theorem zero_tag (tag rank : Nat) (env : Environment Row) (o : Observation Row) (a : Ty) :
    ProbeAt Common.rowLe rank env (observeTy 0 (variant tag a)) (.variant tag o) := by
  cases rank <;> cases o <;>
    simp [ProbeAt,ProbeStep,MaskedProbeStep,variant,observeTy,Layer.evalAt,observe]

theorem present (tag : Nat) (x a : Ty) (high : Subtype x (variant tag a)) :
    ∃ b, project tag x = some b := by
  let env : Environment Row := ⟨fun _ => .bottom,fun _ => []⟩
  have head : ProbeAt Common.rowLe 0 env (observeTy 1 (variant tag a)) (.variant tag .trivial) :=
    (read tag 0 0 env .trivial (variant tag a) a (constructed_project tag a)).mpr (by
      cases q : observeTy 0 a <;> trivial)
  have carries := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (high 1) 0 env _ head
  have last := (probe_step tag 0 env (fun _ _ => True) .trivial x []).mp carries
  cases found : project tag x with
  | none => simp [found,tests] at last
  | some a => exact ⟨a,rfl⟩

theorem reconstruction (tag : Nat) (x lo hi : Ty)
    (lower : Subtype (variant tag lo) x) (upper : Subtype x (variant tag hi)) :
    ∃ a, project tag x = some a ∧ Equivalent x (variant tag a) ∧ Subtype lo a ∧ Subtype a hi := by
  obtain ⟨a,found⟩ := present tag x hi upper
  have eq (depth : Nat) : CommonNominalFullDemand.ProducerEq Common.rowLe
      (observeTy depth x) (observeTy depth (variant tag a)) := by
    apply (CommonNominalFullDemand.producerEq_iff_probe _ _).mpr
    intro rank env o
    have lo := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (lower depth) rank env o
    have hi := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (upper depth) rank env o
    by_cases inside : onTag tag o
    · cases o
      case variant label inner =>
        have e : label = tag := inside
        subst label
        cases depth with
        | zero =>
          exact ⟨fun _ => zero_tag tag rank env inner a,fun _ => hi (zero_tag tag rank env inner _)⟩
        | succ depth =>
          exact (read tag depth rank env inner x a found).trans
            (read tag depth rank env inner (variant tag a) a (constructed_project tag a)).symm
      all_goals exact False.elim inside
    · exact ⟨fun old => (off_tag tag depth rank env o inside _ a).mp (lo old),
        fun now => hi ((off_tag tag depth rank env o inside a _).mp now)⟩
  have same : Equivalent x (variant tag a) := ⟨fun d => (eq d).1,fun d => (eq d).2⟩
  exact ⟨a,found,same,(common_variant_iff ..).mp (subtype_trans lower same.1),
    (common_variant_iff ..).mp (subtype_trans same.2 upper)⟩

end Yulang.GeneralDeclarativeOpaqueVariant328
