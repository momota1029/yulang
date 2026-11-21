import Yulang.GeneralDeclarativeRecordMask330
import Yulang.GeneralDeclarativeRecordSplit330
import Yulang.GeneralNominalCenteredHeadMatPatternSemantics

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeRecordReconstruct330
open CommonNominalFullCarrier (Ty Row Subtype Equivalent observeTy record)
open CommonNominalFullDemand (Environment Observation MaskedProbeStep ProbeAt ProbeStep)
open CommonNominalSyntax (Layer observe)
open GeneralDeclarativeRecordChannel330 (channel project)
open GeneralDeclarativeRecordIntervals330 (direct projected_below present)
open GeneralDeclarativeRecordProbe330 (read)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)

def isField : Observation Row → Prop
  | .field _ _ | .optional _ _ => True
  | _ => False

theorem off (depth rank : Nat) (env : Environment Row)
    (o : Observation Row) (notField : ¬ isField o) (key : Nat) (a rest b tail : Ty) :
    ProbeAt Common.rowLe rank env (observeTy depth (record key a rest)) o ↔
      ProbeAt Common.rowLe rank env (observeTy depth (record key b tail)) o := by
  cases o <;> cases rank <;>
    simp_all [isField,record,ProbeAt,ProbeStep,MaskedProbeStep,observeTy,Layer.evalAt]

theorem other_in_record {key q : Nat} (diff : q ≠ key) (depth rank : Nat) (env : Environment Row)
    (mode : Bool) (obs : Observation Row) (a tail : Ty) :
    ProbeAt Common.rowLe rank env (observeTy depth (record key a tail)) (channel mode q obs) ↔
      ProbeAt Common.rowLe rank env (observeTy depth tail) (channel mode q obs) ∨
        mode = true ∧ obs = .trivial := by
  cases mode <;> cases rank <;>
    simp [diff,record,channel,ProbeAt,ProbeStep,MaskedProbeStep,observeTy,Layer.evalAt]

theorem at_zero (key rank : Nat) (env : Environment Row) (mode : Bool) (obs : Observation Row)
    (a tail : Ty) : ProbeAt Common.rowLe rank env (observeTy 0 (record key a tail)) (channel mode key obs) := by
  cases mode <;> cases rank <;> cases obs <;>
    simp [record,channel,observeTy,Layer.evalAt,observe,ProbeAt,ProbeStep,MaskedProbeStep]

theorem optional_trivial (key queried depth rank : Nat) (env : Environment Row) (a tail : Ty) :
    ProbeAt Common.rowLe rank env (observeTy depth (record key a tail)) (.optional queried .trivial) := by
  by_cases same : queried = key
  · subst queried
    cases depth with
    | zero => exact at_zero key rank env true .trivial a tail
    | succ depth =>
      apply (read key depth rank env _ _ .trivial true (direct key true a tail)).mpr
      cases rank <;> cases inside : observeTy depth a <;>
        simp [ProbeAt,ProbeStep,MaskedProbeStep]
  · exact (other_in_record same depth rank env true .trivial a tail).mpr (.inr ⟨rfl,rfl⟩)

/-- An exact semantic reassembly when the two channels agree: the
masked residual comes from the *actual* record, not either endpoint.
The mask is a carrier operation, not a manufactured source-origin
row or a claim that an unknown source residual was resolved. -/
theorem reconstruct {key : Nat} {x lo hi loRest hiRest required optional : Ty}
    (low : Subtype (record key lo loRest) x) (high : Subtype x (record key hi hiRest))
    (req : project key false [] x = some required) (opt : project key true [] x = some optional)
    (coherent : Equivalent required optional) :
    Equivalent x (record key required (.mask [key] x)) := by
  let rebuilt := record key required (.mask [key] x)
  have probes (depth rank : Nat) (env : Environment Row) (o : Observation Row) :
      ProbeAt Common.rowLe rank env (observeTy depth x) o ↔
        ProbeAt Common.rowLe rank env (observeTy depth rebuilt) o := by
    have lowProbe := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (low depth) rank env o
    have highProbe := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (high depth) rank env o
    have outside (notField : ¬isField o) :
        ProbeAt Common.rowLe rank env (observeTy depth x) o ↔
          ProbeAt Common.rowLe rank env (observeTy depth rebuilt) o :=
      ⟨fun found => (off depth rank env o notField key lo loRest required _).mp (lowProbe found),
        fun built => highProbe ((off depth rank env o notField key required _ hi hiRest).mp built)⟩
    have inside (mode : Bool) (q : Nat) (obs : Observation Row) (eq : o = channel mode q obs) :
        ProbeAt Common.rowLe rank env (observeTy depth x) o ↔
          ProbeAt Common.rowLe rank env (observeTy depth rebuilt) o := by
      subst o
      by_cases this : q = key
      · subst q
        cases depth with
        | zero =>
          exact ⟨fun _ => at_zero key rank env mode obs required _,
            fun _ => highProbe (at_zero key rank env mode obs hi hiRest)⟩
        | succ depth =>
          have rhs := read key depth rank env _ _ obs mode (direct key mode required (.mask [key] x))
          cases mode
          · exact (read key depth rank env _ _ obs false req).trans rhs.symm
          · have eqAt := (CommonNominalFullDemand.producerEq_iff_probe _ _).mp
              ⟨coherent.2 depth,coherent.1 depth⟩ rank env obs
            exact (read key depth rank env _ _ obs true opt).trans (eqAt.trans rhs.symm)
      · have masked := GeneralDeclarativeRecordMask330.other this depth rank env x mode obs
        have same := (other_in_record this depth rank env mode obs required (.mask [key] x)).trans
          (or_congr masked Iff.rfl)
        refine ⟨fun found => same.mpr (.inl found),?_⟩
        intro checked
        rcases same.mp checked with direct|extra
        · exact direct
        · rcases extra with ⟨rfl,rfl⟩
          exact highProbe (optional_trivial key q depth rank env hi hiRest)
    cases o
    case field q obs => exact inside false q obs rfl
    case optional q obs => exact inside true q obs rfl
    all_goals exact outside (by simp [isField])
  have all (depth : Nat) : CommonNominalFullDemand.ProducerEq Common.rowLe
      (observeTy depth x) (observeTy depth rebuilt) :=
    (CommonNominalFullDemand.producerEq_iff_probe _ _).mpr (probes depth)
  exact ⟨fun d => (all d).1,fun d => (all d).2⟩

/-- Within this sandwich, existence of *any* same-label literal
representation is exactly agreement of the recorded field modes. -/
theorem exact {key : Nat} {x lo hi loRest hiRest req opt : Ty}
    (low : Subtype (record key lo loRest) x) (high : Subtype x (record key hi hiRest))
    (required : project key false [] x = some req) (optional : project key true [] x = some opt) :
    (∃ a tail, Equivalent x (record key a tail)) ↔ Equivalent req opt := by
  constructor
  · rintro ⟨a,tail,h⟩
    have fromRequired : Equivalent req a :=
      ⟨projected_below key false required (direct key false a tail) h.1,
       projected_below key false (direct key false a tail) required h.2⟩
    have fromOptional : Equivalent a opt :=
      ⟨projected_below key true (direct key true a tail) optional h.2,
       projected_below key true optional (direct key true a tail) h.1⟩
    exact eqv_trans fromRequired fromOptional
  · intro found
    exact ⟨req,.mask [key] x,reconstruct low high required optional found⟩

end Yulang.GeneralDeclarativeRecordReconstruct330
