import Yulang.GeneralRebaseRowParentInputs287
import Yulang.GeneralRebaseRowChildRaw287

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28500
set_option maxHeartbeats 14000000
namespace Yulang.GeneralRebaseRowParentFrame287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287
open GeneralRebaseRowParentInputs287
open GeneralRebaseRowChildRaw287 (OutputCheck before_exact exact_source)
open GeneralRebaseRowParentOutput287 (outputs_exact)
open GeneralNominalVersionedCandidates231 (Prepared Survivor Unique)
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedInstall232 (install installCore InstallationModels)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalVersionedEffects231 (ClassEffects)
open GeneralNominalVersionedPlans231 (Outputs)
open GeneralNominalCenters
open CommonNominalFullCarrier

theorem initial_args : GeneralNominalRecursiveCandidates.arguments ctx
    (GeneralNominalVersionedCandidates231.inputs root) = some [(1,1)] := by decide +kernel

theorem raw_names (name : Nat) (member : name ∈ GeneralNominalState.sources raw) : name ≤ 2 :=
  (source true).below_seed name member

theorem fresh (choice : Bool) :
    GeneralNominalVersionedAllocation231.Fresh raw (registry choice) root.identity (packet choice).bindings := by
  intro key _ collision
  have huge := GeneralNominalIdentities.source_above_seed raw.seed key
  have small := raw_names _ collision
  change raw.seed < _ at huge
  have fix : raw.seed = 2 := rfl
  rw [fix] at huge
  exact False.elim ((Nat.not_lt_of_ge small) huge)

theorem linked (choice : Bool) : GeneralNominalState.Linked raw
    (GeneralNominalVersionedCandidates231.inputs root).demand :=
  ⟨(source choice).linked.1,by intro _ h; cases h⟩

theorem prepared (choice : Bool) : Prepared (registry choice) ctx root parentDecl := by
  refine ⟨metadata choice,linked choice,[(1,1)],initial_args,?_,?_,model Common.rowEmpty,?_⟩
  · exact fresh choice
  · change GeneralNominalRecursiveInspection.Finished (GeneralNominalPacketSupport.report (packet choice))
    rw [parent_report]
    exact ⟨rfl,rfl,rfl⟩
  · have j := (parent_packet choice (model Common.rowEmpty)).mpr ⟨raw_model Common.rowEmpty,⟨subtype_refl _,subtype_refl _⟩⟩
    exact GeneralNominalVersionedPlans231.head_models j

theorem frame (choice : Bool) : Frame (registry choice) before.core root 0 (plan choice) :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,List.mem_cons_self,
      rfl,initial_args,prepared choice⟩

theorem root_known : ¬ GeneralNominalState.RootPending raw root.demand := by
  rintro ⟨i,h⟩
  exact h ⟨(1 : Fin 3),rfl,Or.inr ⟨outer,rfl⟩⟩

theorem at_role (choice : Bool) (d : GeneralDeclarations.Declaration)
    (member : d ∈ (registry choice).declarations) (role : d.role = root.demand.role) : d = parentDecl := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl
  · rfl
  · cases choice <;> cases role

theorem survivor (choice : Bool) : Survivor (registry choice) ctx root 0 [child choice] :=
  ⟨root_known,parentDecl,List.mem_cons_self,parent_checked,rfl,rfl,[(1,1)],initial_args,prepared choice,
    (sole_child choice).symm⟩

theorem unique (choice : Bool) : Unique (registry choice) ctx root 0 [child choice] := by
  refine ⟨survivor choice,?_⟩
  intro other kids first
  have original := first
  obtain ⟨_,d,visible,_,key,role,_,_,_,_⟩ := first
  have parent := at_role choice d visible role
  have same : other = 0 := key.symm.trans (congrArg GeneralDeclarations.Declaration.id parent)
  have original0 : Survivor (registry choice) ctx root 0 kids := same ▸ original
  exact ⟨same,GeneralNominalVersionedCandidates231.survivor_children_functional
    (checked choice) original0 (survivor choice)⟩

theorem before_requests : requests before.core root = [⟨0,2⟩] := by
  have exactCalc : GeneralRebaseExecutableRequests262.requests before.core root = [⟨0,2⟩] := by decide +kernel
  exact (GeneralRebaseExecutableRequests262.requests_eq _ _).symm.trans exactCalc

theorem ready (choice : Bool) : GeneralNominalCenteredHeadMatEffects.Ready before.core root (plan choice) := by
  intro output member
  rw [before_requests] at member
  cases List.mem_singleton.mp member
  exact ⟨.explicit ⟨0,0,.app 0 [.app 0 [.var 0]]⟩,rfl,rfl⟩

noncomputable def effect (choice : Bool) : Effect roles :=
  ⟨registry choice,before.core,plan choice,frame choice,sole_child choice ▸ unique choice,ready choice⟩

noncomputable def after (choice : Bool) := install before (effect choice)

theorem after_requests (choice : Bool) :
    ∀ out, out ∈ requests (after choice).core root ↔ out ∈ requests before.core root := by
  intro out
  have exactCalc : GeneralRebaseExecutableRequests262.requests (after choice).core root = [⟨0,2⟩] := by
    cases choice <;> decide +kernel
  rw [← GeneralRebaseExecutableRequests262.requests_eq,exactCalc,before_requests]

theorem class_before (choice : Bool) (m : Assignment) (outputGood : Outputs (plan choice) m) :
    ClassEffects before.core root (plan choice) m := by
  constructor
  · intro output member body found
    rw [before_requests] at member
    cases List.mem_singleton.mp member
    have equal : body = .explicit ⟨0,0,.app 0 [.app 0 [.var 0]]⟩ := Option.some.inj found.symm
    subst body
    change ∀ equation ∈ ([⟨2,.actual,expression⟩] : List GeneralNominalCenteredHeadMatSchemas.Equation), equation.Holds _ _
    intro equation member
    cases List.mem_singleton.mp member
    change Equivalent (m 2).1 (F (F (GeneralNominalVersionedPlans231.variables (plan choice) m .actual 0)))
    rw [variables_same]
    exact (outputs_exact choice m).mp outputGood
  · intro one hm other hn _
    rw [before_requests] at hm hn
    cases List.mem_singleton.mp hm
    cases List.mem_singleton.mp hn
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem install_check (choice : Bool) (m : Assignment) :
    InstallationModels before (effect choice) m ↔ OutputCheck m := by
  constructor
  · intro held
    exact ⟨(before_exact m).mp held.1,(outputs_exact choice m).mp held.2.1.2.2⟩
  · intro checks
    have packetOK := (parent_packet choice m).mpr ⟨(exact_source m).mpr checks.1,checks.2⟩
    have effects := class_before choice m packetOK.2.2
    refine ⟨(before_exact m).mpr checks.1,packetOK,⟨GeneralNominalVersionedPlans231.head_models packetOK,effects⟩,?_,?_,?_⟩
    · exact (GeneralNominalVersionedFrameTransport232.class_effects_iff (after_requests choice)).mpr effects
    · intro _ nonexistent; cases nonexistent
    · intro _ nonexistent; cases nonexistent

theorem after_exact (choice : Bool) (m : Assignment) : Models (after choice) m ↔ OutputCheck m :=
  (GeneralNominalVersionedInstall232.install_models (effect := effect choice) rfl).trans (install_check choice m)

theorem after_model (choice : Bool) (row : Common.Row) : Models (after choice) (model row) :=
  (after_exact choice _).mpr ⟨(before_exact _).mp (before_model _),subtype_refl _,subtype_refl _⟩

end Yulang.GeneralRebaseRowParentFrame287
