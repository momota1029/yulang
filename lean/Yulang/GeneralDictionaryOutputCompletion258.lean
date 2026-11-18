import Yulang.GeneralDictionaryOutputFrame258
import Yulang.GeneralDictionaryOutputDepthInstall252
namespace Yulang.GeneralDictionaryOutputCompletion258
open GeneralDictionaryOutputDepth252
open GeneralDictionaryOutputFrame258 (complete)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

def expected (assignment : Assignment) : Ty := nominal 0 [.inl (nominal 0 [.inl (assignment 2).1])]

theorem rhs_exact (assignment : Assignment) :
 GeneralNominalCenteredHeadMatExpressions.value (GeneralNominalVersionedPlans231.variables plan assignment) .actual rhs = expected assignment := by
 simp only [GeneralNominalCenteredHeadMatExpressions.value,GeneralNominalCenteredHeadMatExpressions.values]
 change nominal 0 [.inl (nominal 0 [.inl (assignment (GeneralNominalVersionedFrame231.binder plan 0)).1])] = _
 rw [binder_exact]
 rfl

theorem outputs_exact (assignment : Assignment) :
 GeneralNominalVersionedPlans231.Outputs plan assignment ↔ Equivalent (assignment 3).1 (expected assignment) := by
 unfold GeneralNominalVersionedPlans231.Outputs
 rw [emitted_exact]
 change (∀ equation ∈ ([⟨3,.actual,rhs⟩] : List GeneralNominalCenteredHeadMatSchemas.Equation), equation.Holds _ _) ↔ _
 constructor
 · intro valid
   have one := valid ⟨3,.actual,rhs⟩ (List.mem_singleton_self _)
   change Equivalent (assignment 3).1 (GeneralNominalCenteredHeadMatExpressions.value _ .actual rhs) at one
   rwa [rhs_exact] at one
 · intro equal equation member
   cases List.mem_singleton.mp member
   change Equivalent (assignment 3).1 (GeneralNominalCenteredHeadMatExpressions.value _ .actual rhs)
   rwa [rhs_exact]

theorem completed_outputs (assignment : Assignment) : GeneralNominalVersionedPlans231.Outputs plan (complete assignment) := by
 apply (outputs_exact _).mpr
 have fixed := GeneralDictionaryOutputFrame258.outside assignment 2 (by decide)
 change Equivalent (GeneralPresenceOrderedBlock247.put CommonNominalFullCarrier.model assignment 3 (expected assignment) 3).1
   (nominal 0 [.inl (nominal 0 [.inl (complete assignment 2).1])])
 rw [fixed]
 simp only [GeneralPresenceOrderedBlock247.put,ite_true]
 exact ⟨subtype_refl _,subtype_refl _⟩

theorem packet_exact (assignment : Assignment) :
 GeneralNominalVersionedPlans231.Holds plan (complete assignment) ↔ GeneralNominalState.Models snapshot assignment := by
 rw [GeneralDictionaryOutputInputs258.packet_exact,GeneralDictionaryOutputFrame258.source_exact]
 exact and_iff_left (completed_outputs assignment)

theorem classes (assignment : Assignment) (outputs : GeneralNominalVersionedPlans231.Outputs plan assignment) :
 GeneralNominalVersionedEffects231.ClassEffects initial.core root plan assignment := by
 constructor
 · intro output member body found
   cases GeneralDictionaryOutputDepthInstall252.request_single member
   have equal : body = .explicit ⟨0,0,.app 0 [.app 0 [.var 0]]⟩ := Option.some.inj found.symm
   subst body
   change ∀ equation ∈ ([⟨3,.actual,rhs⟩] : List GeneralNominalCenteredHeadMatSchemas.Equation), equation.Holds _ _
   intro equation member
   cases List.mem_singleton.mp member
   change Equivalent (assignment 3).1 (GeneralNominalCenteredHeadMatExpressions.value _ .actual rhs)
   simp only [GeneralNominalVersionedEffects231.bodyVariables]
   rw [rhs_exact]
   exact (outputs_exact assignment).mp outputs
 · intro first one last two _
   cases GeneralDictionaryOutputDepthInstall252.request_single one
   cases GeneralDictionaryOutputDepthInstall252.request_single two
   exact ⟨subtype_refl _,subtype_refl _⟩

theorem installation (assignment : Assignment) (source : GeneralNominalState.Models snapshot assignment) :
 GeneralNominalVersionedInstall232.InstallationModels initial GeneralDictionaryOutputDepthInstall252.effect (complete assignment) := by
 have packetValid := (packet_exact assignment).mpr source
 have raw := packetValid.1
 have output := completed_outputs assignment
 have classValid := classes (complete assignment) output
 refine ⟨?_,packetValid,⟨GeneralNominalVersionedPlans231.head_models packetValid,classValid⟩,?_,?_,?_⟩
 · exact (GeneralNominalVersionedJournal232.initial_models ..).mpr ⟨raw,fun _ => ⟨subtype_refl _,subtype_refl _⟩⟩
 · exact (GeneralNominalVersionedFrameTransport232.class_effects_iff
     (fun _ => GeneralNominalVersionedTerminal232.requests_iff children_empty)).mpr classValid
 · intro prior member; cases member
 · intro prior member; cases member

theorem installed_models (assignment : Assignment) (source : GeneralNominalState.Models snapshot assignment) :
 GeneralNominalVersionedJournal232.Models GeneralDictionaryOutputDepthInstall252.installed (complete assignment) :=
 (GeneralNominalVersionedInstall232.install_models rfl).mpr (installation assignment source)
end Yulang.GeneralDictionaryOutputCompletion258
