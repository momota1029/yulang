import Yulang.GeneralPresenceOrderedRebase247
import Yulang.GeneralPresenceConsumerSupport246
import Yulang.GeneralPresenceOrderedSyntax247

/-! Ordered consumer rebase permits genuinely new targets when rewritten typed
reads and public coordinates avoid them. Rows remain globally unchanged.
These finite support premises are not an actual source metadata producer. -/
namespace Yulang.GeneralPresenceOrderedExpansion249
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedDependence247
open GeneralPresenceModelCongruence245 GeneralPresenceOrderedRebase247
open GeneralPresenceConsumerSupport246
open GeneralPresenceUsedSupport245 (typedReads)
variable {Name : Type} [DecidableEq Name]

def Protected (old fresh : List (Entry Name)) (consumers : List (Atom Name)) : Prop :=
 ∀ name ∈ listTypedReads (rewrite old consumers), ∀ entry ∈ fresh, entry.1 ≠ name

theorem rewritten_preserved (model : Model) (old fresh : List (Entry Name))
 (consumers : List (Atom Name)) (protectedReads : Protected old fresh consumers)
 (assignment : Name → Comp model) :
 All model (solve model fresh assignment) (rewrite old consumers) ↔
 All model assignment (rewrite old consumers) := by
 apply GeneralPresenceConsumerSupport246.all_iff model _ assignment (solve_rows model fresh assignment)
 intro name member
 exact congrArg Prod.fst (solve_outside model fresh assignment name (protectedReads name member))

theorem models_forward (model : Model) (laws : Laws model) (old fresh : List (Entry Name))
 (freshSafe : SafeOrder fresh) (consumers : List (Atom Name))
 (protectedReads : Protected old fresh consumers) (assignment : Name → Comp model)
 (valid : All model assignment (consumers ++ block old)) :
 All model (solve model fresh assignment) (rewrite old consumers ++ block fresh) := by
 obtain ⟨consumerValid,oldValid⟩ := (all_append model assignment _ _).mp valid
 apply (all_append model _ _ _).mpr
 refine ⟨?_,block_satisfied model laws.refl fresh freshSafe assignment⟩
 apply (rewritten_preserved model old fresh consumers protectedReads assignment).mpr
 apply (rewrite_exact old consumers model assignment).mpr
 exact (GeneralPresenceOrderedRecovery247.all_recovered model laws old assignment oldValid consumers).mpr consumerValid

theorem public_models_iff (model : Model) (laws : Laws model) (old fresh : List (Entry Name))
 (oldSafe : SafeOrder old) (freshSafe : SafeOrder fresh)
 (consumers : List (Atom Name)) (protectedReads : Protected old fresh consumers)
 (sharedNames : Name → Prop)
 (oldPrivate : ∀ name, sharedNames name → ∀ entry ∈ old, entry.1 ≠ name)
 (freshPrivate : ∀ name, sharedNames name → ∀ entry ∈ fresh, entry.1 ≠ name)
 (boundary : Name → Comp model) :
 (∃ assignment, All model assignment (consumers ++ block old) ∧ Agrees model sharedNames assignment boundary) ↔
 (∃ assignment, All model assignment (rewrite old consumers ++ block fresh) ∧ Agrees model sharedNames assignment boundary) := by
 constructor
 · rintro ⟨assignment,valid,agree⟩
   refine ⟨solve model fresh assignment,models_forward model laws old fresh freshSafe consumers protectedReads assignment valid,?_⟩
   intro name shared
   rw [solve_outside model fresh assignment name (freshPrivate name shared)]
   exact agree name shared
 · rintro ⟨assignment,valid,agree⟩
   refine ⟨solve model old assignment,
     GeneralPresenceOrderedRebase247.models_backward model laws old fresh oldSafe consumers assignment valid,?_⟩
   intro name shared
   rw [solve_outside model old assignment name (oldPrivate name shared)]
   exact agree name shared

theorem type_rewrite_closed (old : List (Entry Name)) (safe : SafeOrder old) (term : TyTerm Name) :
 ∀ name ∈ typedReads (term.subst (mapping old)), ∀ entry ∈ old, entry.1 ≠ name := by
 rw [GeneralPresenceOrderedSyntax247.typed_subst]
 intro name member entry present
 obtain ⟨source,_,read⟩ := List.mem_flatMap.mp member
 exact GeneralPresenceOrderedSyntax247.mapping_closed old safe source name read entry present

theorem rewrite_closed (old : List (Entry Name)) (safe : SafeOrder old) (consumers : List (Atom Name)) :
 Protected old old consumers := by
 intro name member entry present
 obtain ⟨atom,atomMember,read⟩ := List.mem_flatMap.mp member
 obtain ⟨original,_,rfl⟩ := List.mem_map.mp atomMember
 cases original with
 | tyLe a b =>
   rcases List.mem_append.mp read with read | read
   · exact type_rewrite_closed old safe a name read entry present
   · exact type_rewrite_closed old safe b name read entry present
 | rowLe a b => cases read

theorem protected_of_within (old fresh : List (Entry Name)) (safe : SafeOrder old)
 (within : TargetsWithin fresh old) (consumers : List (Atom Name)) : Protected old fresh consumers := by
 intro name read entry member
 obtain ⟨original,present,equal⟩ := within entry member
 rw [← equal]
 exact rewrite_closed old safe consumers name read original present

theorem common_public_models_iff (old fresh : List (Entry Name))
 (oldSafe : SafeOrder old) (freshSafe : SafeOrder fresh)
 (consumers : List (Atom Name)) (protectedReads : Protected old fresh consumers)
 (sharedNames : Name → Prop)
 (oldPrivate : ∀ name, sharedNames name → ∀ entry ∈ old, entry.1 ≠ name)
 (freshPrivate : ∀ name, sharedNames name → ∀ entry ∈ fresh, entry.1 ≠ name)
 (boundary : Name → Comp CommonNominalFullCarrier.model) :
 (∃ assignment, All CommonNominalFullCarrier.model assignment (consumers ++ block old) ∧
   Agrees CommonNominalFullCarrier.model sharedNames assignment boundary) ↔
 (∃ assignment, All CommonNominalFullCarrier.model assignment (rewrite old consumers ++ block fresh) ∧
   Agrees CommonNominalFullCarrier.model sharedNames assignment boundary) :=
 public_models_iff _ GeneralPresenceCommonLaws245.common_laws old fresh oldSafe freshSafe consumers
   protectedReads sharedNames oldPrivate freshPrivate boundary
end Yulang.GeneralPresenceOrderedExpansion249
