import Yulang.GeneralRebaseBodyActual260
namespace Yulang.GeneralRebaseRequestBodyKeys260
open GeneralRebaseStep258
open GeneralNominalCenters
open GeneralDictionaryAssociatedProvenance

/-- A table-address namespace, not a fresh source name or a new language rule. -/
def space (owner kind request : Nat) : Nat :=
 GeneralNominalIdentities.pair owner (GeneralNominalIdentities.pair kind request)

def key (owner kind request equation : Nat) : Fact :=
 GeneralRebaseOwnedOutputKeys260.key (space owner kind request) equation

theorem space_identity {owner kind request owner' kind' request' : Nat}
 (same : space owner kind request = space owner' kind' request') :
 owner = owner' ∧ kind = kind' ∧ request = request' := by
 have outer : (owner,GeneralNominalIdentities.pair kind request) = (owner',GeneralNominalIdentities.pair kind' request') := GeneralNominalIdentities.pair_injective same
 have one := congrArg Prod.fst outer
 have inner : (kind,request) = (kind',request') := GeneralNominalIdentities.pair_injective (congrArg Prod.snd outer)
 exact ⟨one,congrArg Prod.fst inner,congrArg Prod.snd inner⟩

theorem key_identity {owner kind request equation owner' kind' request' equation' : Nat}
 (same : key owner kind request equation = key owner' kind' request' equation') :
 owner = owner' ∧ kind = kind' ∧ request = request' ∧ equation = equation' := by
 obtain ⟨spaces,indices⟩ := GeneralRebaseOwnedOutputKeys260.key_identity same
 obtain ⟨owners,kinds,requests⟩ := space_identity spaces
 exact ⟨owners,kinds,requests,indices⟩

/-- The installed tag is also a namespaced table marker here. It is not yet
identified with a source-owner commitment in the existing fixture runners. -/
def compile (plan : Plan roles) (owner kind request : Nat) (output : GeneralSourceState.Output) :=
 GeneralRebaseBodyDecoder260.compile plan (space owner kind request) output

theorem successful (plan : Plan roles) (owner kind request : Nat) (output : GeneralSourceState.Output) (proposal : Proposal) :
 compile plan owner kind request output = .ok proposal ↔
 ∃ body, lookup roles plan.packet.declaration output.name = some body ∧
 (GeneralNominalCenteredHeadMatEffects.bodySchema plan output.target body).unknown = false ∧
 proposal = .installed (space owner kind request) :: GeneralRebaseOwnedOutputKeys260.keys (space owner kind request)
   (GeneralNominalCenteredHeadMatEffects.bodySchema plan output.target body) :=
 GeneralRebaseBodyDecoder260.successful ..

/-- This exact meaning is for one fixed request layout. Membership in the actual
source requests and coverage of all obligations remain separate requirements. -/
theorem equation_meaning (plan : Plan roles) (owner kind request : Nat) (output : GeneralSourceState.Output)
 (body : Body) (assignment : GeneralNominalCommonBridge.Assignment) :
 (∀ fact ∈ GeneralRebaseOwnedOutputKeys260.keys (space owner kind request)
   (GeneralNominalCenteredHeadMatEffects.bodySchema plan output.target body),
 GeneralRebaseOwnedOutputKeys260.Holds (space owner kind request)
   (GeneralNominalCenteredHeadMatEffects.bodySchema plan output.target body)
   (GeneralNominalVersionedEffects231.bodyVariables plan assignment body) assignment fact) ↔
 GeneralNominalVersionedEffects231.BodyHolds plan output.target assignment body :=
 GeneralRebaseBodyDecoder260.equation_meaning ..

theorem requests_separate (owner kind first last : Nat) (different : first ≠ last)
 (firstSchema lastSchema : GeneralNominalCenteredHeadMatSchemas.Schema) (fact : Fact) :
 ¬ (fact ∈ GeneralRebaseOwnedOutputKeys260.keys (space owner kind first) firstSchema ∧
 fact ∈ GeneralRebaseOwnedOutputKeys260.keys (space owner kind last) lastSchema) := by
 apply GeneralRebaseOwnedOutputKeys260.owners_separate
 intro same
 exact different (space_identity same).2.2

theorem kinds_separate (owner first last request : Nat) (different : first ≠ last)
 (firstSchema lastSchema : GeneralNominalCenteredHeadMatSchemas.Schema) (fact : Fact) :
 ¬ (fact ∈ GeneralRebaseOwnedOutputKeys260.keys (space owner first request) firstSchema ∧
 fact ∈ GeneralRebaseOwnedOutputKeys260.keys (space owner last request) lastSchema) := by
 apply GeneralRebaseOwnedOutputKeys260.owners_separate
 intro same
 exact different (space_identity same).2.1

/-- The same internal probe requests now receive different addresses. The
second request is still not an actual request of source206. -/
theorem probe_repaired :
 compile GeneralDictionaryDefaultGap206Source.plan 37 2 0 ⟨0,0⟩ ≠
 compile GeneralDictionaryDefaultGap206Source.plan 37 2 1 ⟨0,1⟩ := by
 intro same
 have lists := Except.ok.inj same
 have heads := (List.cons.inj lists).1
 have spaces := Fact.installed.inj heads
 have requests := (space_identity spaces).2.2
 cases requests
end Yulang.GeneralRebaseRequestBodyKeys260
