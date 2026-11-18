import Yulang.GeneralRebaseBodyTable261
import Yulang.GeneralRebaseEqualOutputs260
namespace Yulang.GeneralRebaseClassTable261
open GeneralRebaseStep258
open GeneralNominalCenters
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)

def equalityAddress (owner : Nat) := GeneralRebaseRequestBodyKeys260.space owner 2 0
def equalityKeys (owner : Nat) (outputs : List Output) :=
 GeneralRebaseOwnedOutputKeys260.keys (equalityAddress owner) (GeneralRebaseEqualOutputs260.schema outputs)
def equalityHolds (owner : Nat) (outputs : List Output) (assignment : Assignment) :=
 GeneralRebaseOwnedOutputKeys260.Holds (equalityAddress owner) (GeneralRebaseEqualOutputs260.schema outputs)
  (GeneralRebaseEqualOutputs260.variables assignment) assignment

def facts (plan : Plan roles) (owner : Nat) (outputs : List Output) : List Fact :=
 GeneralRebaseBodyTable261.facts plan owner outputs ++ equalityKeys owner outputs

def Holds (plan : Plan roles) (owner : Nat) (outputs : List Output) (assignment : Assignment) (fact : Fact) : Prop :=
 GeneralRebaseBodyTable261.Holds plan owner outputs assignment fact ∧
 (fact ∈ equalityKeys owner outputs → equalityHolds owner outputs assignment fact)

def Effects (plan : Plan roles) (outputs : List Output) (assignment : Assignment) : Prop :=
 (∀ output ∈ outputs, ∀ body,
 GeneralDictionaryAssociatedProvenance.lookup roles plan.packet.declaration output.name = some body →
 GeneralNominalVersionedEffects231.BodyHolds plan output.target assignment body) ∧
 (∀ first ∈ outputs, ∀ last ∈ outputs, first.name = last.name →
 CommonNominalFullCarrier.Equivalent (assignment first.target).1 (assignment last.target).1)

theorem equality_exact (owner : Nat) (outputs : List Output) (assignment : Assignment) :
 (∀ fact ∈ equalityKeys owner outputs, equalityHolds owner outputs assignment fact) ↔
 ∀ first ∈ outputs, ∀ last ∈ outputs, first.name = last.name →
 CommonNominalFullCarrier.Equivalent (assignment first.target).1 (assignment last.target).1 :=
 (GeneralRebaseOwnedOutputKeys260.all_exact ..).trans (GeneralRebaseEqualOutputs260.holds_exact ..)

theorem all_exact (plan : Plan roles) (owner : Nat) (outputs : List Output) (assignment : Assignment) :
 (∀ fact ∈ facts plan owner outputs, Holds plan owner outputs assignment fact) ↔ Effects plan outputs assignment := by
 constructor
 · intro valid
   constructor
   · apply (GeneralRebaseBodyTable261.all_exact ..).mp
     intro fact member
     exact (valid fact (List.mem_append_left _ member)).1
   · apply (equality_exact ..).mp
     intro fact member
     exact (valid fact (List.mem_append_right _ member)).2 member
 · rintro ⟨bodies,equalities⟩ fact _
   constructor
   · intro output included within
     exact (GeneralRebaseBodyTable261.local_exact ..).mpr (bodies output included) fact within
   · exact (equality_exact ..).mpr equalities fact

/-- Body-kind1 and equality-kind2 are disjoint even when request codes differ. -/
theorem kinds_separate (plan : Plan roles) (owner : Nat) (outputs : List Output) (output : Output) (fact : Fact) :
 ¬ (fact ∈ GeneralRebaseBodyTable261.keys plan owner output ∧ fact ∈ equalityKeys owner outputs) := by
 rintro ⟨one,two⟩
 obtain ⟨first,one⟩ := (GeneralRebaseOwnedOutputKeys260.member ..).mp one
 obtain ⟨last,two⟩ := (GeneralRebaseOwnedOutputKeys260.member ..).mp two
 have spaces := (GeneralRebaseOwnedOutputKeys260.key_identity (one.symm.trans two)).1
 have kinds := (GeneralRebaseRequestBodyKeys260.space_identity spaces).2.1
 cases kinds

noncomputable def actualFacts (state : GeneralNominalCenteredSteps.State roles)
 (root : GeneralSourceDictionaries.Occurrence roles) (plan : Plan roles) (owner : Nat) :=
 facts plan owner (GeneralNominalCenteredHeadOutputs.requests state root)

theorem actual_exact (state : GeneralNominalCenteredSteps.State roles)
 (root : GeneralSourceDictionaries.Occurrence roles) (plan : Plan roles) (owner : Nat) (assignment : Assignment) :
 (∀ fact ∈ actualFacts state root plan owner,
 Holds plan owner (GeneralNominalCenteredHeadOutputs.requests state root) assignment fact) ↔
 GeneralNominalVersionedEffects231.ClassEffects state root plan assignment := all_exact ..

/-- The list may be executable when supplied by a concrete source. `actualFacts`
still uses the noncomputable alias-class request list. -/
def Models (base : Assignment → Prop) (plan : Plan roles) (owner : Nat) (outputs : List Output) :=
 GeneralRebaseFactSemantics259.Models (basis := facts plan owner outputs) base (Holds plan owner outputs)

theorem initial_exact (base : Assignment → Prop) (plan : Plan roles) (owner : Nat) (outputs : List Output) (assignment : Assignment) :
 Models base plan owner outputs (initial _) assignment ↔ base assignment := GeneralRebaseFactSemantics259.initial_exact ..

theorem done_exact (base : Assignment → Prop) (plan : Plan roles) (owner : Nat) (outputs : List Output) (assignment : Assignment) :
 Models base plan owner outputs (done _) assignment ↔ base assignment ∧ Effects plan outputs assignment := by
 rw [Models,GeneralRebaseFactSemantics259.done_exact,all_exact]
end Yulang.GeneralRebaseClassTable261
