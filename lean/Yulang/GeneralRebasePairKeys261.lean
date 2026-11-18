import Yulang.GeneralRebaseClassRun261
namespace Yulang.GeneralRebasePairKeys261
open GeneralSourceState (Output)
open GeneralRebaseStep258 (Fact)
open GeneralNominalCommonBridge (Assignment)

/-- Pair addresses depend on the requests, not their positions in a table.
Kind 3 is deliberately separate from the earlier index-based equality table. -/
def code (first last : Output) : Nat := GeneralNominalIdentities.pair
 (GeneralRebaseNamedRequest260.code first) (GeneralRebaseNamedRequest260.code last)
def key (owner : Nat) (first last : Output) : Fact :=
 GeneralRebaseRequestBodyKeys260.key owner 3 (code first last) 0

theorem code_injective {first last first' last' : Output}
 (same : code first last = code first' last') : first = first' ∧ last = last' := by
 have pair : (GeneralRebaseNamedRequest260.code first,GeneralRebaseNamedRequest260.code last) =
   (GeneralRebaseNamedRequest260.code first',GeneralRebaseNamedRequest260.code last') := GeneralNominalIdentities.pair_injective same
 exact ⟨GeneralRebaseNamedRequest260.code_injective (congrArg Prod.fst pair),
   GeneralRebaseNamedRequest260.code_injective (congrArg Prod.snd pair)⟩

theorem key_injective {owner owner' : Nat} {first last first' last' : Output}
 (same : key owner first last = key owner' first' last') :
 owner = owner' ∧ first = first' ∧ last = last' := by
 obtain ⟨owners,_,codes,_⟩ := GeneralRebaseRequestBodyKeys260.key_identity same
 exact ⟨owners,code_injective codes⟩

def facts (owner : Nat) (outputs : List Output) : List Fact :=
 outputs.flatMap fun first => (outputs.filter fun last => first.name == last.name).map (key owner first)

/-- Meaning is independent of the current table. No existential choice can
substitute a different pair with the same address. -/
def Holds (owner : Nat) (assignment : Assignment) (fact : Fact) : Prop :=
 ∀ first last, fact = key owner first last →
 CommonNominalFullCarrier.Equivalent (assignment first.target).1 (assignment last.target).1

theorem at_key (owner : Nat) (first last : Output) (assignment : Assignment) :
 Holds owner assignment (key owner first last) ↔
 CommonNominalFullCarrier.Equivalent (assignment first.target).1 (assignment last.target).1 := by
 constructor
 · intro valid; exact valid first last rfl
 · intro valid one two same
   obtain ⟨_,rfl,rfl⟩ := key_injective same
   exact valid

theorem member (owner : Nat) (outputs : List Output) (fact : Fact) :
 fact ∈ facts owner outputs ↔ ∃ first ∈ outputs, ∃ last ∈ outputs,
 first.name = last.name ∧ fact = key owner first last := by
 simp only [facts,List.mem_flatMap,List.mem_map,List.mem_filter]
 constructor
 · rintro ⟨first,one,last,⟨two,names⟩,same⟩
   exact ⟨first,one,last,two,by simpa using names,same.symm⟩
 · rintro ⟨first,one,last,two,names,same⟩
   exact ⟨first,one,last,⟨two,by simpa using names⟩,same.symm⟩

theorem all_exact (owner : Nat) (outputs : List Output) (assignment : Assignment) :
 (∀ fact ∈ facts owner outputs, Holds owner assignment fact) ↔
 ∀ first ∈ outputs, ∀ last ∈ outputs, first.name = last.name →
 CommonNominalFullCarrier.Equivalent (assignment first.target).1 (assignment last.target).1 := by
 constructor
 · intro valid first one last two names
   exact (at_key owner first last assignment).mp
     (valid _ ((member ..).mpr ⟨first,one,last,two,names,rfl⟩))
 · intro valid fact included
   obtain ⟨first,one,last,two,names,rfl⟩ := (member ..).mp included
   exact (at_key ..).mpr (valid first one last two names)

theorem monotone (owner : Nat) (small large : List Output)
 (included : ∀ output ∈ small, output ∈ large) :
 ∀ fact ∈ facts owner small, fact ∈ facts owner large := by
 intro fact present
 obtain ⟨first,one,last,two,names,same⟩ := (member ..).mp present
 exact (member ..).mpr ⟨first,included _ one,last,included _ two,names,same⟩

theorem reordered (owner : Nat) (first last : List Output)
 (same : ∀ output, output ∈ first ↔ output ∈ last) (fact : Fact) :
 fact ∈ facts owner first ↔ fact ∈ facts owner last :=
 ⟨monotone owner first last (fun o h => (same o).mp h) fact,
 monotone owner last first (fun o h => (same o).mpr h) fact⟩

/-- Disjoint from any body equation, even with a different request code. -/
theorem body_separate (owner : Nat) (first last : Output) (request equation : Nat) :
 key owner first last ≠ GeneralRebaseRequestBodyKeys260.key owner 1 request equation := by
 intro same
 have kinds := (GeneralRebaseRequestBodyKeys260.key_identity same).2.1
 cases kinds
end Yulang.GeneralRebasePairKeys261
