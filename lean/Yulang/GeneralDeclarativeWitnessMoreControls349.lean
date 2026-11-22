import Yulang.GeneralDeclarativeWitnessPointFixture349
import Yulang.GeneralDeclarativeWitnessFixture349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessMoreControls349
open GeneralDeclarativeWitnessHeader349 (check)
open GeneralDeclarativeWitnessProblem349 (Problem)
open GeneralDeclarativeWitnessFixture349 (state)
open GeneralSourceMetadataRows291 (Source)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern StableSmaller substArgs encodeArgs)
open GeneralDeclarativeWitnessTree349 (Report agrees)
open CommonRoleOutermostResolver (Tree)

def tables : Source := ⟨.absent,[⟨22,some ⟨[.type],22⟩,.invariant⟩]⟩
def declaration (head : Pattern) : Declaration := ⟨8,7,[head],[⟨0,8,[.var 3],[]⟩],[],[]⟩
def subDecl : Declaration := ⟨9,8,[.var 3],[],[],[]⟩
def metadata (head : Pattern) : InputBundle := ⟨tables,tables,⟨0,[⟨7,1,[]⟩,⟨8,1,[]⟩]⟩,
  [declaration head,subDecl]⟩
def problem (head : Pattern) : Problem := ⟨metadata head,state,⟨7,[⟨0,0,0⟩],[]⟩⟩

theorem unary_where : check (problem (.app 22 [.var 3])) ⟨[]⟩ = true := rfl

/-- This proves one unsupported schema is compatible with the actual
universal stability condition. Certificate failure is not a language
rejection or a counterexample to stability. -/
theorem stable_unhandled :
    StableSmaller [.variant 1 (.var 3)] [.var 3] ∧
      check (problem (.variant 1 (.var 3))) ⟨[]⟩ = false := by
  refine ⟨?_,rfl⟩
  intro capture
  constructor
  · simp [GeneralDeclarationPatterns.counted,GeneralDeclarationPatterns.substArgs,
      Pattern.subst,GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralDeclarationPatterns.encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size]
  · intro n
    simp [GeneralDeclarationPatterns.counted,GeneralDeclarationPatterns.substArgs,
      Pattern.subst,GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralDeclarationPatterns.encodeArgs,Pattern.encode,Roles.argsOccurrences,Roles.Term.occurrences]

def firstTree : Tree := .selected 8 [.selected 10 [],.selected 11 []]
def real : Report := ⟨firstTree,.selected (.node 8 [.node 10 [],.node 11 []]),[]⟩

theorem ordered_tree :
    agrees (problem (.app 22 [.var 3])) firstTree real = true := by decide +kernel

theorem swapped_children :
    agrees (problem (.app 22 [.var 3])) firstTree
       {real with tree := .selected 8 [.selected 11 [],.selected 10 []]} = false := by decide +kernel

theorem swapped_dictionary :
    agrees (problem (.app 22 [.var 3])) firstTree
       {real with result := .selected (.node 8 [.node 11 [],.node 10 []])} = false := by decide +kernel

def partialTree : Tree := .selected 8 [.pending]
theorem pending_child_retained :
    agrees (problem (.app 22 [.var 3])) partialTree ⟨partialTree,.pending,[]⟩ = true ∧
      agrees (problem (.app 22 [.var 3])) partialTree ⟨.pending,.pending,[]⟩ = false := by
  decide +kernel

end Yulang.GeneralDeclarativeWitnessMoreControls349
