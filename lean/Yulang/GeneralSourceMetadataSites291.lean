import Yulang.GeneralSourceMetadataProblem291

/-! Preserve the resolved source family alongside each use. This is not
a textual span map and no parser or new syntax is assumed. -/
namespace Yulang.GeneralSourceMetadataSites291
open GeneralSourceMetadataUse291 (Use)
open GeneralSourceMetadataSyntax291 (patterns manyPatterns terms)
open GeneralSourceMetadataDeclarations291 (clauseUses declarationUses explicitUses)
open GeneralSourceMetadataDefaults291 (Default defaultUses)
open GeneralDeclarations (Clause Declaration)

inductive Site
  | head (decl : Nat)
  | whereInput (decl clause : Nat)
  | whereOutput (decl clause equation : Nat)
  | associated (decl equation : Nat)
  | roleDefault (role name : Nat)
  deriving DecidableEq, Repr

structure Entry where
  site : Site
  query : Use
  deriving DecidableEq, Repr

def tag (site : Site) (uses : List Use) : List Entry := uses.map (fun u => ⟨site,u⟩)

@[simp] theorem tag_query (site : Site) (uses : List Use) : (tag site uses).map Entry.query = uses := by
  unfold tag
  rw [List.map_map]
  exact List.map_id _

def clauseSites (decl : Nat) (c : Clause) : List Entry :=
  tag (.whereInput decl c.id) (manyPatterns c.arguments) ++
    c.outputs.flatMap (fun e => tag (.whereOutput decl c.id e.id) (patterns e.rhs))

def declarationSites (d : Declaration) : List Entry :=
  tag (.head d.id) (manyPatterns d.head) ++ d.requirements.flatMap (clauseSites d.id) ++
    d.associated.flatMap (fun e => tag (.associated d.id e.id) (patterns e.rhs))

def sourceSites (ds : List Declaration) (defaults : List Default) : List Entry :=
  ds.flatMap declarationSites ++
    defaults.flatMap (fun d => tag (.roleDefault d.role d.name) (terms d.body))

theorem clause_queries (decl : Nat) (c : Clause) :
    (clauseSites decl c).map Entry.query = clauseUses c := by
  simp [clauseSites,clauseUses,List.map_flatMap]

theorem declaration_queries (d : Declaration) :
    (declarationSites d).map Entry.query = declarationUses d := by
  simp [declarationSites,declarationUses,List.map_flatMap,clause_queries]

theorem source_queries (ds : List Declaration) (defaults : List Default) :
    (sourceSites ds defaults).map Entry.query = explicitUses ds ++ defaultUses defaults := by
  simp [sourceSites,explicitUses,defaultUses,List.map_flatMap,declaration_queries]

end Yulang.GeneralSourceMetadataSites291
