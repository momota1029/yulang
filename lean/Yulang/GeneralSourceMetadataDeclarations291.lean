import Yulang.GeneralSourceMetadataSyntax291

/-! Independently reflect coverage of the explicit declaration list,
including the where-output equations, not just the candidate heads. -/
namespace Yulang.GeneralSourceMetadataDeclarations291
open GeneralSourceMetadataUse291
open GeneralSourceMetadataSyntax291 (patterns manyPatterns pattern_exact patterns_exact)
open GeneralDeclarations (Clause Declaration Registry)
open GeneralDeclarationPatterns (Constructors)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadWFSource (DeclarationCovered)

def clauseUses (c : Clause) : List Use :=
  manyPatterns c.arguments ++ c.outputs.flatMap (fun out => patterns out.rhs)

def declarationUses (d : Declaration) : List Use :=
  manyPatterns d.head ++ d.requirements.flatMap clauseUses ++ d.associated.flatMap (fun out => patterns out.rhs)

theorem declaration_exact (c : Constructors) (i : Interpretation) (d : Declaration) :
    UsesOK c i (declarationUses d) ↔ DeclarationCovered c i d := by
  simp only [declarationUses,clauseUses,use_append,use_flatMap,patterns_exact,pattern_exact,DeclarationCovered]
  constructor
  · rintro ⟨⟨a,b⟩,d⟩; exact ⟨a,b,d⟩
  · rintro ⟨a,b,d⟩; exact ⟨⟨a,b⟩,d⟩

def explicitUses (ds : List Declaration) : List Use := ds.flatMap declarationUses

def explicitCheck (r : Registry) (i : Interpretation) : Bool :=
  check r.constructors i (explicitUses r.declarations)

theorem explicit_exact (r : Registry) (i : Interpretation) :
    explicitCheck r i = true ↔ ∀ d ∈ r.declarations, DeclarationCovered r.constructors i d := by
  simp only [explicitCheck,check_exact,explicitUses,use_flatMap,declaration_exact]

end Yulang.GeneralSourceMetadataDeclarations291
