import Yulang.GeneralSourceMetadataUse291

/-! Enumerate applications with their arities, not just distinct names.
Explicit source patterns and positional role-default terms differ. -/
namespace Yulang.GeneralSourceMetadataSyntax291
open GeneralSourceMetadataUse291
open GeneralDeclarationPatterns (Pattern Constructors)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadWFSource (PatternCovered PatternsCovered TermCovered TermsCovered)

mutual
 def patterns : Pattern → List Use
  | .var _ => []
  | .app key args => (key,args.length) :: manyPatterns args
  | .record _ p t => patterns p ++ patterns t
  | .variant _ p => patterns p
  | .join first last => patterns first ++ patterns last
 def manyPatterns : List Pattern → List Use
  | [] => []
  | p :: rest => patterns p ++ manyPatterns rest
end

mutual
 theorem pattern_exact (c : Constructors) (i : Interpretation) (p : Pattern) :
    UsesOK c i (patterns p) ↔ PatternCovered c i p := by
  cases p with
  | var name => simp [patterns,UsesOK,PatternCovered]
  | app key args => simp only [patterns,use_cons,PatternCovered,patterns_exact c i args]
  | record tag p t => simp only [patterns,use_append,PatternCovered,pattern_exact c i p,pattern_exact c i t]
  | variant tag p => exact pattern_exact c i p
  | join p q => simp only [patterns,use_append,PatternCovered,pattern_exact c i p,pattern_exact c i q]

 theorem patterns_exact (c : Constructors) (i : Interpretation) (ps : List Pattern) :
    UsesOK c i (manyPatterns ps) ↔ PatternsCovered c i ps := by
  cases ps with
  | nil => simp [manyPatterns,UsesOK,PatternsCovered]
  | cons head rest =>
    simp only [manyPatterns,use_append,PatternsCovered,pattern_exact c i head,patterns_exact c i rest]
end

mutual
 def terms : Roles.Term → List Use
  | .var _ => []
  | .app key args => (key,args.length) :: manyTerms args
 def manyTerms : List Roles.Term → List Use
  | [] => []
  | p :: rest => terms p ++ manyTerms rest
end

mutual
 theorem term_exact (c : Constructors) (i : Interpretation) (term : Roles.Term) :
    UsesOK c i (terms term) ↔ TermCovered c i term := by
  cases term with
  | var name => simp [terms,UsesOK,TermCovered]
  | app key args => simp only [terms,use_cons,TermCovered,terms_exact c i args]

 theorem terms_exact (c : Constructors) (i : Interpretation) (ps : List Roles.Term) :
    UsesOK c i (manyTerms ps) ↔ TermsCovered c i ps := by
  cases ps with
  | nil => simp [manyTerms,UsesOK,TermsCovered]
  | cons head rest => simp only [manyTerms,use_append,TermsCovered,term_exact c i head,terms_exact c i rest]
end

end Yulang.GeneralSourceMetadataSyntax291
