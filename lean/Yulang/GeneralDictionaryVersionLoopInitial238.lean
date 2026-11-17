import Yulang.GeneralDictionaryVersionLoopFull237
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionLoopInitial238
open GeneralDictionaryVersionLoopSource237
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open CommonNominalFullCarrier GeneralNominalCommonBridge
abbrev scalarTerm : GeneralNominalOriginTerms.Expr Nat := .node (.scalar .int) Fin.elim0
abbrev fooTerm : GeneralNominalOriginTerms.Expr Nat := .node (.nominal 0 1) (fun _ => scalarTerm)
abbrev rootTerm : GeneralNominalOriginTerms.Expr Nat := .node (.nominal 5 2) (fun _ => fooTerm)
abbrev rootPattern : Pattern := .app 5 [.app 0 [.app 2 []],.app 0 [.app 2 []]]
theorem root_closed : GeneralNominalGroundAccessibility.ClosedTerm context rootPattern rootTerm := by
 refine ⟨?_,?_,?_⟩
 · simp [rootTerm,fooTerm,scalarTerm,rootPattern,normalize,normalizeArgs,
     GeneralNominalInspection.translate,GeneralCandidateInspection.plainNames,
     GeneralNominalCompoundReadback.quote,List.ofFn_succ,GeneralNominalOriginTerms.arity]
 · simp [rootTerm,fooTerm,scalarTerm,GeneralNominalOriginTerms.Expr.leaves,List.ofFn_succ,GeneralNominalOriginTerms.arity]
 · exact ⟨trivial,fun _ => ⟨trivial,fun _ => ⟨trivial,fun i => Fin.elim0 i⟩⟩⟩
theorem root_denote : GeneralNominalFiniteMeaning.denote (fun _ => .bottom) rootTerm = P := by
 simp [rootTerm,fooTerm,scalarTerm,GeneralNominalFiniteMeaning.denote,
   GeneralNominalFiniteMeaning.build,List.ofFn_succ,GeneralNominalOriginTerms.arity,
   GeneralNominalRecursiveInspection.shapeValue,GeneralNormalizedObservation.Shape.term,
   Core.PresenceGeneration.TyTerm.eval,P,F,S,CommonNominalFullCarrier.model]
theorem scalar_fixed (m : Assignment) (valid : GeneralNominalState.Models snapshot m) : Equivalent (m 0).1 S := by
 constructor
 · exact valid.1.1 (.tyLe (.var 0) (.base .int)) (by simp [atoms,GeneralSourceState.equationAtoms])
 · exact valid.1.1 (.tyLe (.base .int) (.var 0)) (by simp [atoms,GeneralSourceState.equationAtoms])
theorem foo_fixed (m : Assignment) (valid : GeneralNominalState.Models snapshot m) : Equivalent (m 2).1 F := by
 obtain ⟨values,fits,equal⟩ := valid.2.1 2 foo rfl
 change GeneralNominalState.FitsAll base m [.type (0,0)] values at fits
 cases fits with
 | @cons _ a _ rest fit remaining =>
   cases remaining
   cases a with
   | inr => cases fit
   | inl a =>
     have s := scalar_fixed m valid
     have e : Equivalent a S := ⟨subtype_trans fit.2 s.1,subtype_trans s.2 fit.1⟩
     have lifted := GeneralNominalCenteredHeadMatCompilerSemantics.nominal_congr 0 (.cons e .nil)
     exact ⟨subtype_trans equal.1 lifted.1,subtype_trans lifted.2 equal.2⟩
theorem root_fixed (m : Assignment) (valid : GeneralNominalState.Models snapshot m) : Equivalent (m 3).1 P := by
 obtain ⟨values,fits,equal⟩ := valid.2.1 3 pair rfl
 change GeneralNominalState.FitsAll base m [.type (2,2),.type (2,2)] values at fits
 cases fits with
 | @cons _ a _ rest fit remaining =>
   cases remaining with
   | @cons _ b _ tail fit2 remaining =>
     cases remaining
     cases a with
     | inr => cases fit
     | inl a =>
       cases b with
       | inr => cases fit2
       | inl b =>
         have s := foo_fixed m valid
         have e : Equivalent a F := ⟨subtype_trans fit.2 s.1,subtype_trans s.2 fit.1⟩
         have e2 : Equivalent b F := ⟨subtype_trans fit2.2 s.1,subtype_trans s.2 fit2.1⟩
         have lifted := GeneralDictionaryGroundCopy218Source.nominal_pair_congr e e2
         exact ⟨subtype_trans equal.1 lifted.1,subtype_trans lifted.2 equal.2⟩
theorem ground : GeneralNominalGroundAccessibility.GroundRoots context root [rootPattern] := by
 refine ⟨rfl,?_⟩
 intro index
 have zero : index = 0 := Subsingleton.elim _ _
 subst index
 refine ⟨rootTerm,root_closed,?_⟩
 intro m valid
 rw [root_denote]
 exact root_fixed m valid
theorem coverage : GeneralNominalCenteredHeadWFSource.Coverage sourceRegistry interpretation := by
 constructor
 · intro d member
   cases List.mem_singleton.mp member
   simp [GeneralNominalCenteredHeadWFSource.DeclarationCovered,
     GeneralNominalCenteredHeadWFSource.PatternsCovered,GeneralNominalCenteredHeadWFSource.PatternCovered,
     GeneralNominalCenteredHeadWFSource.ConstructorUse]
 · intro role name body found
   cases found
theorem initial_source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root initial :=
 ⟨GeneralNominalCenteredHeadMatStepJournal.initial context root,
   ⟨context,[rootPattern],source,(fun _ => rfl),ground,coverage,rfl⟩,rfl⟩
theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry root initial :=
 ⟨initial,initial_source,.refl⟩
end Yulang.GeneralDictionaryVersionLoopInitial238
