import Yulang.GeneralRebaseInstalledReadback271

namespace Yulang.GeneralRebaseUnaryRank271
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Edge Path Cyclic)
open GeneralNominalRecursiveInspection (Origin Test)
open GeneralNominalOriginTerms (project arity)
open GeneralNominalFiniteMeaning (At project_value)
open GeneralDictionaryInspectionHeads215 (tagged_test tag_subtype tagged_nominal tagged_scalar)
open GeneralNominalFiniteHeadInversion renaming head → tag

inductive Unary where
 | scalar (base : Inference.Base)
 | wrapper (name : Nat) (child : Unary)

def value : Unary → Ty
 | .scalar base => .base base
 | .wrapper name child => nominal name [.inl (value child)]

def depth : Unary → Nat
 | .scalar _ => 0
 | .wrapper _ child => depth child + 1

def rootTag : Unary → CommonNominalFullDemand.Head
 | .scalar b => .base b
 | .wrapper name _ => .nominal name 1

theorem has_tag (t : Unary) : GeneralDictionaryInspectionHeads215.Tagged (value t) (rootTag t) := by
 cases t with
 | scalar b => exact tagged_scalar b
 | wrapper n child => exact tagged_nominal n [.inl (value child)]

theorem depth_invariant (a b : Unary) (same : Equivalent (value a) (value b)) :
 depth a = depth b := by
 induction a generalizing b with
 | scalar base =>
   cases b with
   | scalar => rfl
   | wrapper name child =>
     have clash := tag_subtype (has_tag (.scalar base)) (has_tag (.wrapper name child)) same.1
     cases clash
 | wrapper name child ih =>
   cases b with
   | scalar base =>
     have clash := tag_subtype (has_tag (.wrapper name child)) (has_tag (.scalar base)) same.1
     cases clash
   | wrapper name2 kid =>
     have related := (nominal_regular_invariant_exact ..).mp same.1
     have argument := related.2.2 0 _ _ rfl rfl
     exact congrArg Nat.succ (ih kid argument)

theorem same_origin (m : Assignment) (o : Origin) (a b : Unary)
 (first : At m .actual o (value a)) (last : At m .actual o (value b)) :
 depth a = depth b := by
 obtain ⟨x,seen⟩ := first.1
 have left := first.2 _ seen
 have right := last.2 _ seen
 exact depth_invariant a b ⟨subtype_trans left.2 right.1,subtype_trans right.2 left.1⟩

theorem decreases (state : State roles) (m : Assignment) (valid : Models state m)
 (a b : Origin) (shape : Unary) (known : At m .actual a (value shape)) (step : Edge state a b) :
 ∃ inner, At m .actual b (value inner) ∧ depth inner < depth shape := by
 obtain ⟨_live,test,i,head,rel⟩ := (GeneralRebaseOriginCongruence269.edge_normal state _ _).mp step
 obtain ⟨v,observed⟩ := known.1
 have found := (head m valid).2 _ observed
 have eqTag : rootTag shape = tag test := by
   have typeEq := known.2 _ observed
   exact tag_subtype (has_tag shape) (tagged_test test found) typeEq.2
 cases shape with
 | scalar base =>
   cases test with
   | scalar => exact Fin.elim0 i
   | nominal => cases eqTag
   | structural s => cases s <;> cases eqTag
 | wrapper name child =>
   cases test with
   | scalar => exact Fin.elim0 i
   | structural s => cases s <;> cases eqTag
   | nominal n count =>
     have nEq : name = n ∧ (1 : Nat) = count := CommonNominalFullDemand.Head.nominal.inj eqTag
     obtain ⟨rfl,rfl⟩ := nEq
     have part := project_value (.nominal name 1) (by trivial) (fun _ => value child) known i
     have matching := rel m valid
     refine ⟨child,⟨matching.2.1,?_⟩,Nat.lt_succ_self _⟩
     intro actual atDest
     obtain ⟨candidate,atChild⟩ := part.1
     have eq := matching.2.2 _ _ atChild atDest
     have concrete := part.2 _ atChild
     exact ⟨subtype_trans eq.2 concrete.1,subtype_trans concrete.2 eq.1⟩

theorem path_depth (state : State roles) (m : Assignment) (valid : Models state m)
 (path : Path state a b) (s : Unary) (known : At m .actual a (value s)) :
 ∃ inner, At m .actual b (value inner) ∧ depth inner ≤ depth s := by
 induction path generalizing s with
 | nil => exact ⟨s,known,Nat.le_refl _⟩
 | cons first _ ih =>
   obtain ⟨next,holds,smaller⟩ := decreases state m valid _ _ s known first
   obtain ⟨inner,found,endLess⟩ := ih next holds
   exact ⟨inner,found,Nat.le_trans endLess (Nat.le_of_lt smaller)⟩

theorem acyclic (state : State roles) (m : Assignment) (valid : Models state m)
 (o : Origin) (s : Unary) (known : At m .actual o (value s)) : ¬ Cyclic state o := by
 rintro ⟨⟨next,edge,path⟩,_⟩
 obtain ⟨part,here,strict⟩ := decreases state m valid _ _ s known edge
 obtain ⟨last,there,rest⟩ := path_depth state m valid path part here
 have same := same_origin m o s last known there
 omega

end Yulang.GeneralRebaseUnaryRank271
