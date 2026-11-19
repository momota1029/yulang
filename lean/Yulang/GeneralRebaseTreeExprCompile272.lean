import Yulang.GeneralRebaseTreeRecordBuild272
import Yulang.GeneralNominalCenteredHeadMatCompilerSemantics

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseTreeExprCompile272
open GeneralNominalMaterialization (Mode)
open GeneralNominalCenteredHeadMatExpressions (Expr primitiveValue)
open GeneralCandidateInspection (Primitive)
open CommonNominalFullCarrier
open GeneralRebaseFiniteTree272 (Tree value Canonical scalar)
open GeneralRebaseTreeConstructors272 (scalar_canonical pairTree pair_value pair_checked
 emptyTree empty_canonical variantTree variant_value variant_checked recordTree record_canonical record_value
 nominalTree nominal_value nominal_tree_canonical)
open GeneralRebaseTreeRecordBuild272 (appendField appendField_exact)
open GeneralNominalMatchedAssembly (Aligned)

abbrev Env := Mode → Nat → Option Tree
abbrev Variables := Mode → Nat → Ty
def Interprets (env : Env) (vars : Variables) : Prop :=
 ∀ mode id t, env mode id = some t → Canonical t ∧ Equivalent (vars mode id) (value t)

def primitive (p : Primitive) (args : List Tree) : Option Tree :=
 match p,args with
 | .scalar b,[] => some (scalar b)
 | .pair,[a,b] => some (pairTree a b)
 | .exactEmpty,[] => some emptyTree
 | .emptyRecord,[] => some (recordTree [] Fin.elim0)
 | _,_ => none

mutual
  def compile (env : Env) (mode : Mode) : Expr → Option Tree
    | .variable id => env mode id
    | .primitive p args => (many env mode args).bind (primitive p)
    | .nominal name args => (many env .actual args).map (nominalTree name)
    | .record label payload rest => do appendField label (← compile env mode payload) (← compile env mode rest)
    | .variant label payload => (compile env mode payload).map (variantTree label)
    | .join _ _ => none
  def many (env : Env) (mode : Mode) : List Expr → Option (List Tree)
    | [] => some []
    | first::rest => do pure ((← compile env mode first) :: (← many env mode rest))
end

theorem aligned_canonical (known : Aligned (fun (a : Ty) t => Canonical t ∧ Equivalent a (value t)) xs ys) :
 ∀ t ∈ ys, Canonical t := by
 induction known with
 | nil => intro _ absent; cases absent
 | cons one _ ih =>
   intro t member
   rcases List.mem_cons.mp member with rfl | tail
   · exact one.1
   · exact ih _ tail

theorem aligned_value (known : Aligned (fun (a : Ty) t => Canonical t ∧ Equivalent a (value t)) xs ys) :
 Aligned Equivalent xs (ys.map value) := by
 induction known with
 | nil => exact .nil
 | cons one _ ih => exact .cons one.2 ih

theorem primitive_sound (p : Primitive) (xs : List Ty) (ys : List Tree) (tree : Tree)
 (matched : Aligned (fun (a : Ty) t => Canonical t ∧ Equivalent a (value t)) xs ys)
 (hit : primitive p ys = some tree) : Canonical tree ∧ Equivalent (primitiveValue p xs) (value tree) := by
 unfold primitive at hit
 split at hit
 · rename_i b
   cases Option.some.inj hit
   cases matched
   exact ⟨scalar_canonical b,subtype_refl _,subtype_refl _⟩
 · rename_i first last
   cases Option.some.inj hit
   cases matched with
   | cons left tail =>
     cases tail with
     | cons right finish =>
       cases finish
       rw [pair_value]
       exact ⟨pair_checked _ _ left.1 right.1,
         (common_pair_iff ..).mpr ⟨left.2.1,right.2.1⟩,(common_pair_iff ..).mpr ⟨left.2.2,right.2.2⟩⟩
 · cases Option.some.inj hit
   cases matched
   exact ⟨empty_canonical,subtype_refl _,subtype_refl _⟩
 · cases Option.some.inj hit
   cases matched
   exact ⟨record_canonical [] (by simp) Fin.elim0 (fun i => Fin.elim0 i),subtype_refl _,subtype_refl _⟩
 · contradiction

mutual
  theorem compile_sound (env : Env) (vars : Variables) (honest : Interprets env vars) (mode : Mode)
      (expr : Expr) (t : Tree) (hit : compile env mode expr = some t) :
      Canonical t ∧ Equivalent (GeneralNominalCenteredHeadMatExpressions.value vars mode expr) (value t) := by
    cases expr with
    | «variable» id => exact honest mode id t hit
    | primitive p args =>
      cases found : many env mode args with
      | none => simp [compile,found] at hit
      | some children =>
        have known : primitive p children = some t := by simpa [compile,found] using hit
        exact primitive_sound p _ _ t (many_sound env vars honest mode args children found) known
    | nominal name args =>
      cases found : many env .actual args with
      | none => simp [compile,found] at hit
      | some children =>
        have eq : nominalTree name children = t := Option.some.inj (by simpa [compile,found] using hit)
        subst t
        have each := many_sound env vars honest .actual args children found
        refine ⟨nominal_tree_canonical name children (aligned_canonical each),?_⟩
        rw [nominal_value]
        simpa [GeneralNominalCenteredHeadMatExpressions.value,List.map_map,Function.comp_def] using
          (GeneralNominalCenteredHeadMatCompilerSemantics.nominal_congr name (aligned_value each))
    | record label leaf tail =>
      cases left : compile env mode leaf with
      | none => simp [compile,left,Bind.bind,Option.bind] at hit
      | some first =>
        cases endValue : compile env mode tail with
        | none => simp [compile,left,endValue,Bind.bind,Option.bind] at hit
        | some last =>
          have hitShape : appendField label first last = some t := by
            simpa [compile,left,endValue,Bind.bind,Option.bind] using hit
          have a := compile_sound env vars honest mode leaf first left
          have b := compile_sound env vars honest mode tail last endValue
          have combined := appendField_exact label first last t a.1 b.1 hitShape
          refine ⟨combined.1,?_⟩
          rw [combined.2]
          exact ⟨common_record_mono label a.2.1 b.2.1,common_record_mono label a.2.2 b.2.2⟩
    | variant tag body =>
      cases found : compile env mode body with
      | none => simp [compile,found] at hit
      | some tree =>
        have eq : variantTree tag tree = t := Option.some.inj (by simpa [compile,found] using hit)
        subst t
        have h := compile_sound env vars honest mode body tree found
        refine ⟨variant_checked tag tree h.1,?_⟩
        rw [variant_value]
        exact ⟨(common_variant_iff ..).mpr h.2.1,(common_variant_iff ..).mpr h.2.2⟩
    | join a b => cases hit
  theorem many_sound (env : Env) (vars : Variables) (honest : Interprets env vars) (mode : Mode)
      (exprs : List Expr) (ts : List Tree) (hit : many env mode exprs = some ts) :
      Aligned (fun (a : Ty) t => Canonical t ∧ Equivalent a (value t))
       (GeneralNominalCenteredHeadMatExpressions.values vars mode exprs) ts := by
    cases exprs with
    | nil =>
      cases Option.some.inj hit
      exact .nil
    | cons first rest =>
      cases one : compile env mode first with
      | none => simp [many,one,Bind.bind,Option.bind] at hit
      | some t =>
        cases two : many env mode rest with
        | none => simp [many,one,two,Bind.bind,Option.bind] at hit
        | some tail =>
          have eq : t :: tail = ts := Option.some.inj (by simpa [many,one,two,Bind.bind,Option.bind] using hit)
          subst ts
          exact .cons (compile_sound env vars honest mode first t one) (many_sound env vars honest mode rest tail two)
end

end Yulang.GeneralRebaseTreeExprCompile272
