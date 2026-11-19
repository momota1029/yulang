import Yulang.GeneralRebaseCanonicalUniqueness272

namespace Yulang.GeneralRebaseFiniteTreeCode272
open GeneralNominalOriginTerms (arity)
open GeneralNominalRecursiveInspection (Test)
open GeneralRebaseFiniteTree272 (Tree)

deriving instance DecidableEq for Test

inductive Code where
 | node (test : Test) (children : List Code)

def encode : Tree → Code
 | .node t xs => .node t (List.ofFn fun i => encode (xs i))

theorem encode_get (xs : Fin n → Tree) (i : Fin n) :
 (List.ofFn (fun j => encode (xs j)))[i.val]? = some (encode (xs i)) := by
 rw [List.getElem?_ofFn]
 split
 · rfl
 · rename_i outside
   exact False.elim (outside i.isLt)

theorem injective : Function.Injective encode := by
 intro a
 induction a with
 | node test xs ih =>
   intro b same
   cases b with
   | node other ys =>
     have key : test = other :=
       (Code.node.inj (show Code.node test _ = Code.node other _ from same)).1
     subst other
     have parts : (List.ofFn (fun i => encode (xs i))) = List.ofFn (fun j => encode (ys j)) :=
       (Code.node.inj (show Code.node test _ = Code.node test _ from same)).2
     have every (i : Fin (arity test)) : xs i = ys i := by
       apply ih i
       have left := encode_get xs i
       have right := encode_get ys i
       rw [parts] at left
       exact Option.some.inj (left.symm.trans right)
     exact congrArg (Tree.node test) (funext every)

def same : Tree → Tree → Bool
 | .node t xs,.node u ys =>
   if h : t = u then (List.finRange (arity t)).all (fun i => same (xs i) (ys (h ▸ i)))
   else false

theorem same_exact (a b : Tree) : same a b = true ↔ a = b := by
 induction a generalizing b with
 | node t xs ih =>
   cases b with
   | node u ys =>
     change (if h : t = u then (List.finRange (arity t)).all
       (fun i => same (xs i) (ys (h ▸ i))) else false) = true ↔ _
     split
     · rename_i eq
       subst u
       constructor
       · intro seen
         have all := List.all_eq_true.mp seen
         exact congrArg (Tree.node t) (funext (fun i => (ih i _).mp (all i (List.mem_finRange _))))
       · intro identical
         have proved (i : Fin (arity t)) : xs i = ys i := by
           have children := (Tree.node.inj identical).2
           exact congrFun (eq_of_heq children) i
         exact List.all_eq_true.mpr (fun i _ => (ih i _).mpr (proved i))
     · rename_i different
       constructor
       · intro impossible; cases impossible
       · intro eq
         injection eq with head
         exact False.elim (different head)

end Yulang.GeneralRebaseFiniteTreeCode272
