import Yulang.GeneralRebaseOriginExecutable269
import Yulang.GeneralRebaseVersionedK2Probe268

namespace Yulang.GeneralRebaseOriginEdgeScan269
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Edge Head Equal)
open GeneralNominalRecursiveInspection (Origin Test)
open GeneralNominalOriginTerms (arity project)
open GeneralRebaseOriginCongruence269 (edge_normal)
open GeneralRebaseOriginQuotient269 (TestsCover)
open GeneralRebaseOriginCycles268 (Window Sound)
open GeneralRebasePartialBool268 (Answer Reflect both)
open GeneralRebasePartialFinite268 (any any_sound transfer)
open GeneralRebaseVersionedK2Probe268 (indexed indexed_sound)

def scan (first target : Origin) (tests : List Test) (head : Test → Answer)
 (equal : Origin → Origin → Answer) : Answer :=
 both (equal first first) (any (fun test => both (head test)
   (indexed (fun index => equal (project first test index) target))) tests)

theorem scan_sound (state : State roles) (first target : Origin) (tests : List Test) (head : Test → Answer)
 (equal : Origin → Origin → Answer)
 (headSound : ∀ t ∈ tests, Reflect (Head state first t) (head t))
 (selfSound : Reflect (Equal state first first) (equal first first))
 (equalSound : ∀ t ∈ tests, ∀ i : Fin (arity t),
   Reflect (Equal state (project first t i) target) (equal (project first t i) target))
 (allHeads : ∀ t, Equal state first first → Head state first t → arity t ≠ 0 → t ∈ tests) :
 Reflect (Edge state first target) (scan first target tests head equal) := by
 apply transfer (p := Equal state first first ∧ ∃ t ∈ tests,
   Head state first t ∧ ∃ i : Fin (arity t), Equal state (project first t i) target)
 · rw [edge_normal]
   constructor
   · rintro ⟨seen,t,_,has,idx,matchAt⟩
     exact ⟨seen,t,idx,has,matchAt⟩
   · rintro ⟨seen,t,idx,has,matchAt⟩
     have pos : arity t ≠ 0 := fun zero => Nat.not_lt_zero idx.val (zero ▸ idx.isLt)
     exact ⟨seen,t,allHeads t seen has pos,has,idx,matchAt⟩
 · exact GeneralRebasePartialBool268.both_sound selfSound
     (any_sound _ _ _ (fun t onList => GeneralRebasePartialBool268.both_sound (headSound t onList)
       (indexed_sound _ _ (fun i => equalSound t onList i))))

def assemble (point : Fin n → Origin) (tests : Fin n → List Test) (head : Fin n → Test → Answer)
 (equal : Origin → Origin → Answer) (model : Answer) : Window n :=
 ⟨point,fun a b => scan (point a) (point b) (tests a) (head a) equal,model⟩

theorem assemble_sound (state : State roles) (point : Fin n → Origin) (tests : Fin n → List Test)
 (head : Fin n → Test → Answer) (equal : Origin → Origin → Answer) (model : Answer)
 (cover : TestsCover state point tests)
 (headSound : ∀ a t, t ∈ tests a → Reflect (Head state (point a) t) (head a t))
 (eqSound : ∀ a b, Reflect (Equal state a b) (equal a b))
 (modelSound : Reflect (∃ assn, Models state assn) model) :
 Sound state (assemble point tests head equal model) :=
 ⟨fun a _ => scan_sound state _ _ _ _ _ (headSound a) (eqSound _ _)
   (fun _ _ _ => eqSound _ _) (cover.allHeads a),modelSound⟩

end Yulang.GeneralRebaseOriginEdgeScan269
