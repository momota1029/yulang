import Yulang.GeneralRebaseTreeInterpreter272

namespace Yulang.GeneralRebaseTreeCoverage272
open GeneralNominalRecursiveInspection (Origin)
open GeneralNormalizedObservation (Shape)
open GeneralRebaseFiniteTree272 (Tree)
open GeneralRebaseTreeReadbackState272 (Result decision)
open GeneralRebaseTreeInterpreter272 (Source run inspect)

theorem nominal_total (t : Tree) (name index : Nat) :
 GeneralRebaseTreeNominal272.fromTree name index t ≠ .unknown := by
 cases t with
 | node test kids =>
   cases test with
   | scalar _ | structural _ => intro bad; cases bad
   | nominal actual count =>
     change (if name = actual then if inside : index < count then
        Result.found (kids ⟨index,inside⟩) else Result.absent else Result.absent) ≠ Result.unknown
     split
     · split <;> intro bad <;> cases bad
     · intro bad; cases bad

theorem unequal_total (first last : Shape) (kids : Fin first.arity → Tree) (i : Nat) :
 GeneralRebaseTreeStructural272.unequal first kids last i ≠ .unknown := by
 cases first <;> cases last <;> try (intro bad; cases bad)
 exact GeneralRebaseTreeRecord272.total _ _ _ _

theorem structural_total (t : Tree) (goal : Shape) (i : Nat) :
 GeneralRebaseTreeStructural272.fromTree goal i t ≠ .unknown := by
 cases t with
 | node test kids =>
   cases test with
   | scalar _ | nominal _ _ => intro bad; cases bad
   | structural known =>
     change (if known = goal then if inside : i < known.arity then
       Result.found (kids ⟨i,inside⟩) else Result.absent
       else GeneralRebaseTreeStructural272.unequal known kids goal i) ≠ Result.unknown
     split
     · split <;> intro bad <;> cases bad
     · exact unequal_total known goal kids i

theorem nominal_unknown (r : Result) (name index : Nat) :
 GeneralRebaseTreeNominal272.step name index r = .unknown ↔ r = .unknown := by
 cases r with
 | unknown => exact ⟨fun _ => rfl,fun _ => rfl⟩
 | absent | many => constructor <;> intro bad <;> cases bad
 | found t =>
   exact ⟨fun h => False.elim (nominal_total t name index h),fun h => by cases h⟩

theorem structural_unknown (r : Result) (shape : Shape) (index : Nat) :
 GeneralRebaseTreeStructural272.step shape index r = .unknown ↔ r = .unknown := by
 cases r with
 | unknown => exact ⟨fun _ => rfl,fun _ => rfl⟩
 | absent => constructor <;> intro bad <;> cases bad
 | many =>
   change ((if index < shape.arity then Result.many else Result.absent) = Result.unknown) ↔ Result.many = Result.unknown
   split <;> constructor <;> intro bad <;> cases bad
 | found t =>
   exact ⟨fun h => False.elim (structural_total t shape index h),fun h => by cases h⟩

def rootSource : Origin → Nat
 | .source i => i
 | .nominal o _ _ | .structural o _ _ => rootSource o

theorem unknown_exact (source : Source) (origin : Origin) :
 run source origin = .unknown ↔ source (rootSource origin) = none := by
 induction origin with
 | source i =>
   cases hit : source i <;> simp [rootSource,run,hit]
 | nominal o n i ih => exact (nominal_unknown _ n i).trans ih
 | structural o s i ih => exact (structural_unknown _ s i).trans ih

theorem computable_coverage (source : Source) (o : Origin) :
 inspect source o = none ↔ source (rootSource o) = none := by
 rw [← unknown_exact source o]
 unfold inspect
 cases res : run source o <;> simp [decision]

theorem returns_negative (source : Source) (o : Origin) (supported : ∃ t, source (rootSource o) = some t) :
 inspect source o = some false := by
 obtain ⟨t,present⟩ := supported
 have known : run source o ≠ .unknown := by
   intro absent
   have miss := (unknown_exact _ _).mp absent
   rw [present] at miss
   cases miss
 unfold inspect
 cases r : run source o with
 | unknown => exact False.elim (known r)
 | absent | many | found _ => rfl

end Yulang.GeneralRebaseTreeCoverage272
