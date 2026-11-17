import Yulang.GeneralDictionaryLooseFamilyRevision240
set_option backward.isDefEq.respectTransparency false
/-! Uniform semantic raw-back half of retarget certification. The explicit
premise is inclusion of the actual lower-aggregate equations in ordinary atoms,
not the desired Models implication. Trusted-cache certification and reachable
journal induction remain separate obligations. -/
namespace Yulang.GeneralDictionaryLooseFamilyBack240
open GeneralDictionaryLooseFamilyBase240 GeneralDictionaryLooseFamilySnapshot240
open GeneralDictionaryLooseFamilyRefines240
open GeneralDictionaryLooseFamilyNames240 (lower)
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
variable (n : Nat) (allocated : List GeneralNominalIdentities.Origin)
 (reserved : List Nat) (ordinary : List (PresenceNormalForm.Atom Nat))

def HasLowerEquation : Prop :=
 GeneralNominalAllocation.equations (lower (n+1))
   (.union (.var (lower n)) (.var (lower n))) ⊆ ordinary

theorem lower_equal (included : HasLowerEquation n ordinary) (m : Assignment)
 (valid : GeneralNominalState.Models (snapshot (n+1) allocated reserved ordinary) m) :
 Equivalent (m (lower (n+1))).1 (m (lower n)).1 := by
 have equation := (GeneralNominalCaptureMerges.equations_exact ..).mp
   (fun atom member => valid.2.2 atom (included member))
 change Equivalent (m (lower (n+1))).1 (.union (m (lower n)).1 (m (lower n)).1) at equation
 have union : Equivalent (.union (m (lower n)).1 (m (lower n)).1) (m (lower n)).1 :=
   ⟨(common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩,
    (common_union_is_join _ _ _).mp (subtype_refl _) |>.1⟩
 exact ⟨subtype_trans equation.1 union.1,subtype_trans union.2 equation.2⟩

theorem zero_one (m : Assignment)
 (valid : GeneralNominalState.Models (snapshot (n+1) allocated reserved ordinary) m) : Equivalent (m 0).1 (m 1).1 := by
 have zero : Equivalent (m 0).1 (.base .int) :=
   ⟨valid.1.1 (.tyLe (.var (original (n+1) 0)) (.base .int)) (by exact List.mem_cons_self),
    valid.1.1 (.tyLe (.base .int) (.var (original (n+1) 0))) (by exact List.mem_cons_of_mem _ (List.mem_cons_self))⟩
 have one : Equivalent (m 1).1 (.base .int) :=
   ⟨valid.1.1 (.tyLe (.var (original (n+1) 1)) (.base .int)) (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    valid.1.1 (.tyLe (.base .int) (.var (original (n+1) 1))) (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))⟩
 exact ⟨subtype_trans zero.1 one.2,subtype_trans one.1 zero.2⟩

theorem point_fit_change (m : Assignment) (a b : Fin ((n+1)+5)) (value : Argument)
 (equal : Equivalent (m (source (n+1) a)).1 (m (source (n+1) b)).1)
 (fits : GeneralNominalState.Fits (base (n+1)) m (.type (a,original (n+1) 4)) value) :
 GeneralNominalState.Fits (base (n+1)) m (.type (b,original (n+1) 4)) value := by
 cases value with
 | inr => cases fits
 | inl value => exact ⟨subtype_trans equal.2 fits.1,fits.2⟩

theorem pair_fits (m : Assignment) (a b : Fin ((n+1)+5)) (values : List Argument)
 (equal : Equivalent (m (source (n+1) a)).1 (m (source (n+1) b)).1)
 (fits : GeneralNominalState.FitsAll (base (n+1)) m [.type (a,original (n+1) 4),.type (a,original (n+1) 4)] values) :
 GeneralNominalState.FitsAll (base (n+1)) m [.type (b,original (n+1) 4),.type (b,original (n+1) 4)] values := by
 cases fits with
 | cons one tail =>
   cases tail with
   | cons two tail =>
     cases tail
     exact .cons (point_fit_change n m a b _ equal one) (.cons (point_fit_change n m a b _ equal two) .nil)

theorem raw_back (included : HasLowerEquation n ordinary) (m : Assignment)
 (valid : GeneralNominalState.Models (snapshot (n+1) allocated reserved ordinary) m) :
 GeneralNominalState.Models (state n allocated reserved ordinary) m := by
 refine ⟨valid.1,?_,valid.2.2⟩
 intro slot descriptor found
 change (if slot.val=n+5 then some (looseDescriptor n) else if slot.val=3 then some (rootDescriptor n) else
   if slot.val=2 ∨ 4 ≤ slot.val then some (foo (n+1)) else none) = some descriptor at found
 split at found
 · rename_i last
   cases Option.some.inj found
   have fooFound : (snapshot (n+1) allocated reserved ordinary).nominals slot = some (foo (n+1)) := by
     have notThree : slot.val≠3 := by omega
     have yes : slot.val=2 ∨ 4 ≤ slot.val := Or.inr (by omega)
     simp only [snapshot,notThree,yes,ite_false,ite_true]
   obtain ⟨values,fits,meaning⟩ := valid.2.1 slot _ fooFound
   change GeneralNominalState.FitsAll (base (n+1)) m [.type (original (n+1) 0,original (n+1) 0)] values at fits
   cases fits with
   | @cons _ a _ rest one tail =>
     cases tail
     cases a with
     | inr => cases one
     | inl a =>
       have equal := zero_one n allocated reserved ordinary m valid
       refine ⟨[.inl a],.cons ?_ .nil,meaning⟩
       exact ⟨one.1,subtype_trans one.2 equal.1⟩
 · split at found
   · rename_i three
     cases Option.some.inj found
     have pairFound : (snapshot (n+1) allocated reserved ordinary).nominals slot = some (GeneralDictionaryLooseFamilyBase240.pair (n+1)) := by simp only [snapshot,three,ite_true]
     obtain ⟨values,fits,meaning⟩ := valid.2.1 slot _ pairFound
     have equal : Equivalent (m (source (n+1) (anchor (n+1)))).1 (m (source (n+1) (embed n (anchor n)))).1 := by
       rw [source_anchor,source_embed,source_anchor]
       exact lower_equal n allocated reserved ordinary included m valid
     exact ⟨values,pair_fits n m _ _ values equal fits,meaning⟩
   · rename_i notThree
     split at found
     · rename_i yes
       cases Option.some.inj found
       exact valid.2.1 slot _ (by simp only [snapshot,notThree,yes,ite_false,ite_true])
     · cases found
end Yulang.GeneralDictionaryLooseFamilyBack240
