import Yulang.GeneralRebaseRecordReadback271

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRecordAlignment271
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Origin Observes shapeValue)
open GeneralNominalRecordInversion (record_shape)
open GeneralNominalOriginTerms (Same)
open GeneralRebaseRecordLookup271 (first exists_first)
open GeneralRebaseRecordIndices271 (Shadowed first_at index_visible)

def visibleSet (left right : List Nat) : Bool :=
 left.all (fun k => right.contains k) && right.all (fun k => left.contains k)

theorem visibleSet_exact (left right : List Nat) :
 visibleSet left right = true ↔ ∀ k, k ∈ left ↔ k ∈ right := by
 simp only [visibleSet,Bool.and_eq_true,List.all_eq_true,List.contains_iff_mem]
 exact ⟨fun ⟨lr,rl⟩ k => ⟨lr k,rl k⟩,fun known => ⟨fun k => (known k).mp,fun k => (known k).mpr⟩⟩

theorem map_first (labels : List Nat) (values : Nat → α) (key : Nat) :
 first key (labels.zip (labels.map values)) = if key ∈ labels then some (values key) else none := by
 induction labels with
 | nil => rfl
 | cons k rest ih =>
   by_cases eq : key = k
   · subst k
     simp [first]
   · simp [first,eq,ih]

def align (keys : List Nat) (xs : List Ty) (read : List Nat) : List Ty :=
 read.map (fun key => (first key (keys.zip xs)).getD .bottom)

theorem aligned (keys : List Nat) (xs : List Ty) (read : List Nat) (xLen : xs.length = keys.length)
 (sameSet : visibleSet keys read = true) :
 Equivalent (shapeValue (.record keys) xs) (shapeValue (.record read) (align keys xs read)) := by
 have newLen : (align keys xs read).length = read.length := List.length_map ..
 rw [record_shape keys xs xLen,record_shape read (align keys xs read) newLen]
 apply GeneralRebaseRecordOverwrite271.checked
 intro key
 unfold align
 rw [map_first]
 have inZip : key ∈ (keys.zip xs).map Prod.fst ↔ key ∈ read := by
   rw [List.map_fst_zip (Nat.le_of_eq xLen.symm)]
   exact (visibleSet_exact _ _).mp sameSet key
 cases table : first key (keys.zip xs) with
 | none =>
   have miss : key ∉ read := by
     intro has
     obtain ⟨value,entry⟩ := (exists_first _ _).mpr (inZip.mpr has)
     rw [table] at entry
     cases entry
   simp [miss]
 | some value =>
   have found := inZip.mp ((exists_first _ _).mp ⟨value,table⟩)
   simp [found]

theorem mapped_nth (keys : List Nat) (xs : List Ty) (read : List Nat)
 (i key : Nat) (value : Ty) (look : read[i]? = some key)
 (found : first key (keys.zip xs) = some value) :
 (align keys xs read)[i]? = some value := by
 unfold align
 rw [List.getElem?_map,look]
 simp [found]

theorem same_at (m : Assignment) (source target : Nat) (keys read : List Nat)
 (known : List Ty) (knownLen : known.length = keys.length)
 (eq : Equivalent (m source).1 (shapeValue (.record keys) known))
 (i j key : Nat) (measured : keys[i]? = some key) (located : read[j]? = some key)
 (layout : keys.Nodup) (visible : ¬ Shadowed read j key)
 (child : known[i]? = some (m target).1) (layoutSet : visibleSet keys read = true) :
 Same m (.structural (.source source) (.record read) j) (.source target) := by
 have all := aligned keys known read knownLen layoutSet
 have table := first_at keys known i key (m target).1 measured child (index_visible keys i key measured layout)
 have point : Observes m (.structural (.source source) (.record read) j) (m target).1 :=
   .structural (.source _) (List.length_map ..)
      ⟨subtype_trans eq.1 all.1,subtype_trans all.2 eq.2⟩ (mapped_nth keys known read j key _ located table)
 refine ⟨⟨_,point⟩,⟨_,.source _⟩,?_⟩
 intro a b event identified
 cases identified
 have same := GeneralRebaseRecordReadback271.visible_matches_canonical m source keys read known knownLen
   eq i j key measured located layout visible child event
 exact ⟨same.2,same.1⟩

end Yulang.GeneralRebaseRecordAlignment271
