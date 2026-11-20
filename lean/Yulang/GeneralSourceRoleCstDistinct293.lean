import Yulang.GeneralSourceRoleCstCoverage293

/-! Mixed ordinals separate exported occurrences even when spelling or byte
ranges coincide. The claim is only inside the same supplied snapshot. -/
namespace Yulang.GeneralSourceRoleCstDistinct293
open GeneralSourceRoleCstTree293
open GeneralSourceRoleCstBody293 (IsStatement)
open GeneralSourceRoleCstProducer293 (extract extract_exact)
open GeneralSourceRoleExport292 (Aligned)
open GeneralSourceRoleChildCoverage292 (Child)
open GeneralSourceRoleTrack292 (Tracked)

theorem indices_nodup (i : Nat) (children : List Tree) :
    ((indexedFrom i children).map Prod.fst).Nodup := by
  induction children generalizing i with
  | nil => simp [indexedFrom]
  | cons head tail ih =>
    rw [indexedFrom,List.map_cons,List.nodup_cons]
    refine ⟨?_,ih _⟩
    intro mem
    obtain ⟨⟨key,t⟩,there,eq⟩ := List.mem_map.mp mem
    obtain ⟨n,r,_⟩ := indexed_exact.mp there
    change key = i at eq
    omega

theorem significant_nodup (children : List Tree) :
    ((significant children).map Prod.fst).Nodup :=
  List.Nodup.sublist (List.filter_sublist.map Prod.fst) (indices_nodup 0 children)

theorem statement_slot {base : Path} {outer : Tree} {p : Path × Child}
    (read : IsStatement base outer p) : ∃ last, p.1 = base ++ [last] := by
  obtain ⟨_,i,_,_,_,site,_⟩ := read
  exact ⟨i,site⟩

theorem index_read {base : Path} {i : Nat} {outer : Tree} {p : Path × Child}
    (found : IsStatement (base ++ [i]) outer p) : p.1[base.length]? = some i := by
  obtain ⟨last,desc⟩ := statement_slot found
  rw [desc,List.append_assoc,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
  rfl

theorem unique_image_implies_unique {A B : Type} (f : A → B) (xs : List A)
    (cert : (xs.map f).Nodup) : xs.Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have one := List.nodup_cons.mp cert
    exact List.nodup_cons.mpr ⟨fun rep => one.1 (List.mem_map.mpr ⟨x,rep,rfl⟩),ih one.2⟩

theorem aligned_paths_unique (base : Path) (children : List Tree) (results : List (Path × Child))
    (items : Aligned (fun p => IsStatement (base ++ [p.1]) p.2) (significant children) results) :
    (results.map Prod.fst).Nodup := by
  have eq := GeneralSourceRoleUniqueSource292.aligned_images items
    (fun a => some a.1) (fun b => b.1[base.length]?) (fun _ _ witnessed => (index_read witnessed).symm)
  have outer : ((significant children).map (some ∘ Prod.fst)).Nodup := by
    rw [← List.map_map]
    exact (significant_nodup children).map some (fun _ _ diff same => diff (Option.some.inj same))
  apply unique_image_implies_unique (fun (p : Path) => p[base.length]?)
  rw [List.map_map]
  exact eq ▸ outer

theorem exported_paths_unique {Scope : Type} (scope : Scope) (site : Path) (t : Tree)
    (out : Tracked Scope Path) (ok : extract scope site t = some out) :
    (out.body.map Prod.fst).Nodup := by
  obtain ⟨head,j,n,ps,cs,p,headOK,scopeOK,address,headShape,all⟩ := (extract_exact ..).mp ok
  exact aligned_paths_unique (site ++ [j]) cs out.body all

end Yulang.GeneralSourceRoleCstDistinct293
