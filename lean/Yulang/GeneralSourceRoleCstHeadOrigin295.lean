import Yulang.GeneralSourceRoleCstNamingPacketFixture295

/-! Trace the selected role head and its exact binder spellings back to
the raw direct mixed child from which the existing producer read it. -/
namespace Yulang.GeneralSourceRoleCstHeadOrigin295
open GeneralSourceRoleCstTree293 (Tree Path significant significant_exact)
open GeneralSourceRoleCstProducer293 (roleParts dropVisibility)
open GeneralSourceRoleCstPath293 (follow follow_append drop_subset)
open GeneralSourceRoleCstWire293 (Wire Transfer)
open GeneralSourceRoleCstWirePaths293 (atWire transfer_path)
open GeneralSourceRoleCstShapes293 (toHead)
open GeneralSourceRoleCstRustHead293 (ActualHead)
open GeneralSourceRoleCstSnapshot293 (Address mark)
open GeneralSourceRoleCstSelectedSeal295 (Selection select)
open GeneralSourceRoleCstSealOrigin295 (kept_export)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleTrack292 (Tracked)

theorem head_at_ordinal {root head body : Tree} {b : Nat}
    (parts : roleParts root = some (head,b,body)) :
    ∃ i, follow [i] root = some head := by
  cases root with
  | token => cases parts
  | node k cs =>
    cases k <;> try cases parts
    change (match dropVisibility (significant cs) with
      | [(_, .token .roleKw _), (_,node), (_, .token .colon _), tail] => some (node,tail)
      | _ => none) = some (head,b,body) at parts
    generalize L : dropVisibility (significant cs) = xs at parts
    split at parts
    · rename_i _ kw txt j picked col colText rest
      have e : picked = head := congrArg Prod.fst (Option.some.inj parts)
      have present : (j,picked) ∈ dropVisibility (significant cs) := by rw [L]; simp
      have located := (significant_exact.mp (drop_subset present)).1
      exact ⟨j,by simp [follow,located,e]⟩
    · cases parts

theorem selected_head_from_original {S B : Type} [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (packet : Selection B) (p : Tracked S (Address B))
    (picked : select policy scope w brand a packet = some p) :
    p.scope = scope ∧ ∃ i raw head name params,
      atWire (a.path ++ [i]) w = some raw ∧ Transfer raw head ∧
        ActualHead head name params ∧ p.head = toHead name params := by
  obtain ⟨root,converted,exported⟩ := kept_export policy scope w brand a packet p picked
  obtain ⟨_,role,payload,followRole,extracted,rfl⟩ :=
    (GeneralSourceRoleCstRustSnapshot293.export_exact ..).mp exported
  obtain ⟨head,i,name,args,cs,parts,headOK,tag,_,shape,_⟩ :=
    (GeneralSourceRoleCstRustRole293.extract_exact ..).mp extracted
  obtain ⟨j,found⟩ := head_at_ordinal parts
  have locate : follow (a.path ++ [j]) root = some head := by
    rw [follow_append,followRole,Option.bind_some,found]
  obtain ⟨raw,fromWire,tie⟩ := (transfer_path converted _ _).mp locate
  exact ⟨tag,j,raw,head,name,args,fromWire,tie,headOK,shape⟩

end Yulang.GeneralSourceRoleCstHeadOrigin295
