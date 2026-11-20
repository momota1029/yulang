import Yulang.GeneralSourceRoleCstWire293

/-! Exact direct path transfer. Abbreviating known kinds cannot change
indices, and a successful compact path has a matching original wire node. -/
namespace Yulang.GeneralSourceRoleCstWirePaths293
open GeneralSourceRoleCstTree293 (Tree Path)
open GeneralSourceRoleCstWire293 (Wire Transfer TransferList decode decode_exact)
open GeneralSourceRoleCstPath293 (follow)
open GeneralSourceRoleCstSnapshot293 (Snapshot Address atAddress exportAt)
open GeneralSourceRoleTrack292 (Tracked)
open GeneralSourceMetadataExprDomain291 (bind_success)

def atWire : Path → Wire → Option Wire
  | [],w => some w
  | i::tail,.node _ cs => cs[i]?.bind (atWire tail)
  | _::_,.token _ _ => none

theorem transfer_index {ws : List Wire} {ts : List Tree}
    (mapped : TransferList ws ts) (i : Nat) (t : Tree) :
    ts[i]? = some t ↔ ∃ w, ws[i]? = some w ∧ Transfer w t := by
  induction i generalizing ws ts t with
  | zero =>
    cases mapped with
    | nil =>
      constructor
      · intro h; cases h
      · rintro ⟨_,h,_⟩; cases h
    | @cons w ws u us preserved rest =>
      constructor
      · intro found
        cases Option.some.inj found
        exact ⟨w,rfl,preserved⟩
      · rintro ⟨raw,read,ok⟩
        have eq : w = raw := Option.some.inj read
        subst raw
        have a := (decode_exact ..).mpr ok
        have b := (decode_exact ..).mpr preserved
        exact b.symm.trans a
  | succ i ih =>
    cases mapped with
    | nil =>
      constructor
      · intro h; cases h
      · rintro ⟨_,h,_⟩; cases h
    | cons h t => exact ih t _

theorem source_index {ws : List Wire} {ts : List Tree}
    (mapped : TransferList ws ts) (i : Nat) (w : Wire) (source : ws[i]? = some w) :
    ∃ t, ts[i]? = some t ∧ Transfer w t := by
  induction i generalizing ws ts w with
  | zero =>
    cases mapped with
    | nil => cases source
    | @cons front tail f t preserve rest =>
      cases Option.some.inj source
      exact ⟨f,rfl,preserve⟩
  | succ i ih =>
    cases mapped with
    | nil => cases source
    | cons preserve tail => exact ih tail w source

theorem transfer_path {wire : Wire} {root : Tree} (mapping : Transfer wire root)
    (path : Path) (t : Tree) :
    follow path root = some t ↔ ∃ w, atWire path wire = some w ∧ Transfer w t := by
  induction path generalizing wire root t with
  | nil =>
    constructor
    · intro h; cases Option.some.inj h; exact ⟨wire,rfl,mapping⟩
    · rintro ⟨w,picked,relation⟩
      cases Option.some.inj picked
      exact ((decode_exact ..).mpr mapping).symm.trans ((decode_exact ..).mpr relation)
  | cons i ps ih =>
    cases mapping with
    | token =>
      constructor
      · intro h; cases h
      · rintro ⟨w,bad,_⟩; cases bad
    | @node label k ws ts kOK children =>
      constructor
      · intro located
        obtain ⟨t0,selected,leaf⟩ := bind_success located
        obtain ⟨w0,source,transport⟩ := (transfer_index children i t0).mp selected
        obtain ⟨w,read,related⟩ := (ih transport t).mp leaf
        exact ⟨w,by simp [atWire,source,read],related⟩
      · rintro ⟨w,h,linked⟩
        obtain ⟨w0,source,fromThere⟩ := bind_success h
        obtain ⟨t0,seen,linkedHead⟩ := source_index children i w0 source
        have below := (ih linkedHead t).mpr ⟨w,fromThere,linked⟩
        simp [follow,seen,below]

def exportWire {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (brand : Brand) (root : Wire) (a : Address Brand) :
    Option (Tracked Scope (Address Brand)) :=
  (decode root).bind fun tree => exportAt scope ⟨brand,tree⟩ a

theorem export_wire_exact {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (brand : Brand) (wire : Wire) (a : Address Brand) (out : Tracked Scope (Address Brand)) :
    exportWire scope brand wire a = some out ↔
      ∃ t, Transfer wire t ∧ exportAt scope ⟨brand,t⟩ a = some out := by
  constructor
  · intro h
    obtain ⟨t,proof,exported⟩ := bind_success h
    exact ⟨t,(decode_exact ..).mp proof,exported⟩
  · rintro ⟨t,proof,exported⟩
    simp [exportWire,(decode_exact ..).mpr proof,exported]

end Yulang.GeneralSourceRoleCstWirePaths293
