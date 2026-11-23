import Yulang.GeneralDeclarativeI65NativePrefixCore377
import Yulang.GeneralDeclarativeI65CurrentRelease376
import Yulang.GeneralDeclarativeWitnessNativeRelease360
import Yulang.GeneralDeclarativeWitnessNativeOrder362
import Yulang.GeneralDeclarativeI65EarlyPorts369

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open CommonRecursiveNominalIntervals (Bounds Argument Endpoint effectiveParameter childContext)
open CommonDeclaredNominalInspection (Parameter)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralDeclarativeWitnessNativeInstall360 (World)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority ExactRelease)
open GeneralDeclarativeWitnessNativeValue360 (Write)
open GeneralDeclarativeWitnessNativeOrder362 (node)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Declaration)
open Core.PresenceGeneration (RowTerm)

/-- Actual source/release authorization is independent from whether the
candidate compares successfully. This is one positive supplier of
authority: a specific installed row at a complete granted address on
the same current ordinary state; not an inference from model values. -/
structure CurrentReleasedOrigin (s : State) (origin : Origin) where
  physicalWorld : World
  current : physicalWorld.ordinary = s.current.ordinary
  grantedAt : ReleaseAuthority
  exactWrite : Write
  opened : ExactRelease physicalWorld.board grantedAt exactWrite
  target : origin.slot = exactWrite.address.target
  author : origin.issuer = exactWrite.address.owner.path
  endpoint : origin.endpoint = node exactWrite.code

theorem authorized_origin_retains_actual_stamp {s : State} {o : Origin}
    (source : CurrentReleasedOrigin s o) :
    source.exactWrite.address ∈ source.grantedAt.grants ∧
    source.exactWrite.address.owner ∈ source.physicalWorld.board.active ∧
    source.opened.released.stored = source.exactWrite ∧
    o.endpoint = node source.opened.released.stored.code := by
  exact ⟨source.opened.released.granted,source.opened.released.active,source.opened.same,
    by rw [source.opened.same]; exact source.endpoint⟩

theorem current_release_actual_at_origin {s : State} {origin : Origin}
    (read : CurrentReleasedOrigin s origin) :
    GeneralDeclarativeWitnessNativeInstall360.atTarget read.physicalWorld.board origin.slot =
      some read.exactWrite := by
  have found := read.opened.released.located
  rw [read.opened.same] at found
  simpa only [read.target] using found

/-- Equality of the actual physical board and target identifies the
complete written row, not merely equivalent endpoint values. An
ordinary logical alias cannot replace either premise. -/
theorem same_native_board_slot_retains_write {s : State} {first last : Origin}
    (a : CurrentReleasedOrigin s first) (b : CurrentReleasedOrigin s last)
    (atBoard : a.physicalWorld.board = b.physicalWorld.board) (atSlot : first.slot = last.slot) :
    a.exactWrite = b.exactWrite := by
  have fromA := current_release_actual_at_origin a
  have fromB := current_release_actual_at_origin b
  rw [atBoard,atSlot] at fromA
  exact Option.some.inj (fromA.symm.trans fromB)

def originalOfWrite (written : Write) : Origin :=
  ⟨written.address.target,written.address.owner.path,node written.code⟩

/-- Just the existing exact release operation on one physical rail;
there is no other endpoint, candidate success or comparison argument. -/
def openedOriginalAtCurrent (s : State) (world : World)
    (sameCurrent : world.ordinary = s.current.ordinary)
    (table : ReleaseAuthority) (written : Write) :
    Option (CurrentReleasedOrigin s (originalOfWrite written)) :=
  (GeneralDeclarativeWitnessNativeRelease360.checkExactRelease world.board table written).map
    (fun proof => ⟨world,sameCurrent,table,written,proof,rfl,rfl,rfl⟩)

theorem original_read_alone_needs_release {s : State} {world : World}
    {sameCurrent : world.ordinary = s.current.ordinary}
    {table : ReleaseAuthority} {written : Write} {read : CurrentReleasedOrigin s (originalOfWrite written)}
    (made : openedOriginalAtCurrent s world sameCurrent table written = some read) :
    ∃ retained : ExactRelease world.board table written,
      GeneralDeclarativeWitnessNativeRelease360.checkExactRelease world.board table written =
        some retained := by
  unfold openedOriginalAtCurrent at made
  cases found : GeneralDeclarativeWitnessNativeRelease360.checkExactRelease world.board table written with
  | none => simp [found] at made
  | some proof => exact ⟨proof,rfl⟩


def endpointFromCurrentRelease {s : State} {origin : Origin} {logical : Nat}
    (released : CurrentReleasedOrigin s origin) (inTable : origin ∈ s.origins)
    (routed : OriginRoute s origin logical) :
    AuthorizedEndpoint s (fun o => Nonempty (CurrentReleasedOrigin s o)) logical :=
  ⟨origin,inTable,routed,⟨released⟩⟩


/-- A real authored install supplies one authorized original only when
the same-state source row and actual route already exist. This does not
start an inspection or turn a potential head into an actual visit. -/
theorem original_from_installed_and_retained_author {s : State} {logical : Nat}
    {env frame d layout table wire version}
    {p : GeneralDeclarativeWitnessNativePreparation360.Prepared env frame d layout}
    (emission : GeneralDeclarativeWitnessNativeValue360.Compiled p table wire version)
    {base : GeneralDeclarativeWitnessNativeInstall360.Board}
    {out : World}
    (ran : GeneralDeclarativeWitnessNativeInstall360.install p emission base = some out)
    {later : List Write}
    (disjoint : ∀ w ∈ later,emission.write.address.target ≠ w.address.target)
    (gate : ReleaseAuthority) (grant : emission.write.address ∈ gate.grants)
    (retained : originalOfWrite emission.write ∈ s.origins)
    (routed : OriginRoute s (originalOfWrite emission.write) logical) :
    Nonempty (AuthorizedEndpoint s (fun o => Nonempty (CurrentReleasedOrigin s o)) logical) := by
  have allowed := (emitted_row_remains_exactly_openable emission ran disjoint gate).mpr grant
  cases read : GeneralDeclarativeWitnessNativeRelease360.checkExactRelease
      (appendOtherWrites out.board later) gate emission.write with
  | none => simp [read] at allowed
  | some opened =>
    let actual : World := ⟨s.current.ordinary,appendOtherWrites out.board later⟩
    let backed : CurrentReleasedOrigin s (originalOfWrite emission.write) :=
      ⟨actual,rfl,gate,emission.write,opened,rfl,rfl,rfl⟩
    exact ⟨endpointFromCurrentRelease backed retained routed⟩

end Yulang.GeneralDeclarativeI65
