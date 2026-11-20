import Yulang.GeneralSourceRoleCstTrivia293
import Yulang.GeneralSourceRoleCstSourceExtent293

/-! Two supplied mirrors differing in trivia. Declaration data are equal
after erasure, but mixed child paths and UTF-8 extents must be recomputed. -/
namespace Yulang.GeneralSourceRoleCstTriviaFixture293
open GeneralSourceRoleCstTree293 (Tree)
open GeneralSourceRoleCstFixture293 (ws head block required)
open GeneralSourceRoleCstLossless293 (documentedFile documentedMethod)
open GeneralSourceRoleCstSnapshot293 (Snapshot Address exportAt)
open GeneralSourceRoleCstSpan293 (locate)
open GeneralSourceRoleTrack292 (Tracked forget)
open GeneralSourceRoleCstShapes293 (toHead)

def shiftedRole : Tree :=
  .node .role [.token .pubKw "pub",ws,.token .roleKw "role",ws,head,ws,.token .colon ":",
    block required documentedMethod]

def shiftedFile : Tree := .node .root [ws,shiftedRole]
def first : Snapshot Nat := ⟨5,documentedFile⟩
def second : Snapshot Nat := ⟨6,shiftedFile⟩

def out (brand root body : Nat) : Tracked Unit (Address Nat) :=
  ⟨(),toHead "Index" ["'container","'key"],⟨brand,[root]⟩,
    [(⟨brand,[root,body,1,0]⟩,.typeDecl ⟨"value",false,.absent,true⟩),
      (⟨brand,[root,body,3,0]⟩,.other)]⟩

theorem reprojected_paths :
    exportAt () first ⟨5,[0]⟩ = some (out 5 0 6) ∧
    exportAt () second ⟨6,[1]⟩ = some (out 6 1 7) := ⟨rfl,rfl⟩

theorem erase_retains_same_unresolved_role :
    forget (out 5 0 6) = forget (out 6 1 7) := rfl

theorem extents_shift_by_utf8_width :
    (locate [0,6,1,0] documentedFile 0).map Prod.snd = some ⟨36,46⟩ ∧
    (locate [1,7,1,0] shiftedFile 0).map Prod.snd = some ⟨38,48⟩ :=
  ⟨rfl,rfl⟩

theorem stale_address_does_not_choose_shifted_role :
    exportAt () second ⟨5,[0]⟩ = none ∧ exportAt () second ⟨6,[0]⟩ = none :=
  ⟨rfl,rfl⟩

end Yulang.GeneralSourceRoleCstTriviaFixture293
