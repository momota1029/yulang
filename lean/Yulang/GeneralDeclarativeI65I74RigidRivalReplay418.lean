import Yulang.GeneralDeclarativeI65I74RigidRivalRule418

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RigidRival418
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralNominalCenteredHeadMatExpressions (application)
open GeneralSourceMetadataRows291 (interpretation)
open Checker408 (Problem)
open List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410)
open PlainMerged416 (PlainRows PlainWire)
open X6Ambiguous417 (readCandidate417 readIntegerOrigin417 readPlainHit417
  groundVariantAtRoot variant_profile_tracks_reached_child417)

def readStrRival418 {s q} (rows : PlainRows s q) (ordinal : Nat) :
    Option (Rival rows) := do
  let a ← readCandidate417 s q ordinal
  match literal : a.decl.head with
  | [.variant tag (.app name [])] =>
    if matched : tag = rows.tag then
      let cur := s.core.current
      match exactType : application (authoredRegistry cur).constructors
          (interpretation cur.environment.source.snapshot) name [] with
      | some (.primitive (.scalar .str) []) =>
        some ⟨a,name,by simpa [rivalHead418,matched] using literal,exactType⟩
      | _ => none
    else none
  | _ => none

structure RivalWire where
  origin : Nat
  payloadOrigin : Nat
  variantRow : Nat
  intRow : Nat
  joinRow : Nat
  plainOrdinal : Nat
  rivalOrdinal : Nat
  rootEscape : ExactEscapeWire
  payloadEscape : ExactEscapeWire

def replayWinner418 (p : Problem) (w : RivalWire) : Option (Winner p.state p.root) := do
  let ord := p.state.core.current.ordinary
  let rows ← PlainMerged416.readRows416 p
    (⟨w.origin,w.variantRow,w.intRow,w.joinRow,w.plainOrdinal,w.rootEscape⟩ : PlainWire)
  let primitive ← readIntegerOrigin417 rows w.payloadOrigin
  let plain ← readPlainHit417 rows w.plainOrdinal
  let ground ← readStrRival418 rows w.rivalOrdinal
  let registry := (authoredRegistry p.state.core.current).declarations
  if ordinals : (registry.map Declaration.id).Nodup ∧ plain.candidate.decl.id ≠ ground.candidate.decl.id ∧
      (visible p.state.core p.root = [plain.candidate.decl,ground.candidate.decl] ∨
       visible p.state.core p.root = [ground.candidate.decl,plain.candidate.decl]) then
    if gates : (p.state.core.origins.filter (fun o => o.slot == rows.payload)).length = 1 ∧
        checkExactEscape ord rows.root w.rootEscape = true ∧
        checkExactEscape ord rows.payload w.payloadEscape = true ∧
        ord.equations.all (groundVariantAtRoot w.rootEscape rows.root rows.tag rows.payload) = true then
      if noRaw : (⟨rows.root,rivalCode418 rows.tag⟩ : Equation) ∉ ord.equations ∧
          (⟨rows.payload,strNull⟩ : Equation) ∉ ord.equations then
        some ⟨rows,plain,⟨ground,primitive,gates.1⟩,ordinals.2.2,ordinals.2.1,
          ⟨fun _ => variant_profile_tracks_reached_child417 rows gates.2.1 gates.2.2.2,
           exact_escape_refutes_raw_root_K2410 gates.2.1,
           exact_escape_refutes_raw_root_K2410 gates.2.2.1⟩,⟨noRaw.1,noRaw.2⟩⟩
      else none
    else none
  else none

end Yulang.GeneralDeclarativeI65.I72.RigidRival418
