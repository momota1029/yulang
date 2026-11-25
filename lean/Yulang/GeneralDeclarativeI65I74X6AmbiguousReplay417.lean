import Yulang.GeneralDeclarativeI65I74X6AmbiguousRule417

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralNominalCenteredHeadMatExpressions (application)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralSourceMetadataFiniteLookup291 (get)
open Checker408 (Problem)
open List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410)
open PlainMerged416 (PlainRows PlainWire sourceX6)

def readCandidate417 (s : I72.State) (q : I72.Request) (ordinal : Nat) :
    Option (Candidate s q) := do
  let cur := s.core.current
  let roles := cur.environment.source.roles
  if valid : GeneralSourceMetadataRoles291.check roles = true then
    match original : get q.demand.role (GeneralSourceMetadataRoles291.index roles) with
    | none => none
    | some role =>
      match authored : (authoredRegistry cur).declarations[ordinal]? with
      | none => none
      | some d =>
        if found : d ∈ visible s.core q then
          if header : (GeneralDeclarativeWitnessModeCoverage357.checkDecl cur.environment d &&
               RecordK2412.header412 cur d) = true then
            if noBody : d.outputBinders = [] ∧ d.associated = [] ∧ d.requirements = [] then
              let indexed := GeneralSourceMetadataRoles291.indexed original
              let signature := GeneralDeclarativeWitnessSignature349.checked_signature
                (splitAnd (splitAnd (splitAnd header).2).1).1
              some ⟨d,ordinal,authored,found,⟨role,indexed.1,indexed.2⟩,
                (GeneralSourceMetadataRoles291.check_exact _).mp valid,
                (GeneralDeclarativeWitnessModeCoverage357.declaration_exact _ _).mp (splitAnd header).1,
                signature,noBody.1,noBody.2.1,noBody.2.2⟩
            else none
          else none
        else none
  else none

def readPlainHit417 {s q} (rows : PlainRows s q) (ordinal : Nat) : Option (PlainHit rows) := do
  let a ← readCandidate417 s q ordinal
  match literal : a.decl.head with
  | [.join (.variant firstTag (.var a₁)) (.variant secondTag (.var a₂))] =>
    if matchTag : firstTag = rows.tag ∧ secondTag = rows.tag ∧ a₁ ≠ a₂ then
      some ⟨a,a₁,a₂,matchTag.2.2,by simpa [sourceX6,matchTag.1,matchTag.2.1] using literal⟩
    else none
  | _ => none

def readIntegerOrigin417 {s q} (rows : PlainRows s q) (ordinal : Nat) :
    Option (IntegerOrigin rows) :=
  match authored : s.core.origins[ordinal]? with
  | none => none
  | some original =>
    match typed : original.endpoint with
    | .ordinary (.base .int) =>
      if position : original.slot = rows.payload then
        some ⟨original,List.mem_of_getElem? authored,position,typed⟩
      else none
    | _ => none

def readGroundHit417 {s q} (rows : PlainRows s q) (original : IntegerOrigin rows) (ordinal : Nat) :
    Option (GroundHit rows) := do
  let a ← readCandidate417 s q ordinal
  match literal : a.decl.head with
  | [.variant tag (.app name [])] =>
    if matched : tag = rows.tag then
      let cur := s.core.current
      match exactType : application (authoredRegistry cur).constructors
          (interpretation cur.environment.source.snapshot) name [] with
      | some (.primitive (.scalar .int) []) =>
        some ⟨a,name,original,by simpa [groundSyntax,matched] using literal,exactType⟩
      | _ => none
    else none
  | _ => none

structure AmbiguityWire where
  origin : Nat
  payloadOrigin : Nat
  variantRow : Nat
  intRow : Nat
  joinRow : Nat
  plainOrdinal : Nat
  groundOrdinal : Nat
  rootEscape : ExactEscapeWire
  payloadEscape : ExactEscapeWire

def replayAmbiguity417 (p : Problem) (w : AmbiguityWire) : Option (Ambiguous p.state p.root) := do
  let ord := p.state.core.current.ordinary
  let rows ← PlainMerged416.readRows416 p
    (⟨w.origin,w.variantRow,w.intRow,w.joinRow,w.plainOrdinal,w.rootEscape⟩ : PlainWire)
  let primitive ← readIntegerOrigin417 rows w.payloadOrigin
  let plain ← readPlainHit417 rows w.plainOrdinal
  let ground ← readGroundHit417 rows primitive w.groundOrdinal
  let registry := (authoredRegistry p.state.core.current).declarations
  if ordinals : (registry.map Declaration.id).Nodup ∧ plain.candidate.decl.id ≠ ground.candidate.decl.id ∧
      (visible p.state.core p.root = [plain.candidate.decl,ground.candidate.decl] ∨
       visible p.state.core p.root = [ground.candidate.decl,plain.candidate.decl]) then
    if gates : checkExactEscape ord rows.root w.rootEscape = true ∧
        checkExactEscape ord rows.payload w.payloadEscape = true ∧
        ord.equations.all (groundVariantAtRoot w.rootEscape rows.root rows.tag rows.payload) = true then
      some ⟨rows,plain,ground,ordinals.2.2,ordinals.2.1,
        ⟨fun _ => variant_profile_tracks_reached_child417 rows gates.1 gates.2.2,
         exact_escape_refutes_raw_root_K2410 gates.1,
         exact_escape_refutes_raw_root_K2410 gates.2.1⟩⟩
    else none
  else none

end Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417
