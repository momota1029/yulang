import Yulang.GeneralDeclarativeI65I74InlineVariant458

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ClosedInlineField458
open Yulang.GeneralDeclarativeI65
open Core.PresenceGeneration (TyTerm)
open InlineVariant458 (Scoped ClosedTail checksScoped checksClosedTail scoped_sound458 scoped_complete458 tail_sound458 tail_complete458)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeGraphRows321 (fields)

def authoredFields : TyTerm Nat → Option (List (Nat × TyTerm Nat))
  | .emptyRecord => some []
  | .record label payload tail =>
    if checksScoped payload then
      (authoredFields tail).map fun fields =>
        (label,payload) :: fields.filter (fun row => decide (row.1 ≠ label))
    else none
  | _ => none

inductive ListsAuthoredFields : TyTerm Nat → List (Nat × TyTerm Nat) → Prop
  | empty : ListsAuthoredFields .emptyRecord []
  | field : Scoped payload → ListsAuthoredFields tail others →
    ListsAuthoredFields (.record label payload tail)
      ((label,payload)::others.filter (fun row => decide (row.1 ≠ label)))

theorem authoredFields_reflects458 {term fs} :
    authoredFields term = some fs ↔ ListsAuthoredFields term fs := by
  constructor
  · intro eq
    induction term generalizing fs <;> try (solve | cases eq)
    case emptyRecord =>
      cases Option.some.inj eq
      exact .empty
    case record label payload tail rest ih =>
      by_cases yes : checksScoped payload = true
      · cases read : authoredFields tail with
        | none => simp [authoredFields,yes,read] at eq
        | some parsed =>
          have same : fs = (label,payload)::parsed.filter (fun row => decide (row.1 ≠ label)) :=
            (Option.some.inj (by simpa [authoredFields,yes,read] using eq)).symm
          subst fs
          exact .field (scoped_sound458 yes) (ih read)
      · simp [authoredFields,yes] at eq
  · intro real
    induction real with
    | empty => rfl
    | field exact _ ih => simp [authoredFields,scoped_complete458 exact,ih]

theorem chosen_original_field_hides_its_later_shadow458 {l p tail fs} :
    ListsAuthoredFields (.record l p tail) fs →
    ∀ witness, (l,witness) ∈ fs ↔ witness = p := by
  intro actual
  cases actual with
  | field fixed exact =>
    intro witness
    simp [List.mem_filter]

/-- Mask payload names, not labels: retain exactly the normalized leftmost
spine. Native payloads may be inline and this does not manufacture a raw edge. -/
def rawFieldLabels (e : Expr) : Option (List Nat) :=
  (fields e).map (List.map Prod.fst)

def sourceFieldLabels (t : TyTerm Nat) : Option (List Nat) :=
  (authoredFields t).map (List.map Prod.fst)





theorem whole_closed_spine_preserves_visible_labels458 {t e}
    (legacy : RecordTrail455.closedRecordTerm t = some e) :
    rawFieldLabels e = sourceFieldLabels t := by
  induction t generalizing e <;> try (solve | cases legacy)
  case emptyRecord =>
    cases Option.some.inj legacy
    rfl
  case record l p tail hp ht =>
    cases p <;> try (solve | cases legacy)
    case var n =>
      cases st : RecordTrail455.closedRecordTerm tail with
      | none => simp [RecordTrail455.closedRecordTerm,st] at legacy
      | some rest =>
        have equ : e = .record l (.variable n) rest :=
          (Option.some.inj (by simpa [RecordTrail455.closedRecordTerm,st] using legacy)).symm
        subst e
        have labels := ht st
        cases raw : fields rest <;> cases source : authoredFields tail <;>
          simp [rawFieldLabels,sourceFieldLabels,raw,source] at labels
        · simp [rawFieldLabels,sourceFieldLabels,fields,authoredFields,raw,source,checksScoped]
        · simp [rawFieldLabels,sourceFieldLabels,fields,authoredFields,raw,source,checksScoped]
          change List.map Prod.fst (List.filter ((fun a : Nat => !decide (a = l)) ∘ Prod.fst) _) =
            List.map Prod.fst (List.filter ((fun a : Nat => !decide (a = l)) ∘ Prod.fst) _)
          rw [← List.filter_map, ← List.filter_map,labels]




open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessCycle350 (Link checksLink link)
open GeneralDeclarativeLowerKnown321 (Alias)
open RecordTrail455 (checkOriginalRoute original_route_iff_data455)
open InlineVariant458 (readOrdinaryPayload read_ordinary_payload_exact458 isNativeInline inline_not_a_named_pointer458)

/-- Only the selected actual field is linked. Other visible labels must agree
in order, but their payloads are not attributed to this produced report. -/
def OriginalInlineField (s : GeneralDeclarativeI65.State) (logical : Nat)
    (row : Equation) (label child : Nat) : Prop :=
  ∃ (words chosen : TyTerm Nat) (src : List (Nat × TyTerm Nat)) (raw : List (Nat × Nat)),
    ListsAuthoredFields words src ∧ fields row.right = some raw ∧
    raw.map Prod.fst = src.map Prod.fst ∧ (label,child) ∈ raw ∧ (label,chosen) ∈ src ∧
    (∀ n, chosen ≠ .var n) ∧
    ∃ parent ∈ s.origins, ∃ payload ∈ s.origins,
      parent.slot = row.left ∧ OriginRoute s parent logical ∧
      OriginRoute s payload child ∧ parent.issuer = payload.issuer ∧
      GeneralDeclarativeLowerKnown321.Alias s.current.ordinary child payload.slot ∧
      parent.endpoint = .ordinary words ∧ payload.endpoint = .ordinary chosen

structure FieldWire where
  owner : Nat
  payload : Nat
  fieldOrdinal : Nat
  edge : Link

def checkInlineField (s : GeneralDeclarativeI65.State) (logical : Nat)
    (row : Equation) (label child : Nat) (w : FieldWire) : Bool := ((do
  let raw ← fields row.right
  let parent ← s.origins[w.owner]?
  let payload ← s.origins[w.payload]?
  let words ← readOrdinaryPayload parent.endpoint
  let compiled ← authoredFields words
  let (originalLabel,sourceTerm) ← compiled[w.fieldOrdinal]?
  let payloadTerm ← readOrdinaryPayload payload.endpoint
  pure (decide (raw.map Prod.fst = compiled.map Prod.fst ∧ (label,child) ∈ raw ∧
      label = originalLabel ∧ parent.slot = row.left ∧ parent.issuer = payload.issuer ∧ sourceTerm = payloadTerm) &&
    isNativeInline sourceTerm && checkOriginalRoute s parent logical && checkOriginalRoute s payload child &&
    checksLink s.current.ordinary child payload.slot w.edge)) : Option Bool).getD false

theorem same_authorised_visible_inline_field_iff_finite_wire458 (s : GeneralDeclarativeI65.State)
    (logical : Nat) (row : Equation) (label child : Nat) :
    (∃ w, checkInlineField s logical row label child w = true) ↔
    OriginalInlineField s logical row label child := by
  constructor
  · rintro ⟨w,h⟩
    cases raw : fields row.right <;> simp [checkInlineField,raw,Option.bind] at h
    rename_i rs
    cases lhs : s.origins[w.owner]? <;> simp [lhs] at h
    rename_i parent
    cases rhs : s.origins[w.payload]? <;> simp [rhs] at h
    rename_i payload
    cases pWords : readOrdinaryPayload parent.endpoint <;> simp [pWords] at h
    rename_i words
    cases parsed : authoredFields words <;> simp [parsed] at h
    rename_i src
    cases entry : src[w.fieldOrdinal]? <;> simp [entry] at h
    rename_i item
    obtain ⟨key,t⟩ := item
    cases cWords : readOrdinaryPayload payload.endpoint <;> simp [cWords] at h
    rename_i childSyntax
    obtain ⟨⟨⟨⟨⟨skel,found,rfl,owner,issuer,rfl⟩,notVar⟩,parentRoute⟩,childRoute⟩,alias⟩ := h
    exact ⟨words,t,src,rs,authoredFields_reflects458.mp parsed,raw,skel,found,List.mem_of_getElem? entry,
      (inline_not_a_named_pointer458 _).mp notVar,parent,List.mem_of_getElem? lhs,payload,List.mem_of_getElem? rhs,
      owner,(original_route_iff_data455 ..).mp parentRoute,(original_route_iff_data455 ..).mp childRoute,
      issuer,link alias,read_ordinary_payload_exact458 pWords,read_ordinary_payload_exact458 cWords⟩
  · rintro ⟨words,chosen,src,raw,lexical,rawFound,labelList,fieldRaw,fieldAuth,inline,
      parent,hasP,payload,hasC,owner,pRoute,cRoute,issuer,alias,pTerm,cTerm⟩
    obtain ⟨i,atP⟩ := List.mem_iff_getElem?.mp hasP
    obtain ⟨j,atC⟩ := List.mem_iff_getElem?.mp hasC
    obtain ⟨k,atF⟩ := List.mem_iff_getElem?.mp fieldAuth
    obtain ⟨edge,actual⟩ := WhereSites450.alias_wire_from_actual_derivation450 alias
    exact ⟨⟨i,j,k,edge⟩,by simp [checkInlineField,rawFound,atP,atC,pTerm,cTerm,readOrdinaryPayload,
      authoredFields_reflects458.mpr lexical,atF,labelList,fieldRaw,owner,issuer,
      (inline_not_a_named_pointer458 _).mpr inline,(original_route_iff_data455 ..).mpr pRoute,
      (original_route_iff_data455 ..).mpr cRoute,actual,Option.bind]⟩



theorem chosen_visible_field_is_the_same_native_receipt_in_every_fit458
    {s logical row label child}
    (actual : OriginalInlineField s logical row label child) (m : I72.Model)
    (fit : GeneralDeclarativeI65.Fits s m) :
    ∃ words term payload, m.nativeSyntax row.left = some (.ordinary words) ∧
      m.nativeSyntax payload.slot = some (.ordinary term) ∧ OriginRoute s payload child ∧
      GeneralDeclarativeLowerKnown321.Alias s.current.ordinary child payload.slot := by
  obtain ⟨words,chosen,src,raw,valid,shape,skeleton,member,native,nonvar,parent,hasP,payload,hasC,
    owner,route,childRoute,issuer,edge,spelling,payloadSyntax⟩ := actual
  exact ⟨words,chosen,payload,by simpa only [owner,spelling] using fit.2 parent hasP,
    by simpa only [payloadSyntax] using fit.2 payload hasC,childRoute,edge⟩

end Yulang.GeneralDeclarativeI65.I72.ClosedInlineField458
