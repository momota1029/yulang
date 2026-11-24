import Yulang.GeneralDeclarativeI65DeriveCompoundOutput394
import Yulang.GeneralDeclarativeI65Selection367
import Yulang.GeneralDeclarativeProducedNames325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (All₂)
open CommonDeclaredNominalInspection (Kind)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarations (Declaration Equation)
open GeneralDeclarativeEmissionForest322 (Placement)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeOutputs320 (bodyPattern)

def Binding.name395 : Binding → Nat
  | .value n .. | .row n .. => n

def Binding.kind395 : Binding → Kind
  | .value .. => .value
  | .row .. => .row

/-- The original head position and the leaf's ordinal inside that
particular observed read. An ordinary head or an unused native slot
does not synthesize a native binding. -/
inductive NativeHeadLeaf395 (s : State) (capture : Nat → Capture) :
    {args : List Capture} → {pats : List Pattern} →
    All₂ (DeepHead s capture) args pats → Nat → Nat → Binding → Prop where
  | here {read : ModeWindow s arg pat}
      (deep : DeepRead s capture false (normalize pat) read.lower.endpoint read.upper.endpoint found)
      (atLeaf : found[j]? = some leaf)
      {later : All₂ (DeepHead s capture) as ps} :
      NativeHeadLeaf395 s capture (.cons (.declared read deep) later) 0 j leaf
  | later {later : All₂ (DeepHead s capture) as ps} {earlier : DeepHead s capture arg pat} :
      NativeHeadLeaf395 s capture later i j leaf →
      NativeHeadLeaf395 s capture (.cons earlier later) (i+1) j leaf

theorem native_head_leaf_source395 {s capture args pats}
    {read : All₂ (DeepHead s capture) args pats} {i j leaf}
    (found : NativeHeadLeaf395 s capture read i j leaf) :
    Binding.Source s capture leaf := by
  induction found with
  | here deep atLeaf => exact deep_reads_retain_all_sources deep _ (List.mem_of_getElem? atLeaf)
  | later _ ih => exact ih

theorem Binding.mark_typed395 {s capture leaf}
    (h : Binding.Source s capture leaf) :
    TypedBodyCapture392 s (capture leaf.name395) leaf.kind395 := by
  cases leaf with
  | value n a b => exact .value h
  | row n a b => exact .row h

/-- The actual visible row and the original ordered observation
remain fixed. Neither an event nor an output selects this row. -/
inductive HeadOrigin395 (s : State) (q : Request) (row : Declaration) :
    SourceHead s q row → (Nat → Capture) → Nat → Nat → Binding → Prop where
  | ordered {read : All₂ (DeepHead s capture) q.demand.arguments row.head} :
      NativeHeadLeaf395 s capture read i j leaf →
      HeadOrigin395 s q row (.ordered capture read) capture i j leaf

theorem head_origin_has_kind395 {s q row head capture i j leaf}
    (h : HeadOrigin395 s q row head capture i j leaf) :
    TypedBodyCapture392 s (capture leaf.name395) leaf.kind395 := by
  cases h with
  | ordered source => exact Binding.mark_typed395 (native_head_leaf_source395 source)

private theorem lookup_map_present395 (names : List Nat) (values : Nat → Capture)
    (key : Nat) (seen : key ∈ names) :
    (names.map fun n => (n, values n)).lookup key = some (values key) := by
  induction names with
  | nil => simp at seen
  | cons first rest ih =>
    by_cases equal : first = key
    · subst first
      simp
    · have remains := (List.mem_cons.mp seen).resolve_left (Ne.symm equal)
      have neq : (key == first) = false := beq_eq_false_iff_ne.mpr (Ne.symm equal)
      simp only [List.map_cons,List.lookup,neq,ih remains]

theorem explicit_authored_head_slot395 {s q} (frame : AuthoredBodyFrame393 s q)
    (separate : frame.decl.OutputOnly) {body : Equation}
    (name : Nat) (used : name ∈ frame.decl.inputNames) :
    frame.slots (.explicit body) name = some (frame.input name) := by
  have notOutput : name ∉ frame.decl.outputNames :=
    fun output => separate.1 name output
      (GeneralPatternVariableProvenance.normalize_args_variables frame.decl.head used)
  unfold AuthoredBodyFrame393.slots AuthoredBodyFrame393.captures
  rw [lookup_map_present395 _ _ _ (List.mem_append_left _ used)]
  unfold AuthoredBodyFrame393.names GeneralDeclarativeFrameReadback325.sourceNames
    GeneralDeclarativeProducedNames325.table
  simp [notOutput]

theorem deep_leaf_name_is_in_pattern395 {s capture c pat lo hi found}
    (read : DeepRead s capture c pat lo hi found) :
    ∀ b ∈ found, b.name395 ∈ pat.variables := by
  exact DeepRead.rec
    (motive_1 := fun _ p _ _ bs _ => ∀ b ∈ bs, b.name395 ∈ p.variables)
    (motive_2 := fun _ _ ps _ _ bs _ => ∀ b ∈ bs, b.name395 ∈ GeneralDeclarationPatterns.variablesArgs ps)
    (motive_3 := fun _ _ p _ _ bs _ => ∀ b ∈ bs, b.name395 ∈ p.variables)
    (fun _ b member => by
      cases List.mem_singleton.mp member
      simp [Binding.name395,Pattern.variables])
    (fun _ _ _ _ args b member => by simpa only [Pattern.variables] using args b member)
    (fun _ h => False.elim (List.not_mem_nil h))
    (fun _ _ a t b h => by
      rcases List.mem_append.mp h with l | r
      · exact List.mem_append_left _ (a _ l)
      · exact List.mem_append_right _ (t _ r))
    (fun _ h => h)
    (fun _ h => h)
    (fun _ _ a b leaf h => (List.mem_append.mp h).elim (a leaf) (b leaf))
    (fun _ _ h => False.elim (List.not_mem_nil h))
    (fun _ b member => by
      cases List.mem_singleton.mp member
      simp [Binding.name395,Pattern.variables])
    (fun _ b member => by
      cases List.mem_singleton.mp member
      simp [Binding.name395,Pattern.variables])
    (fun _ _ b member => by
      rcases List.mem_cons.mp member with h | h
      · cases h
        simp [Binding.name395,Pattern.variables]
      · cases List.mem_singleton.mp h
        simp [Binding.name395,Pattern.variables])
    (fun _ _ h => False.elim (List.not_mem_nil h))
    read

theorem native_leaf_is_lexical395 {s capture args pats}
    {read : All₂ (DeepHead s capture) args pats} {i j leaf}
    (h : NativeHeadLeaf395 s capture read i j leaf) :
    leaf.name395 ∈ GeneralDeclarationPatterns.variablesArgs (GeneralDeclarationPatterns.normalizeArgs pats) := by
  induction h with
  | here deep position =>
    exact List.mem_append_left _
      (deep_leaf_name_is_in_pattern395 deep _ (List.mem_of_getElem? position))
  | later _ always => exact List.mem_append_right _ always

theorem native_origin_is_lexical395 {s q row head capture i j leaf}
    (h : HeadOrigin395 s q row head capture i j leaf) :
    leaf.name395 ∈ row.inputNames := by
  cases h with
  | ordered h => exact native_leaf_is_lexical395 h

/-- Indexed read of a real named binder, after the selected frame
keeps that original input. The body need not already have an RHS. -/
def ordered_head_ticket395 {s q row} {head : SourceHead s q row} {capture i j leaf}
    (found : HeadOrigin395 s q row head capture i j leaf)
    (frame : AuthoredBodyFrame393 s q) (sameRow : frame.decl = row)
    (sameInput : frame.input = capture) (separate : row.OutputOnly)
    (body : Equation) :
    BindingTicket394 s (frame.slots (.explicit body)) leaf.name395 leaf.kind395 := by
  refine ⟨capture leaf.name395, ?_, head_origin_has_kind395 found⟩
  rw [← sameInput]
  exact explicit_authored_head_slot395 frame (sameRow ▸ separate) _
    (sameRow ▸ native_origin_is_lexical395 found)

/-- Positional refinement of Stores. Equal declaration bodies at
different registry positions do not let this proof jump between rows. -/
inductive StoredAt395 {s : State} {q : Request} :
    {rows : List Declaration} → CandidateTape s q rows →
    {row : Declaration} → AuthoredCandidate s q row → Nat → Prop where
  | here (pick : AuthoredCandidate s q row) (rest : CandidateTape s q rows) :
      StoredAt395 (.next (.matched pick) rest) pick 0
  | later (status : Assessment s q row) {rest : CandidateTape s q rows} :
      StoredAt395 rest pick i → StoredAt395 (.next status rest) pick (i+1)

theorem actual_stored_at395 {s q rows row} {t : CandidateTape s q rows}
    {pick : AuthoredCandidate s q row} (hit : Stores t pick) :
    ∃ i, StoredAt395 t pick i := by
  induction hit with
  | here c rest => exact ⟨0,.here c rest⟩
  | later status _ ih =>
    obtain ⟨i,atI⟩ := ih
    exact ⟨i+1,.later status atI⟩

theorem stored_at_has_original_row395 {s q rows row} {t : CandidateTape s q rows}
    {pick : AuthoredCandidate s q row} {i} (hit : StoredAt395 t pick i) :
    rows[i]? = some row := by
  induction hit with
  | here => rfl
  | later _ _ ih => simpa using ih

def unfilterOrdinal395 {α : Type} (test : α → Bool) : List α → Nat → Option Nat
  | [], _ => none
  | first :: rest, i =>
    if test first then
      match i with
      | 0 => some 0
      | i+1 => (unfilterOrdinal395 test rest i).map Nat.succ
    else (unfilterOrdinal395 test rest i).map Nat.succ

theorem unfilterOrdinal395_exact {α : Type} (test : α → Bool) (xs : List α)
    (i : Nat) {row : α} (seen : (xs.filter test)[i]? = some row) :
    ∃ j, unfilterOrdinal395 test xs i = some j ∧ xs[j]? = some row := by
  induction xs generalizing i with
  | nil => simp at seen
  | cons first rest ih =>
    cases positive : test first with
    | false =>
      have hit : (rest.filter test)[i]? = some row := by simpa [positive] using seen
      obtain ⟨j,atJ,value⟩ := ih i hit
      exact ⟨j+1,by simp [unfilterOrdinal395,positive,atJ],by simpa using value⟩
    | true =>
      cases i with
      | zero =>
        have equal : first = row := by simpa [positive] using seen
        exact ⟨0,by simp [unfilterOrdinal395,positive],by simp [equal]⟩
      | succ i =>
        have hit : (rest.filter test)[i]? = some row := by simpa [positive] using seen
        obtain ⟨j,atJ,value⟩ := ih i hit
        exact ⟨j+1,by simp [unfilterOrdinal395,positive,atJ],by simpa using value⟩

/-- The frame is manufactured from the exact index of the actual
selected head and the real declaration placement, rather than
decoded from an event or an already emitted typed vector. -/
def frameAtSource395 {s q row} (visibleIn : row ∈ visible s q)
    (j : Nat) (authored : (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.current).declarations[j]? = some row)
    (placement : Placement) (capture : Nat → Capture) : AuthoredBodyFrame393 s q :=
  ⟨j,row,authored,visibleIn,placement,capture⟩

theorem actual_selected_head_has_registry_ordinal395 {s q row}
    {t : CandidateTape s q (visible s q)} (only : TapedMatch s q t row) :
    ∃ (pick : AuthoredCandidate s q row) (i j : Nat),
      StoredAt395 t pick i ∧
      unfilterOrdinal395 (fun row : Declaration => row.role == q.demand.role)
        (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.current).declarations i = some j ∧
      (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.current).declarations[j]? = some row := by
  obtain ⟨pick,stored⟩ := actual_matched_row only
  obtain ⟨i,hit⟩ := actual_stored_at395 stored
  obtain ⟨j,ordinal,entered⟩ := unfilterOrdinal395_exact _ _ i (stored_at_has_original_row395 hit)
  exact ⟨pick,i,j,hit,ordinal,entered⟩

/-- A lookup certificate carries a real native source occurrence
and its original kind, not a claim about what the output must be. -/
def ActualHeadBinding395 {s q row} (head : SourceHead s q row)
    (capture : Nat → Capture) (name : Nat) (kind : Kind) : Prop :=
  ∃ i j leaf, HeadOrigin395 s q row head capture i j leaf ∧ leaf.name395 = name ∧ leaf.kind395 = kind

noncomputable def readHeadBinding395 {s q row} (head : SourceHead s q row)
    (capture : Nat → Capture) (j : Nat)
    (authored : (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.current).declarations[j]? = some row)
    (visibleIn : row ∈ visible s q) (place : Placement)
    (separate : row.OutputOnly) (body : Equation) (name : Nat) (kind : Kind) :
    Option (BindingTicket394 s ((frameAtSource395 visibleIn j authored place capture).slots (.explicit body)) name kind) := by
  classical
  exact if existsLeaf : ActualHeadBinding395 head capture name kind then
    some ⟨capture name, by
      obtain ⟨_,_,_,seen,equal,_⟩ := existsLeaf
      exact explicit_authored_head_slot395 _ separate name (equal ▸ native_origin_is_lexical395 seen),
      by
        obtain ⟨_,_,_,seen,equal,sameKind⟩ := existsLeaf
        exact equal ▸ sameKind ▸ head_origin_has_kind395 seen⟩
  else none

noncomputable def readOriginalSelectedHead395 {s q row} (head : SourceHead s q row)
    (capture : Nat → Capture) (j : Nat)
    (authored : (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.current).declarations[j]? = some row)
    (visibleIn : row ∈ visible s q) (place : Placement)
    (separate : row.OutputOnly) (body : Equation) :
    SourceBindingReads394 s ((frameAtSource395 visibleIn j authored place capture).slots (.explicit body)) :=
  ⟨fun n => readHeadBinding395 head capture j authored visibleIn place separate body n .value,
   fun n => readHeadBinding395 head capture j authored visibleIn place separate body n .row⟩

theorem readHeadBinding395_present_exact {s q row} {head : SourceHead s q row}
    {capture : Nat → Capture} {j : Nat}
    {authored : (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.current).declarations[j]? = some row}
    {visibleIn : row ∈ visible s q} {place : Placement} {separate : row.OutputOnly} {body : Equation}
    {name : Nat} {kind : Kind} :
    (readHeadBinding395 head capture j authored visibleIn place separate body name kind).isSome = true ↔
      ActualHeadBinding395 head capture name kind := by
  classical
  by_cases witnessed : ActualHeadBinding395 head capture name kind
  · simp [readHeadBinding395,witnessed]
  · simp [readHeadBinding395,witnessed]

/-- Default and where-produced binders are outside this head-only
adapter. Absence is not a classifier answer. Old role-position
default reads must be supplied independently. -/
noncomputable def selectedHeadBodyReads395 {s q row} (head : SourceHead s q row)
    (capture : Nat → Capture) (j : Nat)
    (authored : (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.current).declarations[j]? = some row)
    (visibleIn : row ∈ visible s q) (place : Placement) (separate : row.OutputOnly)
    (body : Body) :
    SourceBindingReads394 s ((frameAtSource395 visibleIn j authored place capture).slots body) :=
  match body with
  | .explicit eq => readOriginalSelectedHead395 head capture j authored visibleIn place separate eq
  | .default .. => ⟨fun _ => none,fun _ => none⟩

noncomputable def deriveOutputFromActualHead395 {s q row} (head : SourceHead s q row)
    (capture : Nat → Capture) (j : Nat)
    (authored : (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.current).declarations[j]? = some row)
    (visibleIn : row ∈ visible s q) (place : Placement) (separate : row.OutputOnly)
    (ord : Fin q.demand.outputs.length) (unique : (row.associated.map Equation.name).Nodup) :
    Option (OriginalCompoundOutput394 (frameAtSource395 visibleIn j authored place capture) ord) :=
  deriveOriginalCompoundOutput394 _ ord unique
    (selectedHeadBodyReads395 head capture j authored visibleIn place separate)

/-- Kept separately from source typing: the established literal projection
writes precisely the original target, if it is defined for this code. -/
theorem projected_native_target395 {target : Nat} {rhs : SourceRhsCode394} {write : LiteralWriteSyntax}
    (p : projectOldNativeLiteral394 target rhs = some write) :
    ∃ bodySyntax args, write = .declared target bodySyntax args := by
  cases rhs with
  | «variable» | record | join => simp [projectOldNativeLiteral394] at p
  | variant tag body =>
    cases body with
    | «variable» | record | variant | join => simp [projectOldNativeLiteral394] at p
    | nominal _ args =>
      cases done : plainArgs394 args <;> simp [projectOldNativeLiteral394,done] at p
      exact ⟨_,_,p.symm⟩
  | nominal _ args =>
    cases done : plainArgs394 args <;> simp [projectOldNativeLiteral394,done] at p
    exact ⟨_,_,p.symm⟩

def outputReceipt395 {s q f ord}
    (packet : OriginalCompoundOutput394 (s := s) (q := q) f ord) : Option OrderedReceipt :=
  (projectOldNativeLiteral394 packet.emit.requested.target packet.emit.rhs).map
    fun write => ⟨packet.emit.occurrence,packet.emit.ordinal,packet.emit.requested,packet.body,write⟩

theorem output_receipt_is_literal395 {s q f ord}
    {packet : OriginalCompoundOutput394 (s := s) (q := q) f ord} {receipt : OrderedReceipt}
    (made : outputReceipt395 packet = some receipt) :
    receipt.occurrence = q.occurrence ∧ receipt.ordinal = ord.val ∧
    q.demand.outputs[ord.val]? = some receipt.requested ∧
    GeneralDictionaryAssociatedProvenance.Supplies
      (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.current).roles f.decl
      receipt.requested.name receipt.source ∧ receipt.writesTarget := by
  unfold outputReceipt395 at made
  cases projected : projectOldNativeLiteral394 packet.emit.requested.target packet.emit.rhs with
  | none => simp [projected] at made
  | some write =>
    simp only [projected,Option.map_some,Option.some.injEq] at made
    subst receipt
    obtain ⟨position,ordinal,asked,supplied,_⟩ := compound_emit_is_original_source394 packet
    refine ⟨position,ordinal,asked,supplied,?_⟩
    obtain ⟨bodySyntax,args,shape⟩ := projected_native_target395 projected
    simp [OrderedReceipt.writesTarget,shape]

structure SelectedHeadOrigin395 {s q row}
    (t : CandidateTape s q (visible s q)) where
  pick : AuthoredCandidate s q row
  visibleOrdinal : Nat
  rawOrdinal : Nat
  stored : StoredAt395 t pick visibleOrdinal
  ordinal : unfilterOrdinal395 (fun row : Declaration => row.role == q.demand.role)
    (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.current).declarations visibleOrdinal =
      some rawOrdinal
  authored : (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.current).declarations[rawOrdinal]? =
    some row

theorem selected_head_original_origin395 {s q row}
    {t : CandidateTape s q (visible s q)} (only : TapedMatch s q t row) :
    Nonempty (SelectedHeadOrigin395 (row := row) t) := by
  obtain ⟨pick,i,j,store,original,authored⟩ := actual_selected_head_has_registry_ordinal395 only
  exact ⟨⟨pick,i,j,store,original,authored⟩⟩

structure SelectedOutput395 {s q row} {t : CandidateTape s q (visible s q)}
    (origin : SelectedHeadOrigin395 (row := row) t)
    (place : Placement) (ord : Fin q.demand.outputs.length) where
  capture : Nat → Capture
  observed : All₂ (DeepHead s capture) q.demand.arguments row.head
  sameHead : origin.pick.head = .ordered capture observed
  output : OriginalCompoundOutput394
    (frameAtSource395 origin.pick.inScope origin.rawOrdinal origin.authored place capture) ord

/-- The original source body and exact output of a current taped winner
are used, rather than a chosen binding table. This scoped constructor
handles the ordered native-head source route. The joined route and
reads not observed in that head have no result here, not rejection. -/
noncomputable def deriveSelectedOutput395 {s q row} {t : CandidateTape s q (visible s q)}
    (origin : SelectedHeadOrigin395 (row := row) t)
    (place : Placement) (ord : Fin q.demand.outputs.length)
    (checked : GeneralDeclarations.Checked
      (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.current)) :
    Option (SelectedOutput395 origin place ord) :=
  let declaration := checked.2 row ((visible_exact s q row).mp origin.pick.inScope).1
  match head : origin.pick.head with
  | .joined _ => none
  | .ordered cap read =>
    (deriveOutputFromActualHead395 origin.pick.head cap origin.rawOrdinal origin.authored
      origin.pick.inScope place declaration.outputOnly ord declaration.identified.2.2.1).map
      fun output => ⟨cap,read,head,output⟩

/-- Start from the actual complete tape's positive evidence, not a
published receipt or a per-model head. This operation is only a
readback; the caller owns the independent candidate classification. -/
noncomputable def produceFromActualSelection395 {s q row}
    {t : CandidateTape s q (visible s q)} (only : TapedMatch s q t row)
    (place : Placement) (ord : Fin q.demand.outputs.length)
    (checked : GeneralDeclarations.Checked
      (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.current)) :
    Option (Σ origin : SelectedHeadOrigin395 (row := row) t, SelectedOutput395 origin place ord) :=
  let origin := Classical.choice (selected_head_original_origin395 only)
  (deriveSelectedOutput395 origin place ord checked).map fun output => ⟨origin,output⟩

theorem actual_selection_literal_receipt395 {s q row}
    {t : CandidateTape s q (visible s q)}
    {origin : SelectedHeadOrigin395 (row := row) t} {place ord}
    (selected : SelectedOutput395 origin place ord) {receipt : OrderedReceipt}
    (made : outputReceipt395 selected.output = some receipt) :
    StoredAt395 t origin.pick origin.visibleOrdinal ∧
    (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.current).declarations[origin.rawOrdinal]? = some row ∧
    receipt.occurrence = q.occurrence ∧ receipt.ordinal = ord.val ∧
    q.demand.outputs[ord.val]? = some receipt.requested ∧
    GeneralDictionaryAssociatedProvenance.Supplies
      (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.current).roles row
      receipt.requested.name receipt.source ∧ receipt.writesTarget := by
  exact ⟨origin.stored,origin.authored,output_receipt_is_literal395 made⟩

end Yulang.GeneralDeclarativeI65
