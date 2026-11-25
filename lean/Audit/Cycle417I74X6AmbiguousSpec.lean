import Yulang.GeneralDeclarativeI65I74X6AmbiguousCoherence417
import Yulang.GeneralDeclarativeI65I74X6AmbiguousPriority417

namespace Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417.SpecX6
open GeneralDeclarativeI65 (B6OccurrenceAtlas401 visible)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open Checker408 (Problem Result)
open CommonNominalFullCarrier (Ty variant subtype_refl)
open PlainMerged416 (sourceX6 variantRow416 idempotentRow originX6)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def actual : Declaration := ⟨57,7,[sourceX6 20 8 13],[],[],[]⟩
def ground : Declaration := ⟨58,7,[.variant 20 (.app 9 [])],[],[],[]⟩

def surface (ds : List Declaration) (declared : Bool) : InputBundle :=
  let tags : List Row := [⟨9,some ⟨[],9⟩,.primitive (.scalar .int)⟩,⟨10,some ⟨[],10⟩,.primitive (.scalar .str)⟩]
  ⟨⟨.absent,tags⟩,⟨.absent,tags⟩,⟨1,if declared then [⟨7,1,[]⟩,⟨17,1,[]⟩] else [⟨17,1,[]⟩]⟩,ds⟩

def rootRow : Equation := variantRow416 0 20 1
def intRow : Equation := OpenTail414.intRow 1
def joinRow : Equation := idempotentRow 0
def ordinary : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[rootRow,intRow,joinRow]⟩

def build (ds : List Declaration := [actual])
    (raw : GeneralDeclarativeHead320.State := ordinary) (declared : Bool := true) (typed : Bool := true) :
    Option Problem := do
  let program ← compile bodies
  let src ← GeneralSourceMetadataBareBundle291.compile (surface ds declared)
  let e : Environment := ⟨0,0,0,bodies,program,src⟩
  let s : GeneralDeclarativeI65.State :=
    ⟨⟨e,raw,[]⟩,[],[⟨0,[44],originX6 20 1⟩] ++
      (if typed then [⟨1,[44,0],integerOriginSyntax⟩] else []),[]⟩
  let atlas : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,atlas⟩,⟨[61],⟨7,[⟨0,0,0⟩],[]⟩⟩⟩


def wire : AmbiguityWire := ⟨0,1,0,1,2,0,1,⟨[0,1],[0,1]⟩,⟨[0,1],[2,0]⟩⟩
def reverse : AmbiguityWire := {wire with plainOrdinal := 1, groundOrdinal := 0}

def checkOpt (p : Option Problem := build [actual,ground]) (r : Result := report417)
    (w : Witness := .x6Ambiguity wire) : Bool :=
  (p.map fun data => check data r w).getD false

theorem both_authored_orders_report_only_ambiguity417 :
    checkOpt = true ∧ checkOpt (build [ground,actual]) report417 (.x6Ambiguity reverse) = true :=
  by decide +kernel

theorem neither_candidate_is_selected_and_no_receipt_is_fabricated417 :
    checkOpt (build [actual,ground]) (Check408.nullaryReport actual) = false ∧
    checkOpt (build [actual,ground]) (Check408.nullaryReport ground) = false ∧
    checkOpt (build [actual,ground]) Check408.rawReport = false ∧
    checkOpt (build [actual,ground]) {report417 with
      writes := [⟨[61],0,0,⟨9,9⟩,.default 7 9 (.var 0),.node 0 [] []⟩]} = false :=
  by decide +kernel

def model : I72.Model :=
  ⟨fun n => ((if n = 0 then variant 20 (.base .int) else .base .int),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (originX6 20 1) else
      if n = 1 then some integerOriginSyntax else none⟩

theorem actual_X6_ambiguity_source_fits417 {p : Problem} (ds : List Declaration) (ready : build ds = some p) : Fits p.state model := by
  unfold build at ready
  cases cp : compile bodies with
  | none => simp [cp] at ready
  | some program =>
    cases cm : GeneralSourceMetadataBareBundle291.compile (surface ds true) with
    | none => simp [cp,cm] at ready
    | some bundle =>
      simp only [cp,cm,Option.pure_def] at ready
      cases ready
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro _ no; cases no
      · intro _ no; cases no
      · intro x found
        change x ∈ [rootRow,intRow,joinRow] at found
        simp only [List.mem_cons,List.not_mem_nil,or_false] at found
        rcases found with rfl|rfl|rfl
        · exact ⟨subtype_refl _,subtype_refl _⟩
        · exact ⟨subtype_refl _,subtype_refl _⟩
        · exact PlainMerged416.idempotent_row_adds_no_model_requirement416 0 model
      · intro _ no; cases no
      · intro x found
        change x ∈ [⟨0,[44],originX6 20 1⟩,⟨1,[44,0],integerOriginSyntax⟩] at found
        simp only [List.mem_cons,List.not_mem_nil,or_false] at found
        rcases found with rfl|rfl <;> rfl


theorem build_preserves_authored_table417 {ds : List Declaration} {p : Problem}
    (ready : build ds = some p) :
    (authoredRegistry p.state.core.current).declarations = ds := by
  unfold build at ready
  cases cp : compile bodies with
  | none => simp [cp] at ready
  | some program =>
    cases cm : GeneralSourceMetadataBareBundle291.compile (surface ds true) with
    | none => simp [cp,cm] at ready
    | some bundle =>
      simp only [cp,cm,Option.pure_def] at ready
      cases ready
      exact congrArg InputBundle.declarations
        (GeneralSourceMetadataBareBundle291.preserves_input _ _ cm).1

theorem genuine_X6_model_has_two_actual_matches_and_ambiguous_report417 :
    ∃ p, build [actual,ground] = some p ∧ Fits p.state model ∧
      ∃ a : Ambiguous p.state p.root, replayAmbiguity417 p wire = some a ∧
      a.plain.candidate.decl = actual ∧ a.ground.candidate.decl = ground ∧
      ∀ m, Fits p.state m → ClassifiedAs p.state p.root report417 ∧
        ReportEvidence p.state m p.root report417 := by
  have good := both_authored_orders_report_only_ambiguity417.1
  cases ready : build [actual,ground] with
  | none => simp [checkOpt,ready] at good
  | some p =>
    have yes : check p report417 (.x6Ambiguity wire) = true := by simpa [checkOpt,ready] using good
    obtain ⟨witness,replay,_,left,right⟩ := result_includes_actual_replayed_ordinals417 yes
    have table := build_preserves_authored_table417 ready
    rw [table] at left right
    have leftExact : some actual = some witness.plain.candidate.decl := left
    have rightExact : some ground = some witness.ground.candidate.decl := right
    refine ⟨p,rfl,actual_X6_ambiguity_source_fits417 _ ready,witness,replay,(Option.some.inj leftExact).symm,
      (Option.some.inj rightExact).symm,fun m fit => ⟨(check_sound _ _ _ yes).1,(check_sound _ _ _ yes).2 m fit⟩⟩

def variantAlias : Equation := ⟨2,.variable 0⟩
def aliasOthers : GeneralDeclarativeHead320.State :=
  {ordinary with equations := ordinary.equations ++ [variantAlias,variantRow416 2 20 1]}
def aliasWire : AmbiguityWire :=
  {wire with
    rootEscape := ⟨[0,1,0],[0,1]⟩
    payloadEscape := ⟨[0,1,0],[2,0]⟩}

def extraFromAlias : GeneralDeclarativeHead320.State :=
  {aliasOthers with equations := aliasOthers.equations ++ [variantRow416 2 20 3]}
def extraFromAliasWire : AmbiguityWire :=
  {wire with
    rootEscape := ⟨[0,1,0,1],[0,1]⟩
    payloadEscape := ⟨[0,1,0,2],[2,0,2]⟩}

def offRoute : GeneralDeclarativeHead320.State :=
  {ordinary with equations := ordinary.equations ++ [variantRow416 2 20 2]}
def offRouteWire : AmbiguityWire :=
  {wire with
    rootEscape := ⟨[0,1,2],[0,1,2]⟩
    payloadEscape := ⟨[0,1,2],[2,0,2]⟩}

def payloadLoop : GeneralDeclarativeHead320.State :=
  {ordinary with equations := ordinary.equations ++ [variantRow416 1 20 1]}
def actualRootLoop : GeneralDeclarativeHead320.State :=
  {ordinary with equations := ordinary.equations ++ [⟨1,.variable 0⟩]}
def actualRootLoopWire : GeneralDeclarativeWitnessCycle350.Wire :=
  ⟨0,⟨0,.same,1⟩,[],.forward 3⟩

theorem known_off_path_recursion_and_alias_to_same_payload_are_allowed417 :
    checkOpt (build [actual,ground] aliasOthers) report417 (.x6Ambiguity aliasWire) = true ∧
    checkOpt (build [actual,ground] offRoute) report417 (.x6Ambiguity offRouteWire) = true :=
  by decide +kernel

theorem unfiltered_actual_payload_cycle_not_misreported_as_ambiguity417 :
    List410.checkExactEscape payloadLoop 0 wire.rootEscape = true ∧
    List410.checkExactEscape payloadLoop 1 wire.payloadEscape = false ∧
    checkOpt (build [actual,ground] payloadLoop) = false ∧
    checkOpt (build [actual,ground] actualRootLoop) = false ∧
    checkOpt (build [actual,ground] actualRootLoop) Check408.rawReport
      (.previous (.previous (.previous (.previous (.previous (.previous
        (.previous (.previous (.previous (.rawRoot actualRootLoopWire)))))))))) = true :=
  by decide +kernel

theorem alternate_alias_destination_fails_only_checked_origin_profile417 :
    List410.checkExactEscape extraFromAlias 0 extraFromAliasWire.rootEscape = true ∧
    List410.checkExactEscape extraFromAlias 1 extraFromAliasWire.payloadEscape = true ∧
    extraFromAlias.equations.all
      (groundVariantAtRoot extraFromAliasWire.rootEscape 0 20 1) = false ∧
    checkOpt (build [actual,ground] extraFromAlias) report417
      (.x6Ambiguity extraFromAliasWire) = false :=
  by decide +kernel

def extra : Declaration := {ground with id := 59}
def unrelated : Declaration := {extra with role := 17}
def wrongTag : Declaration := {ground with head := [.variant 21 (.app 9 [])]}
def wrongType : Declaration := {ground with head := [.variant 20 (.app 10 [])]}
def noJoin : GeneralDeclarativeHead320.State := {ordinary with equations := [rootRow,intRow]}
def conflictingRoot : GeneralDeclarativeHead320.State :=
  {ordinary with equations := ordinary.equations ++ [variantRow416 0 20 3]}
def withWhere : Declaration := {ground with requirements := [⟨60,17,[.app 9 []],[]⟩]}

theorem only_the_original_two_visible_hits_count417 :
    checkOpt (build [actual,unrelated,ground]) report417
      (.x6Ambiguity {wire with groundOrdinal := 2}) = true ∧
    checkOpt (build [actual,unrelated,ground]) = false ∧
    checkOpt (build [actual,ground,extra]) = false ∧
    checkOpt (build [actual,{ground with id := actual.id}]) = false ∧
    checkOpt (build [actual,unrelated]) = false ∧
    checkOpt (build [actual,{unrelated with id := actual.id},ground]) report417
      (.x6Ambiguity {wire with groundOrdinal := 2}) = false ∧
    checkOpt (build [actual,withWhere]) = false ∧
    checkOpt (build [actual,wrongTag]) = false ∧
    checkOpt (build [actual,wrongType]) = false ∧
    checkOpt (build [actual]) = false ∧
    checkOpt (build [ground]) = false ∧
    checkOpt (build [actual,ground] ordinary false) = false ∧
    checkOpt (build [actual,ground] noJoin) = false ∧
    checkOpt (build [actual,ground] conflictingRoot) = false :=
  by decide +kernel

def wrongLocator (w : AmbiguityWire) : List AmbiguityWire :=
  [{w with origin := 1},{w with payloadOrigin := 0},{w with payloadOrigin := 2},{w with variantRow := 1},{w with intRow := 0},{w with joinRow := 1},
   {w with plainOrdinal := w.groundOrdinal},{w with plainOrdinal := 2},{w with groundOrdinal := w.plainOrdinal},
   {w with groundOrdinal := 2},{w with rootEscape := w.payloadEscape},
   {w with payloadEscape := w.rootEscape}]

theorem wrong_locations_and_forged_gates_are_not_ambiguity417 :
    (wrongLocator wire).all (fun w => !checkOpt (build [actual,ground]) report417 (.x6Ambiguity w)) = true ∧
    (wrongLocator reverse).all
      (fun w => !checkOpt (build [ground,actual]) report417 (.x6Ambiguity w)) = true :=
  by decide +kernel

theorem raw_int_alone_is_not_original_ground_authority417 :
    checkOpt (build [actual,ground] ordinary true false) = false ∧
    checkOpt (build [actual,ground] actualRootLoop true false) Check408.rawReport
      (.previous (.previous (.previous (.previous (.previous (.previous
        (.previous (.previous (.previous (.rawRoot actualRootLoopWire)))))))))) = true :=
  by decide +kernel

/-- Witness addresses change when the actual rows change order; neither
declaration order nor ordinary storage order chooses a winner. -/
def rowOrders : List (List Equation × (Nat × Nat × Nat)) :=
  [([rootRow,intRow,joinRow],(0,1,2)),([rootRow,joinRow,intRow],(0,2,1)),
   ([intRow,rootRow,joinRow],(1,0,2)),([intRow,joinRow,rootRow],(2,0,1)),
   ([joinRow,rootRow,intRow],(1,2,0)),([joinRow,intRow,rootRow],(2,1,0))]

def applyRows (w : AmbiguityWire) (newIndices : Nat × Nat × Nat) : AmbiguityWire :=
  {w with
    variantRow := newIndices.1
    intRow := newIndices.2.1
    joinRow := newIndices.2.2}

def checkOrder (ds : List Declaration) (w : AmbiguityWire) (address : List Equation × (Nat × Nat × Nat)) :
    Bool :=
  checkOpt (build ds {ordinary with equations := address.1}) report417
    (.x6Ambiguity (applyRows w address.2))

theorem both_source_orders_and_six_honest_row_relocations417 :
    rowOrders.all (checkOrder [actual,ground] wire) = true ∧
    rowOrders.all (checkOrder [ground,actual] reverse) = true ∧
    rowOrders.tail.all
      (fun e => !checkOpt (build [actual,ground] {ordinary with equations := e.1}) report417
        (.x6Ambiguity wire)) = true :=
  by decide +kernel

#eval [checkOpt,checkOpt (build [ground,actual]) report417 (.x6Ambiguity reverse),
  checkOpt (build [actual,ground]) (Check408.nullaryReport actual)]
#print axioms raw_int_alone_is_not_original_ground_authority417
#print axioms both_source_orders_and_six_honest_row_relocations417
#print axioms build_preserves_authored_table417
#print axioms known_off_path_recursion_and_alias_to_same_payload_are_allowed417
#print axioms unfiltered_actual_payload_cycle_not_misreported_as_ambiguity417
#print axioms alternate_alias_destination_fails_only_checked_origin_profile417
#print axioms only_the_original_two_visible_hits_count417
#print axioms wrong_locations_and_forged_gates_are_not_ambiguity417
#print axioms both_authored_orders_report_only_ambiguity417
#print axioms neither_candidate_is_selected_and_no_receipt_is_fabricated417
#print axioms actual_X6_ambiguity_source_fits417
#print axioms genuine_X6_model_has_two_actual_matches_and_ambiguous_report417
end Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417.SpecX6
