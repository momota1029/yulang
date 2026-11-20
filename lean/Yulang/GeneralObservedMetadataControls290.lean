import Yulang.GeneralObservedMetadataClosure290

/-! Closed controls over the recorded cycle-287 observation state. The
additional candidate is an adversarial query (not a new raw transition). -/
set_option maxHeartbeats 15000000
namespace Yulang.GeneralObservedMetadataControls290
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration)
open GeneralNominalInspection (Interpretation Query)
open GeneralCandidateInspection (Primitive)
open GeneralNominalCandidates (Context Metadata)
open GeneralRebaseRowChildSource287 (raw interp constructors registry parentDecl childDecl)
open GeneralRebaseReceiptCollision289 (removed)
open GeneralObservedMetadataKeys290 (headKeys)
open GeneralObservedMetadataScope290 (coverage certify)
open GeneralObservedMetadataReport290 (queriesFrom reportFrom)
open GeneralRebaseReceiptCatalogue289 (agreement constructorKeys)

def insertInvariant (base : Interpretation) (extra : Nat) : Interpretation :=
  ⟨fun key => if key = extra then none else base.primitives key,
   fun key => if key = extra then true else base.invariantNominal key,
   by intro key h; by_cases eq : key = extra
      · simp [eq]
      · simpa [eq] using base.disjoint key (by simpa [eq] using h)⟩

def insertPrimitive (base : Interpretation) (extra : Nat) (new : Primitive) : Interpretation :=
  ⟨fun key => if key = extra then some new else base.primitives key,
   fun key => if key = extra then false else base.invariantNominal key,
   by intro key h; by_cases eq : key = extra
      · simp [eq] at h
      · simpa [eq] using base.disjoint key (by simpa [eq] using h)⟩

def removeInvariant (base : Interpretation) (key : Nat) : Interpretation :=
  ⟨base.primitives,fun n => if n = key then false else base.invariantNominal n,
   by intro n h; by_cases eq : n = key
      · simp [eq] at h
      · exact base.disjoint n (by simpa [eq] using h)⟩

abbrev extra : Declaration := ⟨42,1,[.app 5 [.var 0,.var 1]],[],[],[]⟩
abbrev atZero : List (GeneralNominalInspection.Bounds raw) := [(0,0)]
abbrev extraInterp : Interpretation := insertInvariant interp 5

theorem real_observed_keys : constructorKeys raw = [6,0] := by decide +kernel

theorem declaration_adds_key :
    headKeys extra = [5] ∧ coverage raw [extra] = [6,0,5] := by decide +kernel

theorem old_finite_misses_new_query_key :
    agreement (constructorKeys raw) constructors (removed 5).constructors = true := by
  decide +kernel

theorem new_finite_sees_new_query_key :
    certify (coverage raw [extra]) constructors extraInterp (removed 5).constructors extraInterp =
      .disagreement := by decide +kernel

theorem query_changed :
    queriesFrom constructors extraInterp extra = [.nominal 5 [.variables [0],.variables [1]]] ∧
    queriesFrom (removed 5).constructors extraInterp extra = [.deferred (.app 5 [.var 0,.var 1])] := by
  constructor
  · change [GeneralNominalInspection.translate constructors extraInterp
      (.app 5 [.var 0,.var 1])] = _
    simp [GeneralNominalInspection.translate,extraInterp,insertInvariant,constructors,
      GeneralDeclarationExamples.constructors]
  · change [GeneralNominalInspection.translate (removed 5).constructors extraInterp
      (.app 5 [.var 0,.var 1])] = _
    simp [GeneralNominalInspection.translate,extraInterp,insertInvariant,removed]

theorem old_report_changed :
    (reportFrom raw constructors extraInterp extra atZero).conflicts = atZero ∧
    (reportFrom raw constructors extraInterp extra atZero).blocked = [] ∧
    (reportFrom raw (removed 5).constructors extraInterp extra atZero).conflicts = [] ∧
    (reportFrom raw (removed 5).constructors extraInterp extra atZero).blocked = atZero := by
  decide +kernel

theorem invariant_flag_essential :
    certify (coverage raw [parentDecl]) constructors interp constructors (removeInvariant interp 0) =
      .disagreement ∧
    (reportFrom raw constructors interp parentDecl [(1,1)]).blocked = [] ∧
    (reportFrom raw constructors (removeInvariant interp 0) parentDecl [(1,1)]).blocked = [(1,1)] := by
  decide +kernel

abbrev primitiveOutside : Interpretation := insertPrimitive interp 8 .pair

theorem incompatible_even_when_equal :
    certify (coverage raw [extra] ++ [8]) constructors primitiveOutside constructors primitiveOutside =
      .incompatiblePrimitive := by decide +kernel

theorem equal_local_incompatible_outside :
    certify (coverage raw [parentDecl,childDecl true]) constructors interp constructors primitiveOutside =
      .good ∧ ¬ Metadata (registry true) ⟨raw,primitiveOutside⟩ := by
  constructor
  · decide +kernel
  · intro valid
    obtain ⟨d,found,shape⟩ := valid.2 8 .pair (by rfl)
    change some ⟨[],8⟩ = some d at found
    cases Option.some.inj found
    cases shape

theorem equal_local_missing_catalogue_outside :
    certify (coverage raw [parentDecl,childDecl true]) constructors interp
      (removed 8).constructors interp = .good ∧
    ¬ Metadata (removed 8) ⟨raw,interp⟩ := by
  constructor
  · decide +kernel
  · intro valid
    have clash := congrFun valid.1 8
    change (none : Option GeneralDeclarationPatterns.Constructor) = some ⟨[],8⟩ at clash
    cases clash

end Yulang.GeneralObservedMetadataControls290
