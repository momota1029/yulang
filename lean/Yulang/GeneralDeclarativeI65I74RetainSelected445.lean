import Yulang.GeneralDeclarativeI65I74FullState444
import Yulang.GeneralDeclarativeI65I74MixedFixedDictionary442

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RetainedFull445
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem)
open MixedFixed442
open CommonRoleOutermostResolver (Dictionary)

/-- Independent source of a scoped selection. The original candidate
evidence is the full visible singleton of C442, with its raw K2 guards,
actual B6 term, and exact event head. An executable replay equality,
submitted witness, storage assertion, and model are not fields. -/
structure SourceSelection (p : Problem) where
  origin : Replay p
  head : origin.event.head = (origin.exactDecl.symm ▸ restoreOriginalHead origin.original)
  own : ReplayReadOwnOutput origin

def SourceSelection.dictionary {p} (e : SourceSelection p) : Dictionary :=
  .node e.origin.decl.id []

def eventRow {s q} (e : Event s q) (i : Fin q.demand.outputs.length) :
    RetainedEquation s := ⟨q,e.frame,i,e.outputs i⟩

def selectedRows {s : FullState} {q : I72.Request}
    (e : SourceSelection ⟨s.base,q⟩) : List (RetainedEquation s.base) :=
  List.ofFn (eventRow e.origin.event)

/-- Append the exact ordered source-produced rows. This changes
neither the old snapshot nor an earlier row. -/
def retainSelected (s : FullState) {q : I72.Request}
    (e : SourceSelection ⟨s.base,q⟩) : FullState :=
  ⟨s.base,s.retained ++ selectedRows e⟩

theorem selected_rows_at_original_output445 {s : FullState} {q : I72.Request}
    (e : SourceSelection ⟨s.base,q⟩) (i : Fin q.demand.outputs.length) :
    (selectedRows e)[i.val]? = some (eventRow e.origin.event i) := by
  simp [selectedRows]

theorem fitsFull_retainSelected_iff445 (s : FullState) {q : I72.Request}
    (e : SourceSelection ⟨s.base,q⟩) (m : I72.Model) :
    FitsFull (retainSelected s e) m ↔ FitsFull s m ∧ FixedTargets m e.origin.event := by
  constructor
  · intro h
    refine ⟨⟨h.1,fun r inOld => h.2 r (List.mem_append_left _ inOld)⟩,?_⟩
    intro i
    exact h.2 (eventRow e.origin.event i)
      (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  · intro h
    refine ⟨h.1.1,?_⟩
    intro r kept
    rcases List.mem_append.mp kept with old|newRow
    · exact h.1.2 r old
    · obtain ⟨i,eq⟩ := List.mem_ofFn.mp newRow
      cases eq
      exact h.2 i

theorem replay_exact_selected_head445 {p : Problem} {w : RefPositions441.Wire}
    {r : Replay p} (got : replay442 p w = some r) :
    r.event.head = (r.exactDecl.symm ▸ restoreOriginalHead r.original) := by
  unfold replay442 at got
  split at got
  next d scope =>
    cases first : RefPositions441.replay441 (inputOnly p) d (inputOnly_visible p ▸ scope) w with
    | none => simp [first,Bind.bind,Option.bind] at got
    | some a =>
      simp only [first,Bind.bind,Option.bind] at got
      split at got
      · cases got
      · split at got
        · split at got
          · split at got
            · cases got
            · cases Option.some.inj got
              rfl
          · cases got
        · cases got
  all_goals cases got

theorem source_event_dictionary445 {p : Problem} (e : SourceSelection p) (m : I72.Model)
    (fit : I72.Fits p.state m) (fixed : FixedTargets m e.origin.event) :
    I72.DictionaryEvidence p.state m p.root e.dictionary := by
  let r := e.origin
  change I72.DictionaryEvidence p.state m p.root (.node r.decl.id [])
  rw [← r.exactDecl]
  refine .node r.event ?_ fixed (r.noWhere ▸ .nil)
  have authored : GeneralDeclarations.DeclarationChecked
      (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry p.state.core.current).constructors
      (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry p.state.core.current).roles r.event.frame.decl :=
    r.exactDecl ▸ r.original.checked
  have hhead : preoutputInputOfHead399 r.event.head (fun _ => emptyCapture403) =
      r.original.capture := by
    have go {d d' : GeneralDeclarations.Declaration} (eq : d = d')
        (h : SourceHead p.state.core p.root d') :
        preoutputInputOfHead399 (eq.symm ▸ h) (fun _ => emptyCapture403) =
          preoutputInputOfHead399 h (fun _ => emptyCapture403) := by
      cases eq
      rfl
    have same := e.head
    change r.event.head = (r.exactDecl.symm ▸ restoreOriginalHead r.original) at same
    rw [same]
    exact (go r.exactDecl _).trans (restored_input_is_exact442 r.original)
  exact semantic_node_in_signature p.state p.root r.event
    (node_from_exact_preoutput_head405 r.event authored (fun _ => emptyCapture403)
      (r.exactInput.trans hhead.symm)) m fit

end Yulang.GeneralDeclarativeI65.I72.RetainedFull445
