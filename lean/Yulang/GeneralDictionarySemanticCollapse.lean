import Yulang.GeneralDictionaryRevisionArgumentBridge
import Yulang.GeneralNominalRecursiveInspection

/-! Depth-two nominal reinspection when an outer argument becomes point-valued.
The old duplicated inner arm disappears. This is a semantic projection bridge,
not a literal report/Refines or materialization transport. -/
namespace Yulang.GeneralDictionarySemanticCollapse
open GeneralNominalRecursiveInspection GeneralNominalReobservationSteps
open GeneralNominalInspection (Query Bounds)

variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}

structure Shape (revision : Revision state) where
  root : Fin state.context.state.base.slots
  lower : Fin state.context.state.base.slots
  upper : Fin state.context.state.base.slots
  distinct : lower ≠ upper
  oldOuter : GeneralNominalState.Descriptor state.context.state.base.slots
  newOuter : GeneralNominalState.Descriptor state.context.state.base.slots
  left : GeneralNominalState.Descriptor state.context.state.base.slots
  right : GeneralNominalState.Descriptor state.context.state.base.slots
  oldRoot : state.context.state.nominals root = some oldOuter
  newRoot : revision.snapshot.nominals root = some newOuter
  oldLower : state.context.state.nominals lower = some left
  newLower : revision.snapshot.nominals lower = some left
  oldUpper : state.context.state.nominals upper = some right
  sameOuter : newOuter.declaration.name = oldOuter.declaration.name
  sameInner : right.declaration.name = left.declaration.name
  first : Bounds state.context.state
  last : Bounds state.context.state
  oldArgs : oldOuter.arguments = [.type (lower,upper)]
  newArgs : newOuter.arguments = [.type (lower,lower)]
  leftArgs : left.arguments = [.type first]
  rightArgs : right.arguments = [.type last]
  binder : Nat

variable {revision : Revision state}

def query (s : Shape revision) : Query :=
 .nominal s.oldOuter.declaration.name [.nominal s.left.declaration.name [.variables [s.binder]]]
def parent (s : Shape revision) : Origin :=
 .nominal (.source (state.context.state.base.source s.root)) s.oldOuter.declaration.name 0
def leaf (s : Shape revision) : Origin := .nominal (parent s) s.left.declaration.name 0

def beforeReport (s : Shape revision) : Report state.context.state where
 captures := [⟨s.binder,s.first,some (leaf s)⟩,⟨s.binder,s.last,some (leaf s)⟩]
 inspected := [(s.root,s.root),(s.lower,s.upper)]
 checked := [(s.root,s.root),(s.lower,s.upper),s.first,s.last]
 anchors := [(parent s,(s.lower,s.upper)),(leaf s,s.first),(leaf s,s.last)]
 tests := [(parent s,.nominal s.left.declaration.name 1)]

def afterReport (s : Shape revision) : Report revision.snapshot where
 captures := [⟨s.binder,s.first,some (leaf s)⟩]
 inspected := [(s.root,s.root),(s.lower,s.lower)]
 checked := [(s.root,s.root),(s.lower,s.lower),s.first]
 anchors := [(parent s,(s.lower,s.lower)),(leaf s,s.first)]
 tests := [(parent s,.nominal s.left.declaration.name 1)]

theorem before_exact (s : Shape revision) :
 inspect state.context.state (query s) (s.root,s.root) none = beforeReport s := by
 simp [query,inspect,inspectMany,s.oldRoot,s.oldLower,s.oldUpper,s.oldArgs,s.leftArgs,
   s.rightArgs,s.sameInner,s.distinct,typeArguments,Report.visit,Report.append,
   beforeReport,parent,leaf]

theorem after_exact (s : Shape revision) :
 inspect revision.snapshot (query s) (s.root,s.root) none = afterReport s := by
 have root : revision.entries s.root = some s.newOuter := s.newRoot
 have lower : revision.entries s.lower = some s.left := s.newLower
 simp [query,inspect,inspectMany,Revision.snapshot,root,lower,s.newArgs,s.leftArgs,
   s.sameOuter,typeArguments,List.mapM_cons,List.mapM_nil,
   afterReport,Report.visit,Report.append,parent,leaf]

theorem current_projection (s : Shape revision)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models revision.snapshot model)
    (old : ProjectionModels state.context.state
      (inspect state.context.state (query s) (s.root,s.root) none) model) :
    ProjectionModels revision.snapshot
      (inspect revision.snapshot (query s) (s.root,s.root) none) model := by
 rw [before_exact] at old
 rw [after_exact]
 have fresh := nominal_argument_bounds revision.snapshot model valid s.root s.newOuter
   s.newRoot 0 (s.lower,s.lower) (by rw [s.newArgs]; rfl)
 have fresh' : (∃ actual, Observes model (parent s) actual) ∧
     ∀ actual, Observes model (parent s) actual →
       Fits revision.snapshot model (s.lower,s.lower) actual := by
   simpa [parent,s.sameOuter,Revision.snapshot,Fits] using fresh
 refine ⟨?_,?_,?_,?_⟩
 · intro anchor member
   simp only [afterReport,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl
   · exact fresh'
   · exact old.1 (leaf s,s.first) (by simp [beforeReport])
 · intro test member actual seen
   exact old.2.1 test (by simpa [beforeReport,afterReport] using member) actual seen
 · intro first hf last hl same origin found actual seen
   have ef : first = ⟨s.binder,s.first,some (leaf s)⟩ := List.mem_singleton.mp hf
   have el : last = ⟨s.binder,s.first,some (leaf s)⟩ := List.mem_singleton.mp hl
   subst first; subst last
   exact old.2.2.1 ⟨s.binder,s.first,some (leaf s)⟩ (by simp [beforeReport])
     ⟨s.binder,s.first,some (leaf s)⟩ (by simp [beforeReport]) same origin found actual seen
 · intro first hf last hl same a b ha hb x y hx hy
   have ef : first = ⟨s.binder,s.first,some (leaf s)⟩ := List.mem_singleton.mp hf
   have el : last = ⟨s.binder,s.first,some (leaf s)⟩ := List.mem_singleton.mp hl
   subst first; subst last
   exact old.2.2.2 ⟨s.binder,s.first,some (leaf s)⟩ (by simp [beforeReport])
     ⟨s.binder,s.first,some (leaf s)⟩ (by simp [beforeReport]) same a b ha hb x y hx hy

theorem capture_count_drops (s : Shape revision) :
 (inspect state.context.state (query s) (s.root,s.root) none).captures.length = 2 ∧
 (inspect revision.snapshot (query s) (s.root,s.root) none).captures.length = 1 := by
 rw [before_exact,after_exact]; exact ⟨rfl,rfl⟩

theorem both_finished (s : Shape revision) :
 Finished (inspect state.context.state (query s) (s.root,s.root) none) ∧
 Finished (inspect revision.snapshot (query s) (s.root,s.root) none) := by
 rw [before_exact,after_exact]; exact ⟨⟨rfl,rfl,rfl⟩,⟨rfl,rfl,rfl⟩⟩

theorem bindings_before (s : Shape revision) :
 bindings state.context.state (inspect state.context.state (query s) (s.root,s.root) none) =
 [(s.binder,state.context.state.base.source s.first.1,state.context.state.base.source s.first.2),
  (s.binder,state.context.state.base.source s.last.1,state.context.state.base.source s.last.2)] := by
 rw [before_exact]; rfl

theorem bindings_after (s : Shape revision) :
 bindings revision.snapshot (inspect revision.snapshot (query s) (s.root,s.root) none) =
 [(s.binder,state.context.state.base.source s.first.1,state.context.state.base.source s.first.2)] := by
 rw [after_exact]; rfl

end Yulang.GeneralDictionarySemanticCollapse
