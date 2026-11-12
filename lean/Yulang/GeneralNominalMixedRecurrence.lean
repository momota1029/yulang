import Yulang.GeneralNominalK2Coverage
import Yulang.GeneralNominalProjections

/-! Anonymous root recurrence may pass through explicit nominal arguments.
The root must be structural; nominal bodies never supply edges. An actual
argument edge retains a projection-to-source correspondence in every model,
so arbitrary interval endpoints cannot manufacture recurrence. -/
namespace Yulang.GeneralNominalMixedRecurrence

open GeneralNominalState (State)
open GeneralNominalProjections (Observes Ref)
open CommonNominalFullCarrier

def Structural (state : State) (slot : Fin state.base.slots) : Prop :=
  ∃ kind children, state.view.heads slot = .structural kind children

def ActualArgument (state : State) (parent child : Fin state.base.slots) : Prop :=
  ∃ descriptor, state.nominals parent = some descriptor ∧
    ∃ index, ∀ model, GeneralNominalState.Models state model →
      ∃ actual, Observes model (.argument (.source (state.base.source parent)) descriptor.declaration.name index) (.inl actual) ∧
        Equivalent actual (model (state.base.source child)).1

def Edge (state : State) (first last : Fin state.base.slots) : Prop :=
  GeneralSourceK2.Child state.view first last ∨ ActualArgument state first last

inductive Path (state : State) : Fin state.base.slots → Fin state.base.slots → Prop
  | nil (slot) : Path state slot slot
  | cons : Edge state first middle → Path state middle last → Path state first last

def Cycle (state : State) (root : Fin state.base.slots) : Prop :=
  ∃ child, Edge state root child ∧ Path state child root

def RecursAt (state : State) (root : Fin state.base.slots) : Prop :=
  Structural state root ∧
    ((Cycle state root ∧ ∃ model, GeneralNominalState.Models state model) ∨ GeneralSourceBoundary.GraphK2 state.view.graph root)

def RootK2 (state : State) (demand : GeneralSourceState.Demand roles) : Prop :=
  GeneralNominalState.Linked state demand ∧ ¬ GeneralNominalState.RootPending state demand ∧
    ∃ index slot, state.base.source slot = (demand.arguments index).1 ∧ RecursAt state slot

theorem point_argument_edge (state : State) (parent child : Fin state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals parent = some descriptor) (index : Nat)
    (parameter : descriptor.arguments[index]? = some (.type (child,child))) : ActualArgument state parent child := by
  refine ⟨descriptor,recorded,index,?_⟩
  intro model models
  obtain ⟨value,seen,fits⟩ := GeneralNominalProjections.parameter_binding_valid state model models parent descriptor recorded index 0
    (.type (child,child)) parameter
  cases value with
  | inr => cases fits
  | inl actual => exact ⟨actual,seen,fits.2,fits.1⟩

theorem equal_endpoint_edge (state : State) (parent lower upper : Fin state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals parent = some descriptor) (index : Nat)
    (parameter : descriptor.arguments[index]? = some (.type (lower,upper)))
    (equal : ∀ model, GeneralNominalState.Models state model →
      Equivalent (model (state.base.source lower)).1 (model (state.base.source upper)).1) :
    ActualArgument state parent lower := by
  refine ⟨descriptor,recorded,index,?_⟩
  intro model models
  obtain ⟨value,seen,fits⟩ := GeneralNominalProjections.parameter_binding_valid state model models parent descriptor recorded index 0
    (.type (lower,upper)) parameter
  cases value with
  | inr => cases fits
  | inl actual => exact ⟨actual,seen,subtype_trans fits.2 (equal model models).2,fits.1⟩

theorem actual_edge_sound (state : State) (parent child : Fin state.base.slots)
    (edge : ActualArgument state parent child) (model : GeneralNominalCommonBridge.Assignment)
    (models : GeneralNominalState.Models state model) :
    ∃ descriptor, state.nominals parent = some descriptor ∧ ∃ index actual,
      Observes model (.argument (.source (state.base.source parent)) descriptor.declaration.name index) (.inl actual) ∧
        Equivalent actual (model (state.base.source child)).1 := by
  obtain ⟨descriptor,recorded,index,valid⟩ := edge
  obtain ⟨actual,seen,equal⟩ := valid model models
  exact ⟨descriptor,recorded,index,actual,seen,equal⟩

theorem nominal_not_recursive (state : State) (root : Fin state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals root = some descriptor) : ¬ RecursAt state root := by
  rintro ⟨⟨kind,children,structural⟩,_⟩
  rw [state.bodies_opaque root descriptor recorded] at structural
  cases structural

theorem source_path (state : State) (first last : Fin state.base.slots)
    (path : GeneralSourceK2.Path state.view first last) : Path state first last := by
  induction path with
  | nil slot => exact .nil slot
  | cons edge _ ih => exact .cons (Or.inl edge) ih

theorem old_rootK2 (state : State) (demand : GeneralSourceState.Demand roles)
    (old : GeneralNominalK2Coverage.RootK2 state demand) : RootK2 state demand := by
  obtain ⟨linked,ready,index,root,source,cycle⟩ := old
  refine ⟨linked,ready,index,root,source,?_,?_⟩
  · rcases cycle with ⟨child,⟨kind,children,head,_⟩,_⟩ | old
    · exact ⟨kind,children,head⟩
    · have recurrent := GeneralNominalState.atK2_recurrence state root old
      rcases recurrent with ⟨child,⟨kind,children,head,_⟩,_⟩ | ⟨kind,children,head,_⟩
      · exact ⟨kind,children,head⟩
      · exact ⟨kind,children,head⟩
  · rcases cycle with ⟨child,edge,path⟩ | old
    · exact Or.inr (Or.inl ((GeneralSourceK2.cycle_graph_iff state.view root).mp ⟨child,edge,path⟩))
    · exact Or.inr old.2

theorem pending_excludes_K2 (state : State) (demand : GeneralSourceState.Demand roles)
    (pending : GeneralNominalState.RootPending state demand) : ¬ RootK2 state demand :=
  fun rejected => rejected.2.1 pending

theorem mixed_cycle_rejects (state : State) (root nominal : Fin state.base.slots)
    (structural : Structural state root) (first : GeneralSourceK2.Child state.view root nominal)
    (back : ActualArgument state nominal root)
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models state model) : RecursAt state root :=
  ⟨structural,Or.inl ⟨⟨nominal,Or.inl first,.cons (Or.inr back) (.nil root)⟩,model,models⟩⟩

end Yulang.GeneralNominalMixedRecurrence
