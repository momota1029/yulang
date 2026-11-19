import Yulang.GeneralRebaseOriginEdgeScan269
import Yulang.GeneralRebaseActualArguments269
import Yulang.GeneralDictionaryInspectionHeads215

namespace Yulang.GeneralRebaseNominalOrigin269
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Head Equal)
open GeneralNominalRecursiveInspection (Origin Test Observes embed_observation recover_observation)
open GeneralNominalOriginTerms (arity project)
open GeneralNominalState (Descriptor)
open GeneralRebaseActualArguments269 (Member TypeSlots fits_length bounded_of_observed)
open GeneralDictionaryInspectionHeads215 (tag_subtype tagged_nominal tagged_shape)
open CommonNominalFullCarrier

abbrev Raw (state : State roles) := state.core.erased.current.context.state

def origin (state : State roles) (point : Fin (Raw state).base.slots) : Origin :=
 .source ((Raw state).base.source point)

def tag (d : Descriptor m) : Test := .nominal d.declaration.name d.arguments.length

theorem head (state : State roles) (point : Fin (Raw state).base.slots) (d : Descriptor (Raw state).base.slots)
 (known : (Raw state).nominals point = some d) : Head state (origin state point) (tag d) := by
 intro model valid
 have raw : GeneralNominalState.Models (Raw state) model := valid.1.1
 obtain ⟨args,fits,matching⟩ := raw.2.1 point d known
 refine ⟨⟨_,.source _⟩,?_⟩
 intro value seen
 cases seen
 exact ⟨args,(fits_length fits).symm,matching⟩

theorem exhaust (state : State roles) (point : Fin (Raw state).base.slots) (d : Descriptor (Raw state).base.slots)
 (known : (Raw state).nominals point = some d) (inhabited : ∃ model, Models state model)
 (t : Test) (test : Head state (origin state point) t) (positive : arity t ≠ 0) :
 t = tag d := by
 obtain ⟨model,valid⟩ := inhabited
 have holds := (test model valid).2 _ (.source _)
 have raw : GeneralNominalState.Models (Raw state) model := valid.1.1
 obtain ⟨args,fits,canonical⟩ := raw.2.1 point d known
 cases t with
 | scalar _ => exact False.elim (positive rfl)
 | structural shape =>
   obtain ⟨values,size,same⟩ := holds
   have incompatible := tag_subtype (tagged_nominal d.declaration.name args)
     (tagged_shape shape values size) (subtype_trans canonical.2 same.1)
   cases shape <;> cases incompatible
 | nominal name count =>
   obtain ⟨values,size,same⟩ := holds
   have pair := (nominal_regular_invariant_exact ..).mp (subtype_trans canonical.2 same.1)
   have names : name = d.declaration.name := pair.1.symm
   have arities : count = d.arguments.length := size.symm.trans (pair.2.1.symm.trans (fits_length fits).symm)
   simp only [tag,names,arities]

/-- Raw all-model actual-argument evidence implies full-journal semantic
equality of the corresponding projected value. This direction uses
restriction of full models; the converse is not asserted. -/
theorem member_equal (state : State roles) (parent target : Fin (Raw state).base.slots)
 (d : Descriptor (Raw state).base.slots) (i : Fin (arity (tag d)))
 (matching : Member (Raw state) parent target d i.val) :
 Equal state (project (origin state parent) (tag d) i) (origin state target) := by
 intro model valid
 obtain ⟨actual,observes,point⟩ := matching model valid.1.1
 refine ⟨⟨actual,embed_observation model _ actual observes⟩,⟨_,.source _⟩,?_⟩
 intro left right hLeft hRight
 cases hRight
 have recovered := recover_observation model
   (.argument (.source ((Raw state).base.source parent)) d.declaration.name i.val) left hLeft
 have same := GeneralNominalProjections.observation_unique model _ _ _ recovered observes
 exact ⟨subtype_trans same.1 point.1,subtype_trans point.2 same.2⟩

theorem observed_is_type (state : State roles) (parent : Fin (Raw state).base.slots)
 (d : Descriptor (Raw state).base.slots) (known : (Raw state).nominals parent = some d)
 (i : Fin d.arguments.length) (inhabited : ∃ model, Models state model)
 (active : ∃ o, Equal state (project (origin state parent) (tag d) i) o) :
 i ∈ TypeSlots d := by
 obtain ⟨model,valid⟩ := inhabited
 obtain ⟨o,equal⟩ := active
 obtain ⟨value,seen⟩ := (equal model valid).1
 have recovered := recover_observation model
   (.argument (.source ((Raw state).base.source parent)) d.declaration.name i.val) value seen
 obtain ⟨j,within,eq⟩ := bounded_of_observed (Raw state) model valid.1.1 parent d known i.val value recovered
 have fixed : j = i := Fin.ext eq
 exact fixed ▸ within

end Yulang.GeneralRebaseNominalOrigin269
