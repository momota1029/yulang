import Yulang.GeneralNominalVersionedJournal232
import Yulang.GeneralNominalCycleK2

/-! I44 consumer transplant: full Models now denotes the mixed versioned
journal, and CandidateCycle uses the versioned Frame. Inspection tests and
actual-position graph structure are unchanged. This is not boundary completion.
Actual-position constructor edges are certified against the full corrected
journal. Nominal edges traverse explicit arguments only. The graph is semantic;
no legacy output-schema test enumeration is used. -/
namespace Yulang.GeneralNominalVersionedCycles232
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalRecursiveInspection (Origin Test)
variable {roles : Roles.RoleDecls} {state : State roles}

def Equal (state : State roles) (first last : Origin) : Prop :=
  ∀ model, Models state model → GeneralNominalOriginTerms.Same model first last

def Head (state : State roles) (origin : Origin) (test : Test) : Prop :=
  ∀ model, Models state model → GeneralNominalOriginTerms.Head model origin test

def Edge (state : State roles) (first last : Origin) : Prop :=
  ∃ (parent : Origin) (test : Test) (index : Fin (GeneralNominalOriginTerms.arity test)), Head state parent test ∧
    Equal state first parent ∧ Equal state (GeneralNominalOriginTerms.project parent test index) last

inductive Path (state : State roles) : Origin → Origin → Prop
  | nil (origin : Origin) : Path state origin origin
  | cons : Edge state first middle → Path state middle last → Path state first last

def Cyclic (state : State roles) (origin : Origin) : Prop :=
  (∃ next, Edge state origin next ∧ Path state next origin) ∧ ∃ model, Models state model

def RootCycle (state : State roles) (root : Occurrence roles) : Prop :=
  (∃ index, Cyclic state (.source (root.demand.arguments index).1)) ∨
  ∃ site ∈ state.core.sites, site.occurrence = root ∧ ∃ index, Cyclic state (.source (site.center index))

def CandidateCycle (registry : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  ∃ plan : Plan roles,
    GeneralNominalVersionedEvidence231.Frame registry state.core root plan.packet.declaration.id plan ∧
    ∃ entry ∈ (GeneralNominalCenteredSteps.inspection plan).tests, Cyclic state entry.1

def Safe (state : State roles) (plan : Plan roles) : Prop :=
  (GeneralNominalCenteredSteps.inspection plan).inspected.length = (GeneralNominalCenteredSteps.inspection plan).tests.length ∧
    ∀ entry ∈ (GeneralNominalCenteredSteps.inspection plan).tests, ¬ Cyclic state entry.1

/-- Raw recurrence classifier keeps the old CandidateK2 RootPending, checked
visible declaration, role, located report, visited position and RecursAt clauses.
Only HeadReady is replaced by versioned Prepared: freshness/private propagation
must use the binding-dependent allocator. Prepared itself uses input-only
matching. No equivalence to the legacy allocator's CandidateK2 is asserted. -/
def RawCandidateK2 (registry : Registry) (context : GeneralNominalRecursiveCandidates.Context)
    (root : Occurrence roles) : Prop :=
  ¬ GeneralNominalState.RootPending context.state root.demand ∧
    ∃ declaration ∈ registry.declarations, ∃ _checked : DeclarationChecked registry.constructors roles declaration,
      declaration.role = root.demand.role ∧ GeneralNominalVersionedCandidates231.Prepared registry context root declaration ∧
      ∃ bounds, GeneralNominalRecursiveCandidates.arguments context root = some bounds ∧
        ∃ visited ∈ (GeneralNominalRecursiveCandidates.report context declaration bounds).inspected,
          GeneralNominalCycleK2.RecursAt context.state visited.1

theorem raw_candidate_not_pending (given : RawCandidateK2 registry context root) :
    ¬ GeneralNominalState.RootPending context.state root.demand := given.1

theorem semantic_self_cycle (head : Head state parent test)
    (index : Fin (GeneralNominalOriginTerms.arity test)) (one : Equal state origin parent)
    (two : Equal state (GeneralNominalOriginTerms.project parent test index) origin)
    (inhabited : ∃ model, Models state model) : Cyclic state origin :=
  ⟨⟨origin,⟨parent,test,index,head,one,two⟩,.nil _⟩,inhabited⟩

theorem full_models_only (models : Models first = Models last) :
    Cyclic first origin ↔ Cyclic last origin := by
  have edges : ∀ a b, Edge first a b ↔ Edge last a b := by simp only [Edge,Head,Equal,models,iff_self,implies_true]
  have paths : ∀ a b, Path first a b ↔ Path last a b := by
    intro a b
    constructor <;> intro path
    · induction path with
      | nil => exact .nil _
      | cons edge _ ih => exact .cons ((edges _ _).mp edge) ih
    · induction path with
      | nil => exact .nil _
      | cons edge _ ih => exact .cons ((edges _ _).mpr edge) ih
  simp only [Cyclic,edges,paths,models]

end Yulang.GeneralNominalVersionedCycles232
