import Yulang.GeneralDictionaryCurrentJournal

/-! A finite packet-journal readback from independent syntactic coverage and
well-foundedness. No semantic Evidence premise or preconstructed dictionary is
required. Coverage and accessibility are NOT proved for every stable state. -/
namespace Yulang.GeneralDictionaryJournalTree
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState

/-- Pure recorded syntax: no Models, Instance, or Evidence occurs here. -/
def Recorded (state : State roles) : LocalInstance roles := fun site key children =>
  ∃ packet ∈ state.packets, packet.site.occurrence = site ∧
    packet.declaration.id = key ∧ packet.children = children

def Child (state : State roles) (child parent : Occurrence roles) : Prop :=
  ∃ packet ∈ state.packets, packet.site.occurrence = parent ∧ child ∈ packet.children

inductive Reach (state : State roles) (root : Occurrence roles) : Occurrence roles → Prop where
  | root : Reach state root root
  | child : Reach state root parent → Child state child parent → Reach state root child

/-- This is finite journal coverage, not an assumption of dictionary soundness. -/
def Covered (state : State roles) (root : Occurrence roles) : Prop :=
  ∀ site, Reach state root site → ∃ packet ∈ state.packets, packet.site.occurrence = site

private theorem children_witnesses (rule : LocalInstance roles)
    (sites : List (Occurrence roles))
    (given : ∀ site ∈ sites, ∃ tree : Dictionary roles, tree.root = site ∧ Evidence rule tree) :
    ∃ trees : List (Dictionary roles), trees.map Dictionary.root = sites ∧
      ∀ tree ∈ trees, Evidence rule tree := by
  induction sites with
  | nil => exact ⟨[],rfl,by intro _ member; cases member⟩
  | cons site sites ih =>
    obtain ⟨first,root,evidence⟩ := given site (List.mem_cons_self)
    obtain ⟨rest,roots,valid⟩ := ih (fun site member => given site (List.mem_cons_of_mem _ member))
    refine ⟨first :: rest,by simp only [List.map_cons,root,roots],?_⟩
    intro tree member
    rcases List.mem_cons.mp member with rfl | member
    · exact evidence
    · exact valid tree member

/-- All branching is the actual ordered packet children, including duplicates.
Accessibility constructs a finite tree rather than presupposing one. -/
theorem recorded_tree (state : State roles) (root : Occurrence roles)
    (covered : Covered state root) (accessible : Acc (Child state) root) :
    ∃ tree : Dictionary roles, tree.root = root ∧ Evidence (Recorded state) tree := by
  have construct : ∀ site, Acc (Child state) site → Reach state root site →
      ∃ tree : Dictionary roles, tree.root = site ∧ Evidence (Recorded state) tree := by
    intro site accessible
    induction accessible with
    | intro site below ih =>
      intro reached
      obtain ⟨packet,present,same⟩ := covered site reached
      obtain ⟨children,roots,valid⟩ := children_witnesses (Recorded state) packet.children
        (fun child member => ih child ⟨packet,present,same,member⟩
          (.child reached ⟨packet,present,same,member⟩))
      exact ⟨.node site packet.declaration.id children,rfl,
        .node ⟨packet,present,same,rfl,roots.symm⟩ valid⟩
  exact construct root accessible .root

/-- Current-context soundness follows for every journal model after one actual
restricted execution. The chosen tree/payload is independent of the model. -/
theorem uniform_dictionary (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context) (after : State roles)
    (path : B4Target.Steps (GeneralDictionaryFinishedTrace.Step registry root)
      (initial context root) after)
    (covered : Covered after root) (accessible : Acc (Child after) root) :
    ∃ tree : Dictionary roles, tree.root = root ∧ Evidence (Recorded after) tree ∧
      ∀ model, Models after model →
        GeneralDictionaryRecursiveEvidence.Evidence registry after.context model root (erase tree) := by
  obtain ⟨tree,same,syntactic⟩ := recorded_tree after root covered accessible
  refine ⟨tree,same,syntactic,?_⟩
  intro model valid
  refine ⟨tree,⟨same,rfl⟩,?_⟩
  apply evidence_mono (Recorded after) (GeneralDictionaryRecursiveEvidence.Instance registry after.context model)
    (fun site key children recorded => ?_) syntactic
  obtain ⟨packet,present,rfl,rfl,rfl⟩ := recorded
  exact GeneralDictionaryCurrentJournal.initial_trace_current registry root context after path packet present model valid

/-- Semantic soundness does not manufacture child coverage: a missing generated
packet is an explicit failure of this syntactic precondition. -/
theorem missing_packet (state : State roles) (root site : Occurrence roles)
    (reached : Reach state root site)
    (missing : ∀ packet ∈ state.packets, packet.site.occurrence ≠ site) : ¬ Covered state root := by
  intro covered
  obtain ⟨packet,present,same⟩ := covered site reached
  exact missing packet present same

end Yulang.GeneralDictionaryJournalTree
