import Yulang.CommonRoleCorrelatedEquations
import Yulang.CommonRoleSupportSearch

/-! Shared finite branch certificates over full ancestor routes. Totality here is
an explicitly stronger diagnostic certificate, NOT a language rejection rule.
No existence, unique solution, stable observation or source-lowering theorem is
claimed. Every sibling uses the same choice table; pending trees need not admit
such a total certificate. -/
namespace Yulang.CommonRoleGlobalChoices
open CommonRoleSettledSyntax CommonRoleOpenProducer CommonRoleMaterializedDomain
open CommonRoleSourceWorklist (Node)
open CommonRoleSettledConstraints (State)
open CommonRoleCorrelatedPaths (Route History Path extend)
open CommonRoleGuardedEquations (Candidate candidate candidate_exact)
open CommonRoleSourceTemplateClosure (declarationChildren)

variable (registry : Registry) (root : SourceRequest n)
abbrev Choice := Route registry root × Declaration
abbrev Table := List (Choice registry root)

def choiceSpace : Table registry root :=
  (CommonRoleCorrelatedCarrier.carrier registry root).flatMap fun r =>
    registry.declarations.map fun d => (r,d)

theorem universe_exact (r : Route registry root) (d : Declaration) :
    (r,d) ∈ choiceSpace registry root ↔
      r ∈ CommonRoleCorrelatedCarrier.carrier registry root ∧ d ∈ registry.declarations := by
  simp [choiceSpace]

def mask (table : Table registry root) (history : History registry root)
    (node : Node registry root) (d : Declaration) : Bool :=
  table.contains ((history,node),d)

theorem mask_exact (table : Table registry root) (r : Route registry root) (d : Declaration) :
    mask registry root table r.1 r.2 d = true ↔ (r,d) ∈ table := by
  simp [mask]

variable (observation : State n)

/-- Independent global certificate. All paths and choices use one shared table. -/
def Valid (table : Table registry root) : Prop :=
  (∀ r d, (r,d) ∈ table → d ∈ registry.declarations ∧
    Path registry root (mask registry root table) observation r ∧ Candidate observation r.2.val d) ∧
  (∀ r d e, (r,d) ∈ table → (r,e) ∈ table → d = e) ∧
  (∀ r, Path registry root (mask registry root table) observation r → ∃ d, (r,d) ∈ table)

def check (table : Table registry root) : Bool :=
  (table.all fun p => registry.declarations.contains p.2 &&
    ((CommonRoleCorrelatedPaths.collect registry root (mask registry root table) observation).contains p.1 &&
      candidate observation p.1.2.val p.2)) &&
  ((table.all fun p => table.all fun q => decide (p.1 ≠ q.1 ∨ p.2 = q.2)) &&
   ((CommonRoleCorrelatedPaths.collect registry root (mask registry root table) observation).all
    fun r => table.any fun p => decide (p.1 = r)))

theorem check_exact (table : Table registry root) :
    check registry root observation table = true ↔ Valid registry root observation table := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.contains_iff_mem, CommonRoleCorrelatedPaths.collect_exact, candidate_exact, decide_eq_true_eq]
  constructor
  · rintro ⟨a,b,c⟩
    refine ⟨?_,?_,?_⟩
    · intro r d h; exact a (r,d) h
    · intro r d e hd he
      exact (b (r,d) hd (r,e) he).resolve_left (by simp)
    · intro r hr
      obtain ⟨⟨t,d⟩,ht,eq⟩ := c r hr
      change t = r at eq
      subst t
      exact ⟨d,ht⟩
  · rintro ⟨a,b,c⟩
    refine ⟨?_,?_,?_⟩
    · intro p hp; exact a p.1 p.2 hp
    · intro p hp q hq
      by_cases eq : p.1 = q.1
      · exact Or.inr (b p.1 p.2 q.2 hp (by simpa [eq] using hq))
      · exact Or.inl eq
    · intro r hr
      obtain ⟨d,hd⟩ := c r hr
      exact ⟨(r,d),hd,rfl⟩

def search : List (Table registry root) :=
  (CommonRoleSupportSearch.subsets (choiceSpace registry root)).filter (check registry root observation)

/-- Exact exhaustive search for canonical shared certificates, at a fixed state. -/
theorem search_exact (table : Table registry root) :
    table ∈ search registry root observation ↔
      table ∈ CommonRoleSupportSearch.subsets (choiceSpace registry root) ∧
      Valid registry root observation table := by
  simp only [search, List.mem_filter, check_exact]

/-- Every chosen certificate contains ALL source children of each chosen parent,
using that same table, not separately selected tables for individual siblings. -/
theorem siblings_closed (table : Table registry root)
    (valid : Valid registry root observation table)
    (r : Route registry root) (d : Declaration) (chosen : (r,d) ∈ table)
    (c : Node registry root) (child : c.val ∈ declarationChildren d r.2.val) :
    Path registry root (mask registry root table) observation (extend registry root r d c) ∧
      ∃ e, (extend registry root r d c,e) ∈ table := by
  obtain ⟨hd,hpath,hcand⟩ := valid.1 r d chosen
  have h : Path registry root (mask registry root table) observation (extend registry root r d c) :=
    .step hpath hd ((mask_exact registry root table r d).mpr chosen) hcand child
  exact ⟨h,valid.2.2 _ h⟩

/-- Two globally supported choices for the same full route cannot disagree. -/
theorem choice_unique (table : Table registry root)
    (valid : Valid registry root observation table)
    (r : Route registry root) (d e : Declaration)
    (hd : (r,d) ∈ table) (he : (r,e) ∈ table) : d = e := valid.2.1 r d e hd he

/-- All searched table entries belong to the fixed finite source carrier. -/
theorem searched_entry_retained (table : Table registry root)
    (found : table ∈ search registry root observation)
    (r : Route registry root) (d : Declaration) (chosen : (r,d) ∈ table) :
    r ∈ CommonRoleCorrelatedCarrier.carrier registry root ∧ d ∈ registry.declarations := by
  exact (universe_exact registry root r d).mp
    (CommonRoleSupportSearch.subset_of_mem_subsets ((search_exact ..).mp found).1 chosen)

/-- Completeness for every Boolean-described canonical finite certificate. -/
theorem canonical_complete (p : Choice registry root → Bool)
    (valid : Valid registry root observation ((choiceSpace registry root).filter p)) :
    (choiceSpace registry root).filter p ∈ search registry root observation :=
  (search_exact ..).mpr ⟨CommonRoleSupportSearch.filter_mem_subsets p _, valid⟩

/-- Explicit finite upper bound; this is exponential reference search. -/
theorem search_capacity : (search registry root observation).length ≤
    2 ^ (choiceSpace registry root).length := by
  calc
    _ ≤ (CommonRoleSupportSearch.subsets (choiceSpace registry root)).length := List.length_filter_le ..
    _ = _ := CommonRoleSupportSearch.subsets_length _

/-- Table order and duplicate representation do not change the active mask. -/
theorem mask_ext (a b : Table registry root)
    (same : ∀ p, p ∈ a ↔ p ∈ b) :
    mask registry root a = mask registry root b := by
  funext history node d
  apply Bool.eq_iff_iff.mpr
  simpa only [mask, List.contains_iff_mem] using same ((history,node),d)

/-- The independent certificate depends only on table membership. -/
theorem valid_ext (a b : Table registry root)
    (same : ∀ p, p ∈ a ↔ p ∈ b) :
    Valid registry root observation a ↔ Valid registry root observation b := by
  have masks := mask_ext registry root a b same
  simp only [Valid, masks, same]

/-- Every valid table has a canonical representation in the actual finite search;
no externally supplied proof about its filtered representation is required. -/
theorem complete (table : Table registry root)
    (valid : Valid registry root observation table) :
    let canonical := (choiceSpace registry root).filter table.contains
    canonical ∈ search registry root observation ∧
      (∀ p, p ∈ canonical ↔ p ∈ table) := by
  let canonical := (choiceSpace registry root).filter table.contains
  have same : ∀ p, p ∈ canonical ↔ p ∈ table := by
    intro ⟨r,d⟩
    simp only [canonical, List.mem_filter, List.contains_iff_mem]
    constructor
    · exact And.right
    · intro h
      obtain ⟨hd,hp,_⟩ := valid.1 r d h
      exact ⟨(universe_exact registry root r d).mpr
        ⟨CommonRoleCorrelatedCarrier.path_retained registry root _ observation r hp,hd⟩,h⟩
  exact ⟨canonical_complete registry root observation table.contains
    ((valid_ext registry root observation canonical table same).mpr valid),same⟩

end Yulang.CommonRoleGlobalChoices
