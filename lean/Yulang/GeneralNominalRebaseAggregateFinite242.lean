import Yulang.GeneralNominalCaptureMerges
/-! Finite normalized aggregate expressions from an explicit finite pair pool.
The actual operational closure of that endpoint pool is a separate obligation. -/
namespace Yulang.GeneralNominalRebaseAggregateFinite242
open GeneralSourceState (Interval)
open GeneralNominalAllocation (lower upper)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {pair : Interval} {pool bounds : List Interval}

def canonical (pool bounds : List Interval) : List Interval := pool.filter (fun pair => pair ∈ bounds)
theorem canonical_mem : pair ∈ canonical pool bounds ↔ pair ∈ pool ∧ pair ∈ bounds := by simp [canonical]
theorem canonical_exact (supported : bounds ⊆ pool) : pair ∈ canonical pool bounds ↔ pair ∈ bounds :=
 ⟨fun member => (canonical_mem.mp member).2,fun member => canonical_mem.mpr ⟨supported member,member⟩⟩
theorem canonical_nonempty (supported : bounds ⊆ pool) (nonempty : bounds ≠ []) : canonical pool bounds ≠ [] := by
 intro empty
 have none : ∀ pair ∈ bounds, False := by
   intro pair member
   have found := (canonical_exact supported).mpr member
   rw [empty] at found
   cases found
 exact nonempty (List.eq_nil_iff_forall_not_mem.mpr none)
theorem canonical_idempotent : canonical pool (canonical pool bounds) = canonical pool bounds := by
 unfold canonical
 apply List.filter_congr
 intro pair member
 simp [member]

def subsets : List Interval → List (List Interval)
 | [] => [[]]
 | pair :: rest => subsets rest ++ (subsets rest).map (pair :: ·)
theorem canonical_enumerated (pool bounds : List Interval) : canonical pool bounds ∈ subsets pool := by
 induction pool with
 | nil => simp [canonical,subsets]
 | cons pair rest ih =>
   by_cases member : pair ∈ bounds
   · simp only [canonical,List.filter_cons,member,decide_true,ite_true]
     apply List.mem_append_right
     exact List.mem_map.mpr ⟨canonical rest bounds,ih,rfl⟩
   · simp only [canonical,List.filter_cons,member,decide_false,Bool.false_eq_true,ite_false]
     exact List.mem_append_left _ ih

theorem subsets_length (pool : List Interval) : (subsets pool).length = 2 ^ pool.length := by
 induction pool with
 | nil => rfl
 | cons pair rest ih => simp only [subsets,List.length_append,List.length_map,ih,List.length_cons,Nat.pow_succ]; omega

theorem lower_equivalent (model : Assignment) (supported : bounds ⊆ pool) (nonempty : bounds ≠ []) :
 Equivalent ((lower (canonical pool bounds)).eval CommonNominalFullCarrier.model model)
   ((lower bounds).eval CommonNominalFullCarrier.model model) := by
 have canonNonempty := canonical_nonempty supported nonempty
 have original := GeneralNominalCaptureMerges.lower_exact model bounds nonempty
 have normalized := GeneralNominalCaptureMerges.lower_exact model (canonical pool bounds) canonNonempty
 constructor
 · apply (normalized _).mpr
   intro pair member
   exact (original _).mp (subtype_refl _) pair ((canonical_exact supported).mp member)
 · apply (original _).mpr
   intro pair member
   exact (normalized _).mp (subtype_refl _) pair ((canonical_exact supported).mpr member)

theorem upper_equivalent (model : Assignment) (supported : bounds ⊆ pool) (nonempty : bounds ≠ []) :
 Equivalent ((upper (canonical pool bounds)).eval CommonNominalFullCarrier.model model)
   ((upper bounds).eval CommonNominalFullCarrier.model model) := by
 have canonNonempty := canonical_nonempty supported nonempty
 have original := GeneralNominalCaptureMerges.upper_exact model bounds nonempty
 have normalized := GeneralNominalCaptureMerges.upper_exact model (canonical pool bounds) canonNonempty
 constructor
 · apply (original _).mpr
   intro pair member
   exact (normalized _).mp (subtype_refl _) pair ((canonical_exact supported).mpr member)
 · apply (normalized _).mpr
   intro pair member
   exact (original _).mp (subtype_refl _) pair ((canonical_exact supported).mp member)

theorem fits_iff (model : Assignment) (supported : bounds ⊆ pool) (actual : Ty) :
 (∀ pair ∈ canonical pool bounds, GeneralNominalCaptureMerges.Fits model pair actual) ↔
 (∀ pair ∈ bounds, GeneralNominalCaptureMerges.Fits model pair actual) := by
 constructor
 · exact fun holds pair member => holds pair ((canonical_exact supported).mpr member)
 · exact fun holds pair member => holds pair ((canonical_exact supported).mp member)

def expressionPairs (pool : List Interval) := (subsets pool).map (fun bounds => (lower bounds,upper bounds))

theorem finite_representative (model : Assignment) (supported : bounds ⊆ pool) (nonempty : bounds ≠ []) :
 ∃ pair ∈ expressionPairs pool,
 Equivalent (pair.1.eval CommonNominalFullCarrier.model model) ((lower bounds).eval CommonNominalFullCarrier.model model) ∧
 Equivalent (pair.2.eval CommonNominalFullCarrier.model model) ((upper bounds).eval CommonNominalFullCarrier.model model) :=
 ⟨_,List.mem_map.mpr ⟨_,canonical_enumerated pool bounds,rfl⟩,
 lower_equivalent model supported nonempty,upper_equivalent model supported nonempty⟩

theorem uniform_representative (supported : bounds ⊆ pool) (nonempty : bounds ≠ []) :
 ∃ pair ∈ expressionPairs pool, ∀ model : Assignment,
 Equivalent (pair.1.eval CommonNominalFullCarrier.model model) ((lower bounds).eval CommonNominalFullCarrier.model model) ∧
 Equivalent (pair.2.eval CommonNominalFullCarrier.model model) ((upper bounds).eval CommonNominalFullCarrier.model model) :=
 ⟨_,List.mem_map.mpr ⟨_,canonical_enumerated pool bounds,rfl⟩,
 fun model => ⟨lower_equivalent model supported nonempty,upper_equivalent model supported nonempty⟩⟩

theorem expressionPairs_length : (expressionPairs pool).length = 2 ^ pool.length := by
 rw [expressionPairs,List.length_map,subsets_length]

def endpointPairs (sources : List Nat) : List Interval :=
 sources.flatMap (fun first => sources.map (fun last => (first,last)))

theorem endpointPairs_mem {pair : Interval} : pair ∈ endpointPairs sources ↔ pair.1 ∈ sources ∧ pair.2 ∈ sources := by
 constructor
 · intro member
   obtain ⟨first,one,lasts⟩ := List.mem_flatMap.mp member
   obtain ⟨last,two,equal⟩ := List.mem_map.mp lasts
   cases equal
   exact ⟨one,two⟩
 · rintro ⟨one,two⟩
   exact List.mem_flatMap.mpr ⟨pair.1,one,List.mem_map.mpr ⟨pair.2,two,Prod.eta pair⟩⟩

theorem endpointPairs_length (sources : List Nat) : (endpointPairs sources).length = sources.length * sources.length := by
 have general (first last : List Nat) : (first.flatMap (fun a => last.map (fun b => (a,b)))).length = first.length * last.length := by
   induction first with
   | nil => simp
   | cons head tail ih => simp only [List.flatMap_cons,List.length_append,List.length_map,ih,List.length_cons,Nat.add_mul,Nat.one_mul]; omega
 exact general sources sources

theorem endpoint_uniform
 (supported : ∀ pair ∈ bounds, pair.1 ∈ sources ∧ pair.2 ∈ sources) (nonempty : bounds ≠ []) :
 ∃ pair ∈ expressionPairs (endpointPairs sources), ∀ model : Assignment,
 Equivalent (pair.1.eval CommonNominalFullCarrier.model model) ((lower bounds).eval CommonNominalFullCarrier.model model) ∧
 Equivalent (pair.2.eval CommonNominalFullCarrier.model model) ((upper bounds).eval CommonNominalFullCarrier.model model) :=
 uniform_representative (fun _ member => endpointPairs_mem.mpr (supported _ member)) nonempty

end Yulang.GeneralNominalRebaseAggregateFinite242
