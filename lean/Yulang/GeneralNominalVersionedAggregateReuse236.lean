import Yulang.GeneralNominalVersionedJournalFrame236
set_option backward.isDefEq.respectTransparency false
/-! Stored observation versions retain exactly their old merge equations.
The coverage predicate is syntactic and historical, not an assumed model law. -/
namespace Yulang.GeneralNominalVersionedAggregateReuse236
open GeneralDeclarations GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalAllocation (Bindings occurrences lower upper equations)
open GeneralNominalVersionedJournal232
open PresenceNormalForm (All)

def chunk (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
 (declaration : Declaration) (bindings : Bindings) (name : Nat) : List (PresenceNormalForm.Atom Nat) :=
 match occurrences bindings name with
 | [_] => []
 | bounds =>
   equations ((GeneralNominalVersionedAllocation231.capture state registry root declaration.id bindings).inputs name).1 (lower bounds) ++
   equations ((GeneralNominalVersionedAllocation231.capture state registry root declaration.id bindings).inputs name).2 (upper bounds)

theorem merges_eq : GeneralNominalVersionedAllocation231.merges state registry root declaration bindings =
 declaration.inputNames.flatMap (chunk state registry root declaration bindings) := rfl

theorem chunk_same (seed : a.seed = b.seed) (key : one.id = two.id)
 (same : occurrences first name = occurrences last name) :
 chunk a r root one first name = chunk b s root two last name := by
 unfold chunk GeneralNominalVersionedAllocation231.capture
 simp only [same,seed,key]
 cases found : occurrences last name with
 | nil =>
   have version := GeneralNominalAggregateVersion231.version_eq_iff.mpr same
   simp only [GeneralNominalAggregateVersion231.slot,GeneralNominalAggregateVersion231.key,version]
 | cons head rest =>
   cases rest with
   | nil => rfl
   | cons next tail =>
     have version := GeneralNominalAggregateVersion231.version_eq_iff.mpr same
     simp only [GeneralNominalAggregateVersion231.slot,GeneralNominalAggregateVersion231.key,version]

theorem recorded_merges {state : State roles} {prior : Plan roles} (valid : Models state model) (member : prior ∈ state.plans) :
 All CommonNominalFullCarrier.model model
   (GeneralNominalVersionedAllocation231.merges prior.packet.context.state prior.packet.registry
     prior.packet.site.occurrence.identity prior.packet.declaration prior.packet.bindings) :=
 (GeneralNominalVersionedPlans231.private_models_iff prior.packet model).mp
   (GeneralNominalVersionedPlans231.head_models (valid.2.1 prior member)).1 |>.2.2.1

def Covered (state : State roles) (packet : GeneralNominalSaturationState.Packet roles) : Prop :=
 ∀ name ∈ packet.declaration.inputNames, (occurrences packet.bindings name).length ≠ 1 →
 ∃ prior ∈ state.plans, name ∈ prior.packet.declaration.inputNames ∧
   prior.packet.context.state.seed = packet.context.state.seed ∧
   prior.packet.site.occurrence.identity = packet.site.occurrence.identity ∧
   prior.packet.declaration.id = packet.declaration.id ∧
   occurrences prior.packet.bindings name = occurrences packet.bindings name

theorem covered_merges (covered : Covered state packet) (valid : Models state model) :
 All CommonNominalFullCarrier.model model
   (GeneralNominalVersionedAllocation231.merges packet.context.state packet.registry
     packet.site.occurrence.identity packet.declaration packet.bindings) := by
 rw [merges_eq]
 intro atom member
 obtain ⟨name,named,within⟩ := List.mem_flatMap.mp member
 by_cases single : (occurrences packet.bindings name).length = 1
 · cases found : occurrences packet.bindings name with
   | nil => simp [found] at single
   | cons bounds rest =>
     have empty : rest = [] := by
       apply List.length_eq_zero_iff.mp
       simp only [found,List.length_cons] at single
       omega
     rw [empty] at found
     simp only [chunk,found] at within
     cases within
 · obtain ⟨prior,present,oldNamed,seed,root,key,same⟩ := covered name named single
   have equal := chunk_same (r := prior.packet.registry) (s := packet.registry) (root := prior.packet.site.occurrence.identity) seed key same
   rw [← root] at within
   rw [← equal] at within
   exact recorded_merges valid present atom (List.mem_flatMap.mpr ⟨name,oldNamed,within⟩)

theorem slot_fields (same : GeneralNominalAggregateVersion231.slot seed r d p n first =
 GeneralNominalAggregateVersion231.slot seed r' d' p' n' last) :
 r = r' ∧ d = d' ∧ p = p' ∧ n = n' ∧ occurrences first n = occurrences last n' := by
 have keys := (GeneralNominalIdentities.source_identity seed _ _).mp same
 have root := congrArg (fun k : GeneralNominalIdentities.Origin => k.1) keys
 have decl := congrArg (fun k : GeneralNominalIdentities.Origin => k.2.1) keys
 have purpose := congrArg (fun k : GeneralNominalIdentities.Origin => k.2.2.1) keys
 have name := congrArg (fun k : GeneralNominalIdentities.Origin => k.2.2.2.1) keys
 have version := congrArg (fun k : GeneralNominalIdentities.Origin => k.2.2.2.2) keys
 refine ⟨root,decl,purpose,name,?_⟩
 exact GeneralNominalAggregateVersion231.code_injective (Nat.succ.inj version)

/-- Reuse coverage expressed only through actually stored lower aggregate IDs.
Equal content-addressed IDs recover declaration, invocation and occurrences. -/
def SlotCovered (state : State roles) (packet : GeneralNominalSaturationState.Packet roles) : Prop :=
 ∀ name ∈ packet.declaration.inputNames, (occurrences packet.bindings name).length ≠ 1 →
 ∃ prior ∈ state.plans, ∃ oldName ∈ prior.packet.declaration.inputNames,
   prior.packet.context.state.seed = packet.context.state.seed ∧
   GeneralNominalAggregateVersion231.slot prior.packet.context.state.seed
     prior.packet.site.occurrence.identity prior.packet.declaration.id 0 oldName prior.packet.bindings =
   GeneralNominalAggregateVersion231.slot packet.context.state.seed
     packet.site.occurrence.identity packet.declaration.id 0 name packet.bindings

theorem covered_of_slots (covered : SlotCovered state packet) : Covered state packet := by
 intro name named many
 obtain ⟨prior,present,oldName,oldNamed,seed,slots⟩ := covered name named many
 rw [seed] at slots
 have fields := slot_fields slots
 refine ⟨prior,present,fields.2.2.2.1 ▸ oldNamed,seed,fields.1,fields.2.1,?_⟩
 simpa only [fields.2.2.2.1] using fields.2.2.2.2

theorem reused_merges (covered : SlotCovered state packet) (valid : Models state model) :
 All CommonNominalFullCarrier.model model
   (GeneralNominalVersionedAllocation231.merges packet.context.state packet.registry
     packet.site.occurrence.identity packet.declaration packet.bindings) :=
 covered_merges (covered_of_slots covered) valid

end Yulang.GeneralNominalVersionedAggregateReuse236
