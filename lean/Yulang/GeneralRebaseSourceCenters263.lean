import Yulang.GeneralRebaseRegisteredSites263
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Yulang.GeneralRebaseSourceCenters263
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

/-- Only actual registered head schemas, deliberately excluding output/body
and ClassEffects satisfaction from the support premise. -/
def Heads (state : State roles) (assignment : Assignment) : Prop :=
 ∀ plan ∈ state.plans, GeneralNominalVersionedPlans231.SchemaHolds plan plan.headSchema assignment

theorem heads (state : State roles) (assignment : Assignment) (valid : Models state assignment) :
 Heads state assignment := fun plan member =>
   (GeneralRebaseRegisteredPlan263.inputs state assignment valid plan member).2.2.2.2.1

def Centers (assignment : Assignment) (first last : Site roles) : Prop :=
 ∀ index : Nat, Equivalent
   (assignment ((List.ofFn first.center)[index]?.getD 0)).1
   (assignment ((List.ofFn last.center)[index]?.getD 0)).1

theorem self (assignment : Assignment) (site : Site roles) : Centers assignment site site :=
 fun _ => GeneralDictionaryDefaultExpression209.equivalent_refl _

theorem child_centers (first last : Plan roles)
 (seed : first.packet.context.state.seed = last.packet.context.state.seed)
 (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
 (declaration : first.packet.declaration = last.packet.declaration)
 (clause : Clause) (member : clause ∈ first.packet.declaration.requirements)
 (signature : clause.Signature roles) (assignment : Assignment)
 (binders : ∀ name ∈ first.packet.declaration.inputNames,
   Equivalent (assignment (first.binder name)).1 (assignment (last.binder name)).1) :
 Centers assignment
   (GeneralNominalVersionedFrame231.childSite first clause signature)
   (GeneralNominalVersionedFrame231.childSite last clause signature) := by
 have result := GeneralNominalChildSemantic186.child_centers_list first last seed identity declaration
   clause member signature assignment (fun name used => GeneralRebaseHeadSupport263.source_same assignment _ _ (binders name used))
 intro index
 have one := result index
 have e1 : (GeneralNominalVersionedFrame231.childSite first clause signature).center =
     (first.childSite clause signature).center := funext (GeneralNominalVersionedFrame231.childSite_center_eq first clause signature)
 have e2 : (GeneralNominalVersionedFrame231.childSite last clause signature).center =
     (last.childSite clause signature).center := funext (GeneralNominalVersionedFrame231.childSite_center_eq last clause signature)
 rw [e1,e2]
 exact one.2.2 _ _ (.source _) (.source _)

private theorem childSite_congr (plan : Plan roles) (first last : Clause)
 (equal : first = last) (one : first.Signature roles) (two : last.Signature roles) :
 GeneralNominalVersionedFrame231.childSite plan first one = GeneralNominalVersionedFrame231.childSite plan last two := by
 cases equal
 rfl

/-- Semantic center coherence across two independent actual mixed paths.
The induction is on strictly growing invocation identities, not source path
length, and uses actual head models of registered producers. -/
theorem centers_from_heads (registry : Registry) (checked : Checked registry)
 (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
 (before after : State roles)
 (pathOne : B4Target.Steps (Step registry root) (initial context root) before)
 (pathTwo : B4Target.Steps (Step registry root) (initial context root) after)
 (assignment : Assignment) (validOne : Heads before assignment) (validTwo : Heads after assignment)
 (first last : Site roles) (memberOne : first ∈ before.core.sites) (memberTwo : last ∈ after.core.sites)
 (identity : first.occurrence.identity = last.occurrence.identity) : Centers assignment first last := by
 have byIdentity : ∀ number, ∀ first last : Site roles,
     first ∈ before.core.sites → last ∈ after.core.sites →
     first.occurrence.identity = number → first.occurrence.identity = last.occurrence.identity →
     Centers assignment first last := by
   intro number
   induction number using Nat.strongRecOn with
   | ind number ih =>
     intro first last one two atNumber identity
     rcases GeneralRebaseRegisteredSites263.origin registry context root before pathOne first one with rfl | ⟨a,ha,ea⟩
     · rcases GeneralRebaseRegisteredSites263.origin registry context root after pathTwo last two with rfl | ⟨b,hb,eb⟩
       · exact self assignment _
       · have impossible := GeneralRebaseRegisteredSites263.emitted_above_root registry context root after pathTwo b hb last eb
         change root.identity = last.occurrence.identity at identity
         omega
     · rcases GeneralRebaseRegisteredSites263.origin registry context root after pathTwo last two with rfl | ⟨b,hb,eb⟩
       · have impossible := GeneralRebaseRegisteredSites263.emitted_above_root registry context root before pathOne a ha first ea
         change first.occurrence.identity = root.identity at identity
         omega
       · obtain ⟨ca,_,rfl⟩ := List.mem_map.mp ea
         obtain ⟨cb,_,rfl⟩ := List.mem_map.mp eb
         have ma := GeneralRebaseRegisteredPlan263.metadata registry context root before pathOne a ha
         have mb := GeneralRebaseRegisteredPlan263.metadata registry context root after pathTwo b hb
         have seed := ma.seed.trans mb.seed.symm
         have pa := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr ca.property
         have pb := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr cb.property
         obtain ⟨parent,decl,clauses⟩ := GeneralNominalChildCoherence184.producer_declarations
           registry checked a b seed ma.visible mb.visible ca.val cb.val pa pb (a.packet.checked.signature.2.2.2 ca.val pa) (b.packet.checked.signature.2.2.2 cb.val pb) identity
         have smaller := GeneralNominalCenteredWhere.packet_child_above a.packet _
           (GeneralNominalCenteredTrace.clauseChild_mem a.packet ca.val pa (a.packet.checked.signature.2.2.2 ca.val pa))
         have small : a.input.occurrence.identity < number := by
           rw [a.input_exact,← atNumber]
           exact smaller
         have parentCenters := ih a.input.occurrence.identity small a.input b.input
           (GeneralRebaseRegisteredSites263.inputs registry context root before pathOne a ha)
           (GeneralRebaseRegisteredSites263.inputs registry context root after pathTwo b hb) rfl
           ((congrArg Occurrence.identity a.input_exact).trans
             (parent.trans (congrArg Occurrence.identity b.input_exact).symm))
         have binders := GeneralRebaseHeadSupport263.input_binder a b assignment decl
           (ma.constructors.trans mb.constructors.symm) (ma.interpretation.trans mb.interpretation.symm)
           parentCenters
           (validOne a ha)
           (validTwo b hb) ma.finished
         have sameCenters := child_centers a b seed parent decl ca.val pa
           (a.packet.checked.signature.2.2.2 ca.val pa) assignment binders
         have siteEq : GeneralNominalVersionedFrame231.childSite b cb.val (b.packet.checked.signature.2.2.2 cb.val pb) =
             GeneralNominalVersionedFrame231.childSite b ca.val (a.packet.checked.signature.2.2.2 ca.val pa) := by
           exact childSite_congr b _ _ clauses.symm _ _
         rw [siteEq]
         exact sameCenters
 exact byIdentity first.occurrence.identity first last memberOne memberTwo rfl identity


/-- No semantic center/binder/effect equivalence assumption: actual registered
head models plus common source ancestry produce normalized compatibility. -/
theorem compatible (registry : Registry) (checked : Checked registry)
 (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
 (before after : State roles)
 (pathOne : B4Target.Steps (Step registry root) (initial context root) before)
 (pathTwo : B4Target.Steps (Step registry root) (initial context root) after)
 (first last : Plan roles) (memberOne : first ∈ before.plans) (memberTwo : last ∈ after.plans)
 (owner : (first.packet.site.occurrence.identity,first.packet.declaration.id) =
          (last.packet.site.occurrence.identity,last.packet.declaration.id))
 (assignment : Assignment) (validOne : Models before assignment) (validTwo : Models after assignment) :
 GeneralRebaseNormalizedBody263.Compatible first last assignment := by
 have same := centers_from_heads registry checked context root before after pathOne pathTwo assignment (heads before assignment validOne) (heads after assignment validTwo)
   first.input last.input
   (GeneralRebaseRegisteredSites263.inputs registry context root before pathOne first memberOne)
   (GeneralRebaseRegisteredSites263.inputs registry context root after pathTwo last memberTwo)
   ((congrArg Occurrence.identity first.input_exact).trans
     ((congrArg Prod.fst owner).trans (congrArg Occurrence.identity last.input_exact).symm))
 exact GeneralRebaseRegisteredPlan263.compatible registry checked context root before after pathOne pathTwo
   first last memberOne memberTwo (congrArg Prod.fst owner) (congrArg Prod.snd owner) assignment validOne validTwo same

theorem source_compatible (registry : Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : Occurrence roles) (start before after : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start)
 (pathOne : B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root) start before)
 (pathTwo : B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root) start after)
 (first last : Plan roles) (memberOne : first ∈ before.plans) (memberTwo : last ∈ after.plans)
 (owner : (first.packet.site.occurrence.identity,first.packet.declaration.id) =
          (last.packet.site.occurrence.identity,last.packet.declaration.id))
 (assignment : Assignment) (validOne : Models before assignment) (validTwo : Models after assignment) :
 GeneralRebaseNormalizedBody263.Compatible first last assignment := by
 have compiled := GeneralNominalVersionedMixedSourceBoundary234.initial_compiled source
 obtain ⟨legacy,⟨context,labels,formed,point,ground,coverage,rfl⟩,rfl⟩ := compiled
 exact compatible _ (GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked).2
   context root before after pathOne pathTwo first last memberOne memberTwo owner assignment validOne validTwo


/-- Head-only support is sufficient; output body/ClassEffects need not hold
in either snapshot to obtain transport. -/
theorem compatible_from_heads (registry : Registry) (checked : Checked registry)
 (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
 (before after : State roles)
 (pathOne : B4Target.Steps (Step registry root) (initial context root) before)
 (pathTwo : B4Target.Steps (Step registry root) (initial context root) after)
 (first last : Plan roles) (memberOne : first ∈ before.plans) (memberTwo : last ∈ after.plans)
 (owner : (first.packet.site.occurrence.identity,first.packet.declaration.id) =
          (last.packet.site.occurrence.identity,last.packet.declaration.id))
 (assignment : Assignment) (validOne : Heads before assignment) (validTwo : Heads after assignment) :
 GeneralRebaseNormalizedBody263.Compatible first last assignment := by
 have ma := GeneralRebaseRegisteredPlan263.metadata registry context root before pathOne first memberOne
 have mb := GeneralRebaseRegisteredPlan263.metadata registry context root after pathTwo last memberTwo
 have same := centers_from_heads registry checked context root before after pathOne pathTwo assignment validOne validTwo
   first.input last.input
   (GeneralRebaseRegisteredSites263.inputs registry context root before pathOne first memberOne)
   (GeneralRebaseRegisteredSites263.inputs registry context root after pathTwo last memberTwo)
   ((congrArg Occurrence.identity first.input_exact).trans
     ((congrArg Prod.fst owner).trans (congrArg Occurrence.identity last.input_exact).symm))
 exact GeneralRebaseHeadSupport263.from_heads first last assignment
   (GeneralRebaseRegisteredPlan263.layout registry checked context first last ma mb (congrArg Prod.snd owner))
   (ma.constructors.trans mb.constructors.symm) (ma.seed.trans mb.seed.symm)
   (congrArg Prod.fst owner) same (validOne first memberOne) (validTwo last memberTwo) ma.finished

theorem source_compatible_from_heads (registry : Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : Occurrence roles) (start before after : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start)
 (pathOne : B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root) start before)
 (pathTwo : B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root) start after)
 (first last : Plan roles) (memberOne : first ∈ before.plans) (memberTwo : last ∈ after.plans)
 (owner : (first.packet.site.occurrence.identity,first.packet.declaration.id) =
          (last.packet.site.occurrence.identity,last.packet.declaration.id))
 (assignment : Assignment) (validOne : Heads before assignment) (validTwo : Heads after assignment) :
 GeneralRebaseNormalizedBody263.Compatible first last assignment := by
 have compiled := GeneralNominalVersionedMixedSourceBoundary234.initial_compiled source
 obtain ⟨legacy,⟨context,labels,formed,point,ground,coverage,rfl⟩,rfl⟩ := compiled
 exact compatible_from_heads _ (GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked).2
   context root before after pathOne pathTwo first last memberOne memberTwo owner assignment validOne validTwo


/-- Backward-compatible Models wrapper for the strictly weaker head theorem. -/
theorem centers (registry : Registry) (checked : Checked registry)
 (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
 (before after : State roles)
 (pathOne : B4Target.Steps (Step registry root) (initial context root) before)
 (pathTwo : B4Target.Steps (Step registry root) (initial context root) after)
 (assignment : Assignment) (validOne : Models before assignment) (validTwo : Models after assignment)
 (first last : Site roles) (memberOne : first ∈ before.core.sites) (memberTwo : last ∈ after.core.sites)
 (identity : first.occurrence.identity = last.occurrence.identity) : Centers assignment first last :=
 centers_from_heads registry checked context root before after pathOne pathTwo assignment
   (heads before assignment validOne) (heads after assignment validTwo) first last memberOne memberTwo identity
end Yulang.GeneralRebaseSourceCenters263
