import YulangClosure.SimpleSubLatticeInference
import YulangClosure.SimpleSubLatticeDecision

/-!
Literal graph-prefix growth preserves existing finite lattice rules, all-depth
interpretations, concrete extrusion and every constraint operation. This permits
allocation and constraints to interleave before one final accepted certificate.
No reverse unfolding rule, intermediate graph validity, or preservation of the
whole target's guardedness is assumed. Completion derives the initial decoder;
all original uses and clients retain one final graph and reference pullback.
The decided corollaries compute the finite terminal witness instead of requiring
an externally supplied certificate.

Native mutable-row realization, source inventory/metadata formation, ordinary
coalescing and the full original Call judgment remain separate obligations.
-/
namespace YulangClosure.SimpleSub.LatticeInference.Completion
open Lattice
open Regular (Comparison)
open RegularPublication (bind_some)

theorem Extends.present {source target : Graph} (extension : Extends source target)
    {k i} (present : Exists source k i) : Exists target k i := by
  rcases present with ⟨node,found⟩
  exact ⟨node,extension.lookup found⟩

theorem Extends.union_at {source target : Graph} (extension : Extends source target)
    {k i parts} (found : unionAt source k i = some parts) : unionAt target k i = some parts := by
  cases h : source.lookup k i with
  | none => simp [unionAt,h] at found
  | some node =>
      cases node <;> simp [unionAt,h] at found
      simpa [unionAt,extension.lookup h] using found

theorem Extends.intersection_at {source target : Graph} (extension : Extends source target)
    {k i parts} (found : intersectionAt source k i = some parts) :
    intersectionAt target k i = some parts := by
  cases h : source.lookup k i with
  | none => simp [intersectionAt,h] at found
  | some node =>
      cases node <;> simp [intersectionAt,h] at found
      simpa [intersectionAt,extension.lookup h] using found

theorem Extends.bottom_at {source target : Graph} (extension : Extends source target)
    {k i} (found : bottomAt source k i = true) : bottomAt target k i = true := by
  cases h : source.lookup k i with
  | none => simp [bottomAt,h] at found
  | some node =>
      cases node with
      | union a b => simp [bottomAt,h] at found
      | intersection a b => simp [bottomAt,h] at found
      | structural node =>
          cases node <;> simp_all [bottomAt,extension.lookup h]

theorem Extends.top_at {source target : Graph} (extension : Extends source target)
    {k i} (found : topAt source k i = true) : topAt target k i = true := by
  cases h : source.lookup k i with
  | none => simp [topAt,h] at found
  | some node =>
      cases node with
      | union a b => simp [topAt,h] at found
      | intersection a b => simp [topAt,h] at found
      | structural node =>
          cases node <;> simp_all [topAt,extension.lookup h]

theorem Extends.expansion {source target : Graph} (extension : Extends source target)
    {pair children} (expanded : structuralExpand source pair = some children) :
    structuralExpand target pair = some children := by
  cases hl : source.lookup pair.kind pair.lower with
  | none => simp [structuralExpand,hl] at expanded
  | some lower =>
      cases hu : source.lookup pair.kind pair.upper with
      | none => simp [structuralExpand,hu] at expanded
      | some upper =>
          cases lower <;> cases upper <;> simp [structuralExpand,hl,hu] at expanded
          simpa [structuralExpand,extension.lookup hl,extension.lookup hu] using expanded

theorem Extends.layer {source target : Graph} (extension : Extends source target)
    {relation pair} (proof : Layer source relation pair) : Layer target relation pair := by
  induction proof with
  | structural expanded closed => exact .structural (extension.expansion expanded) closed
  | refl present => exact .refl (extension.present present)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | bottom found present => exact .bottom (extension.bottom_at found) (extension.present present)
  | top found present => exact .top (extension.top_at found) (extension.present present)
  | unionLeft found => exact .unionLeft (extension.union_at found)
  | unionRight found => exact .unionRight (extension.union_at found)
  | unionElim found _ _ ih₁ ih₂ => exact .unionElim (extension.union_at found) ih₁ ih₂
  | intersectionLeft found => exact .intersectionLeft (extension.intersection_at found)
  | intersectionRight found => exact .intersectionRight (extension.intersection_at found)
  | intersectionIntro found _ _ ih₁ ih₂ =>
      exact .intersectionIntro (extension.intersection_at found) ih₁ ih₂
  | unionMono left right _ _ ih₁ ih₂ =>
      exact .unionMono (extension.union_at left) (extension.union_at right) ih₁ ih₂
  | intersectionMono left right _ _ ih₁ ih₂ =>
      exact .intersectionMono (extension.intersection_at left) (extension.intersection_at right) ih₁ ih₂

/-- Transport at each finite depth, avoiding any unproved reverse unfolding. -/
theorem Extends.approx {source target : Graph} (extension : Extends source target)
    {depth pair} (proof : Approx source depth pair) : Approx target depth pair := by
  induction depth generalizing pair with
  | zero => trivial
  | succ depth ih => exact Layer.mono (fun _ h => ih h) (extension.layer proof)

theorem Extends.regular {source target : Graph} (extension : Extends source target)
    {pair} (proof : RegularSub source pair) : RegularSub target pair :=
  fun depth => extension.approx (proof depth)

theorem Extends.extrusion {source target : Graph} (extension : Extends source target)
    {pair copies} (trace : Extrusion source pair copies) : Extrusion target pair copies := by
  induction trace with
  | copy coordinate => exact .copy coordinate
  | same k identity present => exact .same k identity (extension.present present)
  | structural pair parts expanded children ih =>
      exact .structural pair parts (extension.expansion expanded) ih
  | union lower upper left right ih₁ ih₂ =>
      exact .union (extension.union_at lower) (extension.union_at upper) ih₁ ih₂
  | intersection lower upper left right ih₁ ih₂ =>
      exact .intersection (extension.intersection_at lower) (extension.intersection_at upper) ih₁ ih₂

theorem Extends.step {source target : Graph} (extension : Extends source target)
    {ref birth before after} (step : ConstraintStep source ref birth before after) :
    ConstraintStep target ref birth before after := by
  cases step with
  | reflexive k identity rest events present =>
      exact .reflexive k identity rest events (extension.present present)
  | decompose pair children rest events expanded =>
      exact .decompose pair children rest events (extension.expansion expanded)
  | union k u a b upper rest events found =>
      exact .union k u a b upper rest events (extension.union_at found)
  | intersection k lower u a b rest events found =>
      exact .intersection k lower u a b rest events (extension.intersection_at found)
  | insertLower k lower row state => exact .insertLower k lower row _
  | insertUpper k row upper state => exact .insertUpper k row upper _
  | replay k lower row upper rest events lb ub => exact .replay k lower row upper rest events lb ub
  | extrudeUpper k lower upper fresh copies rest events identity origin receiver traversal =>
      exact .extrudeUpper k lower upper fresh copies rest events identity origin receiver
        (extension.extrusion traversal)
  | extrudeLower k lower fresh upper copies rest events identity origin receiver traversal =>
      exact .extrudeLower k lower fresh upper copies rest events identity origin receiver
        (extension.extrusion traversal)
  | intrude state event selected retained qualifies actual =>
      exact .intrude _ event selected retained qualifies actual

theorem Extends.history {source target : Graph} (extension : Extends source target)
    {ref birth first last} (history : ConstraintHistory source ref birth first last) :
    ConstraintHistory target ref birth first last := by
  induction history with
  | nil state => exact .nil state
  | cons step rest ih => exact .cons (extension.step step) ih

theorem Extends.decode_store {source target : Graph} (extension : Extends source target)
    {refs store pairs} (decoded : decodeStore source refs store = some pairs) :
    decodeStore target refs store = some pairs := by
  induction store generalizing pairs with
  | nil => exact decoded
  | cons clause rest ih =>
      rcases bind_some decoded with ⟨pair,hp,decoded⟩
      rcases bind_some decoded with ⟨pairs,hs,decoded⟩
      simpa [decodeStore,extension.decode_constraint hp,ih hs] using decoded

theorem Extends.store_satisfied {source target : Graph} (extension : Extends source target)
    {refs store} (solved : StoreSatisfied source refs store) : StoreSatisfied target refs store := by
  intro clause hc
  rcases solved clause hc with ⟨pair,decoded,related⟩
  exact ⟨pair,extension.decode_constraint decoded,extension.regular related⟩

end YulangClosure.SimpleSub.LatticeInference.Completion

namespace YulangClosure.SimpleSub.LatticeGrowingInference
open Lattice LatticeInference LatticeInference.Completion
open Regular (Comparison ConstraintState)

inductive GrowingHistory (ref : Nat → Nat → Prop) (birth : Nat → Nat) :
    Graph → ConstraintState → Graph → ConstraintState → Prop where
  | nil (graph : Graph) (state : ConstraintState) : GrowingHistory ref birth graph state graph state
  | step {graph before middle target after}
      (change : ConstraintStep graph ref birth before middle)
      (rest : GrowingHistory ref birth graph middle target after) :
      GrowingHistory ref birth graph before target after
  | grow {graph next state target after}
      (extension : Extends graph next)
      (rest : GrowingHistory ref birth next state target after) :
      GrowingHistory ref birth graph state target after

theorem GrowingHistory.extension {ref birth graph first target last}
    (history : GrowingHistory ref birth graph first target last) : Extends graph target := by
  induction history with
  | nil graph state => exact Extends.refl graph
  | step change rest ih => exact ih
  | grow extension rest ih => exact extension.trans ih

theorem GrowingHistory.flatten {ref birth graph first target last}
    (history : GrowingHistory ref birth graph first target last) :
    ConstraintHistory target ref birth first last := by
  induction history with
  | nil graph state => exact .nil state
  | step change rest ih => exact .cons (rest.extension.step change) ih
  | grow extension rest ih => exact ih

theorem GrowingHistory.append {ref birth graph first middle midState target last}
    (left : GrowingHistory ref birth graph first middle midState)
    (right : GrowingHistory ref birth middle midState target last) :
    GrowingHistory ref birth graph first target last := by
  induction left with
  | nil => exact right
  | step change rest ih => exact .step change (ih right)
  | grow extension rest ih => exact .grow extension (ih right)

theorem GrowingHistory.of_fixed {ref birth graph first last}
    (history : ConstraintHistory graph ref birth first last) :
    GrowingHistory ref birth graph first graph last := by
  induction history with
  | nil state => exact .nil graph state
  | cons change rest ih => exact .step change ih

theorem GrowingHistory.accepted_sound {ref birth graph first target last certificate}
    (history : GrowingHistory ref birth graph first target last)
    (accepted : accepts target certificate last.obligations = true) :
    Extends graph target ∧ target.Valid ∧ target.Guarded ∧ Holds target first.obligations :=
  ⟨history.extension,accepted_original_demands history.flatten accepted⟩

theorem completed_growing_store_sound {graph refs store}
    (lawful : LawfulStore graph refs store) :
    let result := completedStore graph refs store
    ∀ {events ref birth target last certificate},
      GrowingHistory ref birth result.1 ⟨result.2,events⟩ target last →
      accepts target certificate last.obligations = true →
      Extends graph target ∧ target.Valid ∧ target.Guarded ∧ StoreSatisfied target refs store := by
  intro result events ref birth target last certificate history accepted
  have completed := completedStore_correct lawful
  exact ⟨completed.1.trans history.extension,
    history_store_sound (history.extension.decode_store completed.2) history.flatten accepted⟩

/-- One final graph/reference pullback serves every original use and client,
after computed completion and interleaved literal allocation/constraint steps. -/
theorem completed_growing_publication_with_clients
    {n count bounds beforeCap afterCap beforeUse afterUse roots uses q graph refs}
    {inventory clients : Store}
    (lawful : LawfulStore graph refs
      (inventory ++ clients.map (Constraint.rename (publicationTransport n count afterUse q))))
    (bounded : ScopedPublication.BoundsBounded n bounds)
    (images : ScopedPublication.InactiveImages n beforeUse afterUse q)
    (closed : ScopedPublication.StoppedClosed (bounds.map (ScopedPublication.Bound.rename q)) afterCap)
    (stops : ∀ k i, afterCap k i = false → afterUse k i = false)
    (useBounds : ∀ use, use ∈ uses → use < count)
    (coverage : ∀ clause,
      ScopedPublication.Published n (bounds.map (ScopedPublication.Bound.rename q)) afterCap afterUse
        (roots.map (ScopedPublication.Row.rename q)) uses clause → clause ∈ inventory) :
    let result := completedStore graph refs
      (inventory ++ clients.map (Constraint.rename (publicationTransport n count afterUse q)))
    ∀ {events ref birth target last certificate},
      GrowingHistory ref birth result.1 ⟨result.2,events⟩ target last →
      accepts target certificate last.obligations = true →
      Extends graph target ∧ target.Valid ∧ target.Guarded ∧
        PublishedSatisfied target (fun k i => refs k (publicationTransport n count afterUse q k i))
          n bounds beforeCap beforeUse roots uses ∧
        StoreSatisfied target (fun k i => refs k (publicationTransport n count afterUse q k i)) clients := by
  intro result events ref birth target last certificate history accepted
  have completed := completedStore_correct lawful
  exact ⟨completed.1.trans history.extension,
    publication_history_with_clients bounded images closed stops useBounds coverage
      (history.extension.decode_store completed.2) history.flatten accepted⟩

theorem GrowingHistory.decided_sound {ref birth graph first target last}
    (history : GrowingHistory ref birth graph first target last)
    (decided : LatticeDecision.decideDemands target last.obligations = true) :
    Extends graph target ∧ target.Valid ∧ target.Guarded ∧ Holds target first.obligations :=
  history.accepted_sound (certificate := LatticeDecision.constructCertificate target) decided

/-- No final decoder equation, terminal model, fixed-graph history, or finite
certificate is supplied: completion and certificate construction are executable. -/
theorem completed_decided_growing_store_sound {graph refs store}
    (lawful : LawfulStore graph refs store) :
    let result := completedStore graph refs store
    ∀ {events ref birth target last},
      GrowingHistory ref birth result.1 ⟨result.2,events⟩ target last →
      LatticeDecision.decideDemands target last.obligations = true →
      Extends graph target ∧ target.Valid ∧ target.Guarded ∧ StoreSatisfied target refs store := by
  intro result events ref birth target last history decided
  exact completed_growing_store_sound lawful
    (certificate := LatticeDecision.constructCertificate target) history decided

theorem completed_decided_growing_publication_with_clients
    {n count bounds beforeCap afterCap beforeUse afterUse roots uses q graph refs}
    {inventory clients : Store}
    (lawful : LawfulStore graph refs
      (inventory ++ clients.map (Constraint.rename (publicationTransport n count afterUse q))))
    (bounded : ScopedPublication.BoundsBounded n bounds)
    (images : ScopedPublication.InactiveImages n beforeUse afterUse q)
    (closed : ScopedPublication.StoppedClosed (bounds.map (ScopedPublication.Bound.rename q)) afterCap)
    (stops : ∀ k i, afterCap k i = false → afterUse k i = false)
    (useBounds : ∀ use, use ∈ uses → use < count)
    (coverage : ∀ clause,
      ScopedPublication.Published n (bounds.map (ScopedPublication.Bound.rename q)) afterCap afterUse
        (roots.map (ScopedPublication.Row.rename q)) uses clause → clause ∈ inventory) :
    let result := completedStore graph refs
      (inventory ++ clients.map (Constraint.rename (publicationTransport n count afterUse q)))
    ∀ {events ref birth target last},
      GrowingHistory ref birth result.1 ⟨result.2,events⟩ target last →
      LatticeDecision.decideDemands target last.obligations = true →
      Extends graph target ∧ target.Valid ∧ target.Guarded ∧
        PublishedSatisfied target (fun k i => refs k (publicationTransport n count afterUse q k i))
          n bounds beforeCap beforeUse roots uses ∧
        StoreSatisfied target (fun k i => refs k (publicationTransport n count afterUse q k i)) clients := by
  intro result events ref birth target last history decided
  exact completed_growing_publication_with_clients lawful bounded images closed stops useBounds coverage
    (certificate := LatticeDecision.constructCertificate target) history decided

/-! Decompose a recursive Function, append a fresh tuple whose entries include
both lattice constructors, then insert/discharge a demand on that fresh node. -/
def grownLattice : Graph := appendNode recursiveLatticeGraph (.structural (.tuple [4,5]))

def initial : ConstraintState := ⟨[⟨.value,0,1⟩],[]⟩
def children : ConstraintState :=
  ⟨[⟨.value,3,2⟩,⟨.effect,1,0⟩,⟨.effect,1,0⟩,⟨.value,4,5⟩],[]⟩

theorem interleaved_history : GrowingHistory (fun _ _ => False) (fun _ => 0)
    recursiveLatticeGraph initial grownLattice children := by
  apply GrowingHistory.step
    (ConstraintStep.decompose ⟨.value,0,1⟩ children.obligations [] [] rfl)
  apply GrowingHistory.grow (appendNode_extends recursiveLatticeGraph (.structural (.tuple [4,5])))
  apply GrowingHistory.step (ConstraintStep.insertLower .value 9 9 children)
  apply GrowingHistory.step
    (ConstraintStep.reflexive .value 9 children.obligations [] ⟨.structural (.tuple [4,5]),rfl⟩)
  exact .nil _ _

theorem interleaved_accepted :
    accepts grownLattice recursiveLatticeCertificate children.obligations = true := rfl

theorem interleaved_original_solved :
    Extends recursiveLatticeGraph grownLattice ∧ grownLattice.Valid ∧ grownLattice.Guarded ∧
      Holds grownLattice initial.obligations :=
  interleaved_history.accepted_sound interleaved_accepted

end YulangClosure.SimpleSub.LatticeGrowingInference
