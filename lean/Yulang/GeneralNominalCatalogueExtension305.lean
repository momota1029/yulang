import Yulang.GeneralNominalReportContext305

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalCatalogueExtension305
open GeneralNormalizedObservation (Head Shape Snapshot)
open GeneralNominalState (State Known)
open GeneralNominalRefinements (Refines)
open GeneralNominalReportCoordinates305 (Coordinates HeadData observed nominalRead nominalMove)
open GeneralNominalRecursiveCandidates (Context)

def shapes (old : Fin k → Shape) (extra : Shape) : Fin (k+1) → Shape :=
  Fin.lastCases extra old

theorem shapes_old (old : Fin k → Shape) (extra : Shape) (i : Fin k) :
    shapes old extra i.castSucc = old i := by simp [shapes]

theorem shapes_new (old : Fin k → Shape) (extra : Shape) :
    shapes old extra (Fin.last k) = extra := by simp [shapes]

theorem shapes_inj (old : Fin k → Shape) (extra : Shape) (inj : Function.Injective old)
    (fresh : ∀ i, old i ≠ extra) : Function.Injective (shapes old extra) := by
  intro i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => intro _; rfl
    | cast j => simp only [shapes_new,shapes_old]; exact fun h => False.elim (fresh j h.symm)
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp only [shapes_old,shapes_new]; exact fun h => False.elim (fresh i h)
    | cast j =>
      simp only [shapes_old]
      exact fun h => congrArg Fin.castSucc (inj h)

def transferChildren {a b : Shape} (eq : a = b) (children : Fin b.arity → Fin slots) :
    Fin a.arity → Fin slots :=
  cast (congrArg (fun t : Shape => Fin t.arity → Fin slots) eq).symm children

theorem transfer_term {a b : Shape} (eq : a = b) (children : Fin b.arity → Fin slots) :
    a.term (transferChildren eq children) = b.term children := by
  cases eq
  rfl

theorem transfer_list {a b : Shape} (eq : a = b) (children : Fin b.arity → Fin slots) :
    List.ofFn (transferChildren eq children) = List.ofFn children := by
  cases eq
  rfl

def extendHead {old : Fin k → Shape} (extra : Shape) :
    Head old slots → Head (shapes old extra) slots
  | .deferred why => .deferred why
  | .scalar base => .scalar base
  | .structural i children => .structural i.castSucc (transferChildren (shapes_old old extra i) children)

theorem head_term {old : Fin k → Shape} (extra : Shape) (h : Head old slots) :
    (extendHead extra h).term = h.term := by
  cases h with
  | deferred => rfl
  | scalar => rfl
  | structural kind children =>
    simp only [extendHead,Head.term,transfer_term]

theorem head_node {old : Fin k → Shape} (extra : Shape) (h : Head old slots) :
    (extendHead extra h).node = h.node := by
  cases h with
  | deferred => rfl
  | scalar => rfl
  | structural kind children =>
    simp only [extendHead,Head.node,Fin.val_castSucc,transfer_list]

def extendView (v : Snapshot base) (extra : Shape) (canonical : extra.Canonical)
    (fresh : ∀ i, v.shapes i ≠ extra) : Snapshot base where
  kinds := v.kinds+1
  shapes := shapes v.shapes extra
  shapes_injective := shapes_inj v.shapes extra v.shapes_injective fresh
  canonical := by
    intro i
    induction i using Fin.lastCases with
    | last => simpa only [shapes_new] using canonical
    | cast i => simpa only [shapes_old] using v.canonical i
  heads := fun slot => extendHead extra (v.heads slot)
  checked := fun slot term found => v.checked slot term ((head_term extra _).symm.trans found)

def extend (s : State) (extra : Shape) (canonical : extra.Canonical)
    (fresh : ∀ i, s.view.shapes i ≠ extra) : State where
  base := s.base
  view := extendView s.view extra canonical fresh
  constructors := s.constructors
  nominals := s.nominals
  catalogue := s.catalogue
  bodies_opaque := by
    intro i d listed
    change extendHead extra (s.view.heads i) = _
    rw [s.bodies_opaque i d listed]
    rfl
  seed := s.seed
  reserved := s.reserved
  allocated := s.allocated
  ordinary := s.ordinary

theorem known_iff (s : State) (extra : Shape) (canonical : extra.Canonical)
    (fresh : ∀ i, s.view.shapes i ≠ extra) (id : Nat) :
    Known s id ↔ Known (extend s extra canonical fresh) id := by
  have graph (i : Fin s.base.slots) : (extend s extra canonical fresh).view.graph i = s.view.graph i :=
    head_node extra (s.view.heads i)
  constructor
  · rintro ⟨i,idEq,seen⟩
    refine ⟨i,idEq,?_⟩
    rwa [graph i]
  · rintro ⟨i,idEq,seen⟩
    refine ⟨i,idEq,?_⟩
    rwa [graph i] at seen

def equivalent (old : Context) (extra : Shape) (canonical : extra.Canonical)
    (fresh : ∀ i, old.state.view.shapes i ≠ extra) :
    GeneralNominalReportContext305.EquivalentContexts old ⟨extend old.state extra canonical fresh,old.interpretation⟩ := by
  let s := old.state
  let t := extend s extra canonical fresh
  let f := GeneralNominalRefinements.refl s
  refine ⟨⟨f.base,f.heads,f.nominals,f.ordinary,fun id => (known_iff s extra canonical fresh id).mp,
    f.reserved,f.allocated,rfl,rfl⟩,
    ⟨f.base,f.heads,f.nominals,f.ordinary,fun id => (known_iff s extra canonical fresh id).mpr,
    f.reserved,f.allocated,rfl,rfl⟩,⟨id,fun _ => rfl,?_,?_⟩,rfl⟩
  · intro i
    unfold observed
    simp only [extend, extendView, id_eq]
    cases s.view.heads i with
    | deferred => rfl
    | scalar => rfl
    | structural kind children =>
      simp only [extendHead,HeadData.move,shapes_old,transfer_list,List.map_id]
  · intro i
    unfold nominalRead nominalMove
    change (s.nominals i).map _ = Option.map _ ((s.nominals i).map _)
    cases s.nominals i with
    | none => rfl
    | some d =>
      simp only [Option.map_some]
      congr 1
      cases GeneralNominalRecursiveInspection.typeArguments d.arguments with
      | none => rfl
      | some xs =>
        rw [Option.map_some]
        change (d.declaration.name,some xs) =
          (d.declaration.name,some (xs.map (fun pair => (pair.1,pair.2))))
        simp

end Yulang.GeneralNominalCatalogueExtension305
