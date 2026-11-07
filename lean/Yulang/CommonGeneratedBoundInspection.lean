import Yulang.CommonSymbolicBoundRigid
import Yulang.CommonPresenceConstraintGraph
import Yulang.PresenceGeneratedRigidShape

/-!
# Ordinary fixed-bound inspection of actual shared source nodes

The adapter retains the existing pool's child and row IDs. A source
intersection has no supported one-layer decomposition and returns `none`;
the generated lower-endpoint invariant proves that this case is absent.
No instantiated value is inspected by the compiler.

Known source constructors against required/width targets are exact for all
independent assignments. Optional targets require the stated local width
inequality. Original constructor equations transfer these laws to node
values, and generated target heads use the same ordinary bound references.
The output contains no dynamic Boolean or profile checks.
-/

namespace Yulang.CommonGeneratedBoundInspection

open Common (Ty Row Subtype Equivalent)
open Core.PresenceGeneration (TyTerm RowTerm)
open PresenceOpenTailGenerationLowering (Pool subterms)
open CommonPresenceConstraintGraph (lowerNode rowEval Realizes)
open CommonSymbolicBoundInspection
open PresenceGeneratedRigidShape (lower upper)

variable {m : Nat}

abbrev PoolSource (pool : Pool m) := Source (RowTerm (Fin m)) (Fin pool.size)
abbrev PoolRigid (pool : Pool m) := Rigid (RowTerm (Fin m)) (Fin pool.size)
abbrev PoolOutput (pool : Pool m) := Output (RowTerm (Fin m)) (Fin pool.size)

/-- Every child reference comes from the original collector. -/
def ofNode (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    Option (PoolSource pool) :=
  match term with
  | .var index => some (.reference (.original (pool.input index)))
  | .union first last => some (.union
      (.original (pool.child _ member first (by simp [subterms])))
      (.original (pool.child _ member last (by simp [subterms]))))
  | .inter _ _ => none
  | .bottom => some (.rigid .bottom)
  | .top => some (.rigid .top)
  | .base scalar => some (.rigid (.base scalar))
  | .pair first last => some (.rigid (.pair
      (.original (pool.child _ member first (by simp [subterms])))
      (.original (pool.child _ member last (by simp [subterms])))))
  | .emptyRecord => some .width
  | .exactEmpty => some .exactEmpty
  | .required label payload => some (.record label
      (.original (pool.child _ member payload (by simp [subterms]))) .width)
  | .record label payload tail => some (.record label
      (.original (pool.child _ member payload (by simp [subterms])))
      (.original (pool.child _ member tail (by simp [subterms]))))
  | .recordDefault label source fallback => some (.recordDefault label
      (.original (pool.child _ member source (by simp [subterms])))
      (.original (pool.child _ member fallback (by simp [subterms]))))
  | .variant label payload => some (.rigid (.variant label
      (.original (pool.child _ member payload (by simp [subterms])))))
  | .arrow input incoming output outgoing => some (.rigid (.arrow
      (.original (pool.child _ member input (by simp [subterms]))) incoming
      (.original (pool.child _ member output (by simp [subterms]))) outgoing))

theorem ofNode_some (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (shape : lower term = true) : ∃ source, ofNode pool term member = some source := by
  cases term <;> first | exact ⟨_, rfl⟩ | cases shape

/-- Literal equality before imposing any original constructor equation. -/
theorem ofNode_eval (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (source : PoolSource pool) (found : ofNode pool term member = some source)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) :
    source.eval (rowEval rows) values = (lowerNode pool term member).eval rows values := by
  cases term <;> simp only [ofNode] at found <;> cases found <;> rfl

def withNode (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (inspector : PoolSource pool → PoolOutput pool) : PoolOutput pool :=
  match ofNode pool term member with
  | none => []
  | some source => inspector source

def required (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (label : Nat) (payload : Option (Fin pool.size)) : PoolOutput pool :=
  withNode pool term member (fun source => inspectRequired source label payload)

def optional (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (label : Nat) (payload : Option (Fin pool.size)) : PoolOutput pool :=
  withNode pool term member (fun source => inspectOptional source label payload)

def width (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) : PoolOutput pool :=
  withNode pool term member inspectWidth

def rigid (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (target : PoolRigid pool) (targetRef : BoundRef (Fin pool.size)) : PoolOutput pool :=
  withNode pool term member (fun source => inspectRigid source target targetRef)

def NodeWidth (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (values : Fin pool.size → Ty) : Prop :=
  match ofNode pool term member with
  | none => False
  | some source => LocalWidth values source

theorem nodeWidth_record (pool : Pool m) (label : Nat) (payload tail : TyTerm (Fin m))
    (member : TyTerm.record label payload tail ∈ pool.terms) (values : Fin pool.size → Ty) :
    NodeWidth pool (.record label payload tail) member values ↔
      Subtype (values (pool.child _ member tail (by simp [subterms]))) Common.emptyRecord := Iff.rfl

theorem nodeWidth_default (pool : Pool m) (label : Nat) (source fallback : TyTerm (Fin m))
    (member : TyTerm.recordDefault label source fallback ∈ pool.terms) (values : Fin pool.size → Ty) :
    NodeWidth pool (.recordDefault label source fallback) member values ↔
      Subtype (values (pool.child _ member source (by simp [subterms]))) Common.emptyRecord := Iff.rfl

theorem nodeWidth_required (pool : Pool m) (label : Nat) (payload : TyTerm (Fin m))
    (member : TyTerm.required label payload ∈ pool.terms) (values : Fin pool.size → Ty) :
    NodeWidth pool (.required label payload) member values := Common.subtype_refl _

theorem required_node_exact (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (shape : lower term = true) (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (label : Nat) (payload : Option (Fin pool.size)) :
    Holds (rowEval rows) values (required pool term member label payload) ↔
      Subtype ((lowerNode pool term member).eval rows values)
        ((BoundRef.required label payload).eval values) := by
  obtain ⟨source, found⟩ := ofNode_some pool term member shape
  simp only [required, withNode, found]
  rw [← ofNode_eval pool term member source found rows values]
  exact inspect_required_exact _ _ _ _ _

theorem optional_node_exact (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (shape : lower term = true) (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (width : NodeWidth pool term member values) (label : Nat) (payload : Option (Fin pool.size)) :
    Holds (rowEval rows) values (optional pool term member label payload) ↔
      Subtype ((lowerNode pool term member).eval rows values)
        ((BoundRef.optional label payload).eval values) := by
  obtain ⟨source, found⟩ := ofNode_some pool term member shape
  simp only [optional, withNode, found]
  rw [← ofNode_eval pool term member source found rows values]
  exact inspect_optional_exact _ _ _ _ _ (by simpa only [NodeWidth, found] using width)

theorem width_node_exact (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (shape : lower term = true) (rows : Fin m → Row) (values : Fin pool.size → Ty) :
    Holds (rowEval rows) values (width pool term member) ↔
      Subtype ((lowerNode pool term member).eval rows values) Common.emptyRecord := by
  obtain ⟨source, found⟩ := ofNode_some pool term member shape
  simp only [width, withNode, found]
  rw [← ofNode_eval pool term member source found rows values]
  exact inspect_width_exact _ _ _

theorem rigid_node_exact (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (shape : lower term = true) (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (target : PoolRigid pool) (targetRef : BoundRef (Fin pool.size))
    (targetSame : Equivalent (target.eval (rowEval rows) (BoundRef.eval values)) (targetRef.eval values)) :
    Holds (rowEval rows) values (rigid pool term member target targetRef) ↔
      Subtype ((lowerNode pool term member).eval rows values)
        (target.eval (rowEval rows) (BoundRef.eval values)) := by
  obtain ⟨source, found⟩ := ofNode_some pool term member shape
  simp only [rigid, withNode, found]
  rw [← ofNode_eval pool term member source found rows values]
  exact inspect_rigid_exact _ _ _ _ _ targetSame

theorem optional_realized_exact (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (shape : lower term = true) (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (realizes : Realizes pool rows values) (width : NodeWidth pool term member values)
    (label : Nat) (payload : Option (Fin pool.size)) :
    Holds (rowEval rows) values (optional pool term member label payload) ↔
      Subtype (values (pool.reference term member)) ((BoundRef.optional label payload).eval values) :=
  (optional_node_exact pool term member shape rows values width label payload).trans
    (subtype_congr (CommonPresenceConstraintGraph.realizes_reference pool rows values realizes term member)
      (Common.equivalent_refl _))

/-- Fixed target dispatch for actual generated ordinary upper heads. -/
def inspect (pool : Pool m) (source target : TyTerm (Fin m))
    (sourceMember : source ∈ pool.terms) (targetMember : target ∈ pool.terms) : PoolOutput pool :=
  match target with
  | .var index => [[edge (.original (pool.reference source sourceMember)) (.original (pool.input index))]]
  | .emptyRecord => width pool source sourceMember
  | .required label payload => required pool source sourceMember label
      (some (pool.child _ targetMember payload (by simp [subterms])))
  | .base scalar => rigid pool source sourceMember (.base scalar) (.original (pool.reference _ targetMember))
  | .pair first last => rigid pool source sourceMember
      (.pair (.original (pool.child _ targetMember first (by simp [subterms])))
        (.original (pool.child _ targetMember last (by simp [subterms]))))
      (.original (pool.reference _ targetMember))
  | .arrow input incoming output outgoing => rigid pool source sourceMember
      (.arrow (.original (pool.child _ targetMember input (by simp [subterms]))) incoming
        (.original (pool.child _ targetMember output (by simp [subterms]))) outgoing)
      (.original (pool.reference _ targetMember))
  | .bottom => rigid pool source sourceMember .bottom (.original (pool.reference _ targetMember))
  | .top => [[]]
  | .variant label payload => rigid pool source sourceMember
      (.variant label (.original (pool.child _ targetMember payload (by simp [subterms]))))
      (.original (pool.reference _ targetMember))
  | _ => []

/-- For generated ordinary targets, no local width premise is necessary.
Only the independent original constructor equations and endpoint syntax
invariant are used; no profile or dynamic Boolean constraint is retained. -/
theorem inspect_exact (pool : Pool m) (source target : TyTerm (Fin m))
    (sourceMember : source ∈ pool.terms) (targetMember : target ∈ pool.terms)
    (sourceShape : lower source = true) (targetShape : upper target = true)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) (realizes : Realizes pool rows values) :
    Holds (rowEval rows) values (inspect pool source target sourceMember targetMember) ↔
      Subtype (values (pool.reference source sourceMember)) (values (pool.reference target targetMember)) := by
  have sourceSame := CommonPresenceConstraintGraph.realizes_reference pool rows values realizes source sourceMember
  have targetSame := CommonPresenceConstraintGraph.realizes_reference pool rows values realizes target targetMember
  cases target with
  | var index => simp only [inspect, holds_edge, BoundRef.eval, Pool.input]
  | emptyRecord =>
      exact (width_node_exact pool source sourceMember sourceShape rows values).trans
        (subtype_congr sourceSame targetSame)
  | required label payload =>
      exact (required_node_exact pool source sourceMember sourceShape rows values label
        (some (pool.child _ targetMember payload (by simp [subterms])))).trans
        (subtype_congr sourceSame targetSame)
  | base scalar =>
      exact (rigid_node_exact pool source sourceMember sourceShape rows values (.base scalar)
        (.original (pool.reference _ targetMember)) targetSame).trans (subtype_congr sourceSame targetSame)
  | pair first last =>
      exact (rigid_node_exact pool source sourceMember sourceShape rows values
        (.pair (.original (pool.child _ targetMember first (by simp [subterms])))
          (.original (pool.child _ targetMember last (by simp [subterms]))))
        (.original (pool.reference _ targetMember)) targetSame).trans (subtype_congr sourceSame targetSame)
  | arrow input incoming output outgoing =>
      exact (rigid_node_exact pool source sourceMember sourceShape rows values
        (.arrow (.original (pool.child _ targetMember input (by simp [subterms]))) incoming
          (.original (pool.child _ targetMember output (by simp [subterms]))) outgoing)
        (.original (pool.reference _ targetMember)) targetSame).trans (subtype_congr sourceSame targetSame)
  | _ => cases targetShape

theorem withNode_plain (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (inspector : PoolSource pool → PoolOutput pool) (plain : ∀ source, Plain (inspector source)) :
    Plain (withNode pool term member inspector) := by
  unfold withNode
  cases ofNode pool term member with
  | none => simp [Plain]
  | some source => exact plain source

theorem required_plain (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (label : Nat) (payload : Option (Fin pool.size)) : Plain (required pool term member label payload) :=
  withNode_plain pool term member _ (fun source => inspect_required_plain source label payload)

theorem optional_plain (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (label : Nat) (payload : Option (Fin pool.size)) : Plain (optional pool term member label payload) :=
  withNode_plain pool term member _ (fun source => inspect_optional_plain source label payload)

theorem width_plain (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    Plain (width pool term member) := withNode_plain pool term member _ inspect_width_plain

theorem rigid_plain (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (target : PoolRigid pool) (targetRef : BoundRef (Fin pool.size)) :
    Plain (rigid pool term member target targetRef) :=
  withNode_plain pool term member _ (fun source => inspect_rigid_plain source target targetRef)

theorem inspect_plain (pool : Pool m) (source target : TyTerm (Fin m))
    (sourceMember : source ∈ pool.terms) (targetMember : target ∈ pool.terms) :
    Plain (inspect pool source target sourceMember targetMember) := by
  cases target with
  | var => simp [inspect, Plain, edge, PlainCheck]
  | emptyRecord => exact width_plain _ _ _
  | required => exact required_plain _ _ _ _ _
  | base | pair | arrow | bottom | variant => exact rigid_plain _ _ _ _ _
  | top | exactEmpty | union | inter | record | recordDefault => simp [inspect, Plain]

end Yulang.CommonGeneratedBoundInspection
