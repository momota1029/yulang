import Yulang.GeneralDeclarativeWitnessTypedIndex354
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTypedJoint354
open GeneralDeclarativeWitnessCovariantOrigin353 (Row Problem Valuation View HasView assigned)
open GeneralDeclarativeWitnessCovariantCanonical353 (valuation view_for_every_model)
open GeneralDeclarativeWitnessTypedForest354 (Leaf Leaves Accepted)
open GeneralDeclarativeWitnessTypedChild354 (downstream physical_target)
open GeneralDeclarativeWitnessTypedSound354 (released_row_in_child)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂ Dictionary)
open GeneralDeclarativeWitnessCovariantViews353 (View.head)
open GeneralDeclarativeWitnessCovariantMetadata353 (table)
open CommonDeclaredNominalInspection (DeclaredSubtype)

def leafRows {p s w i d} (a : Leaf p s w i d) :=
  (downstream (p.atChild a.plan i) a.linked.writer.output.state a.linked.demand a.linked.emitted.atWrite.typed.row).rows

def leavesRows {p s w i ds} : Leaves p s w i ds → List Row
  | .nil => []
  | .cons a tail => leafRows a ++ leavesRows tail

local instance : BEq Row := ⟨fun a b => decide (a=b)⟩
local instance : LawfulBEq Row where
  eq_of_beq := of_decide_eq_true
  rfl := decide_eq_true rfl

def fusion (rs : List Row) : List Row := rs.eraseDups

def compatible (rs : List Row) : Bool := decide ((fusion rs).map Row.root).Nodup

def shared (p : Problem) (rs : List Row) (m : Assignment) : Valuation :=
  valuation {p with rows := fusion rs} m

theorem author_rows {p : Problem} {rs : List Row} (same : compatible rs = true) (m : Assignment) :
    ∀ row ∈ rs, HasView m (shared p rs m) row := by
  refine fun row found =>
    view_for_every_model {p with rows := fusion rs} m (of_decide_eq_true same) row
      (List.mem_eraseDups.mpr found)

def Supported (s : State) (m : Assignment) (v : Valuation) (d : Demand) (k : Dictionary) : Prop :=
  ∃ (i : GeneralDeclarativeWitnessTypedChild354.Input) (w : GeneralDeclarativeWitnessTypedChild354.Wire)
    (a : GeneralDeclarativeWitnessTypedChild354.Linked i s w) (l c h : View),
      a.demand = d ∧ k = .node a.receiver.facts.center.decl.id [] ∧ a.receiver.compiler.compiled.kids = [] ∧
      v a.receiver.facts.arg.lower = some l ∧ v a.receiver.facts.arg.center = some c ∧
      v a.receiver.facts.arg.upper = some h ∧
      DeclaredSubtype (table w.childHead.center.box) (View.head l) (View.head c) ∧
      DeclaredSubtype (table w.childHead.center.box) (View.head c) (View.head h) ∧
      a.receiver.facts.arg.center = a.emitted.atWrite.demand.target ∧
      c.tag = a.emitted.atWrite.typed.tag ∧ c.box = a.emitted.atWrite.typed.box ∧
      Common.Equivalent c.payload
        (.union (assigned m a.writer.output.source.anchor.first.valueName).1
                (assigned m a.writer.output.source.anchor.last.valueName).1)

theorem shared_intervals {p s w i ds} (xs : Leaves p s w i ds)
    (m : Assignment) (fit : Models s m) (v : Valuation)
    (sub : ∀ r ∈ leavesRows xs, HasView m v r) : All₂ (Supported s m v) ds xs.dicts := by
  induction xs with
  | nil => exact .nil
  | cons child more ih =>
    have per : ∀ r ∈ leafRows child, HasView m v r := fun r found => sub r (List.mem_append_left _ found)
    have prior := GeneralDeclarativeWitnessReceipt349.same_model child.linked.writer.check m fit
    obtain ⟨lo,mid,hi,l,c,h,_,lc,ch⟩ :=
      GeneralDeclarativeWitnessCovariantInterval353.typed_interval child.linked.receiver.facts m v prior per
    obtain ⟨actual,known,tag,box,payload⟩ := per _ (released_row_in_child child.linked)
    have physical := physical_target child.linked
    rw [physical] at c
    have rowName : child.linked.emitted.atWrite.typed.row.root = child.linked.emitted.atWrite.demand.target := rfl
    rw [rowName] at known
    have eq := Option.some.inj (known.symm.trans c)
    subst actual
    rw [← physical] at c
    have actualPayload := GeneralDeclarativeWitnessTypedRelease354.actual_payload child.linked.emitted m fit
    have joined := Common.equivalent_trans payload
      ⟨CommonNominalRegularErasure.subtype_monotone _ _ actualPayload.1,
        CommonNominalRegularErasure.subtype_monotone _ _ actualPayload.2⟩
    exact .cons ⟨_,_,child.linked,lo,mid,hi,child.exactDemand,rfl,child.noMore,l,c,h,lc,ch,physical,tag,box,joined⟩
      (ih fun r found => sub r (List.mem_append_right _ found))

theorem one_valuation {p s w} (a : Accepted p s w)
    (coherence : compatible (leavesRows a.children) = true) (m : Assignment) (fit : Models s m) :
    All₂ (Supported s m (shared p.producer (leavesRows a.children) m)) a.parent.output.children a.children.dicts :=
  shared_intervals a.children m fit _ (author_rows coherence m)

end Yulang.GeneralDeclarativeWitnessTypedJoint354
