import Yulang.GeneralVersionedChildEndpointCut315
import Yulang.GeneralNominalVersionedExpressionFrame236

set_option backward.isDefEq.respectTransparency false
/-! Isolated representation experiment. An endpoint read key injects the
actual ordered source IDs used by that expression, including the reset to
actual mode inside nominal applications. This is not a change to the
compiler, the child semantics, or the actual B4 source boundary. -/
namespace Yulang.GeneralVersionedEndpointAddress315
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalVersionedExpressionFrame236 (reads variableSource variable_value value_eq)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralNominalIdentities (Origin source source_identity)
open GeneralNominalAllocation (origin)
open GeneralNominalAggregateVersion231 (code code_injective)
open GeneralNominalMaterialization (Mode)

inductive Side where
  | lower
  | upper
  deriving DecidableEq

def Side.purpose : Side → Nat
  | .lower => 10
  | .upper => 11

def Side.mode : Side → Mode
  | .lower => .lower
  | .upper => .upper

def footprint (p : Plan roles) (mode : Mode) (expr : Expr) : List Nat :=
  (reads mode expr).map fun pair => variableSource p pair.1 pair.2

def version (position : Nat) (sources : List Nat) : Nat :=
  GeneralNominalIdentities.pair position (code (sources.map (fun n => (n,0))))

theorem encode_names {a b : List Nat}
    (same : a.map (fun n => (n,0)) = b.map (fun n => (n,0))) : a = b := by
  have exacts := congrArg (List.map (fun n : Nat × Nat => n.1)) same
  simpa [List.map_map,Function.comp_def] using exacts

theorem version_injective {a b : Nat} {as bs : List Nat} (same : version a as = version b bs) :
    a = b ∧ as = bs := by
  have decoded : (a,code (as.map (fun n => (n,0)))) = (b,code (bs.map (fun n => (n,0)))) :=
    GeneralNominalIdentities.pair_injective same
  exact ⟨(Prod.mk.inj decoded).1,encode_names (code_injective (Prod.mk.inj decoded).2)⟩

def key (p : Plan roles) (side : Side) (clause pos : Nat) (expression : Expr) : Origin :=
  origin p.packet.site.occurrence.identity p.packet.declaration.id side.purpose clause
    (version pos (footprint p side.mode expression))

def atCell (p : Plan roles) (side : Side) (clause pos : Nat) (expression : Expr) :=
  source p.packet.context.state.seed (key p side clause pos expression)

theorem footprint_read {p q : Plan roles} {mode : Mode} {e : Expr}
    (same : footprint p mode e = footprint q mode e) (r : Mode × Nat) (used : r ∈ reads mode e) :
    variableSource p r.1 r.2 = variableSource q r.1 r.2 := by
  obtain ⟨i,range,atIndex⟩ := List.mem_iff_getElem.mp used
  have cells := congrArg (fun l : List Nat => l[i]?) same
  simp only [footprint,List.getElem?_map,List.getElem?_eq_getElem range,atIndex,Option.map_some,Option.some.injEq] at cells
  exact cells

theorem fields {p q : Plan roles} {a b : Side} {c d i j : Nat} {e f : Expr}
    (seed : p.packet.context.state.seed = q.packet.context.state.seed)
    (same : atCell p a c i e = atCell q b d j f) :
    p.packet.site.occurrence.identity = q.packet.site.occurrence.identity ∧
    p.packet.declaration.id = q.packet.declaration.id ∧ a = b ∧ c = d ∧ i = j ∧
    footprint p a.mode e = footprint q b.mode f := by
  unfold atCell at same
  rw [seed] at same
  have coords := (source_identity _ _ _).mp same
  have sideTag := congrArg (fun k : Origin => k.2.2.1) coords
  change a.purpose = b.purpose at sideTag
  have sideEq : a = b := by cases a <;> cases b <;> first | rfl | cases sideTag
  have owner := congrArg Prod.fst coords
  have declaration := congrArg (fun k : Origin => k.2.1) coords
  have clause := congrArg (fun k : Origin => k.2.2.2.1) coords
  have versionEq : version i (footprint p a.mode e) = version j (footprint q b.mode f) :=
    congrArg (fun k : Origin => k.2.2.2.2) coords
  have stored := version_injective versionEq
  exact ⟨owner,declaration,sideEq,clause,stored.1,stored.2⟩

theorem coherent {p q : Plan roles} {side : Side} {c d i j : Nat} {e : Expr}
    (seed : p.packet.context.state.seed = q.packet.context.state.seed)
    (same : atCell p side c i e = atCell q side d j e) (m : Assignment) :
    value (variables p m) side.mode e = value (variables q m) side.mode e := by
  have equal := (fields seed same).2.2.2.2.2
  apply value_eq
  intro read used
  simp only [variable_value,footprint_read equal read used]

theorem outside_legacy (p : Plan roles) (side : Side) (c i : Nat) (expr : Expr)
    {other : Origin} (small : other.2.2.1 ≤ 9) :
    atCell p side c i expr ≠ source p.packet.context.state.seed other := by
  intro same
  have same := (source_identity _ _ _).mp same
  have tag := congrArg (fun k : Origin => k.2.2.1) same
  change side.purpose = other.2.2.1 at tag
  cases side <;> simp [Side.purpose] at tag <;> omega

end Yulang.GeneralVersionedEndpointAddress315
