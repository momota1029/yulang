import Yulang.GeneralRebaseTreeSeedFrame272

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseTreeSeedExtract272
open CommonNominalFullCarrier
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalRecursiveInspection (Test)
open GeneralNominalOriginTerms (arity project same_symm)
open GeneralNominalFiniteMeaning (At assemble build childMode)
open GeneralRebaseStructuralOrigin270 (Slots)
open GeneralRebaseNominalOrigin269 (Raw origin)
open GeneralRebaseOriginNegativeTags270 (sourceSlot sourceSlot_sound)
open GeneralRebaseTreeSeedFrame272 (Frame describe describe_sound)
open GeneralRebaseFiniteTree272 (Tree Canonical value)
open GeneralRebaseTreeInterpreter272 (Source)
open GeneralRebaseUniformTree272 (Uniform)
open GeneralRebaseTreeProjection272 (transport_value)

def fill (test : Test) (slots : Fin (arity test) → Option Tree) : Option Tree :=
 if present : ∀ i, (slots i).isSome = true then
   some (.node test (fun i => (slots i).get (present i)))
 else none

theorem filled (test : Test) (slots : Fin (arity test) → Option Tree) (out : Tree)
 (known : fill test slots = some out) :
 ∃ children, out = .node test children ∧ ∀ i, slots i = some (children i) := by
 unfold fill at known
 split at known
 · rename_i present
   refine ⟨fun i => (slots i).get (present i),(Option.some.inj known).symm,?_⟩
   intro i
   exact (Option.some_get (present i)).symm
 · contradiction

def extract (state : State roles) : Nat → Slots state → Option Tree
 | 0,_ => none
 | n+1,slot =>
   match describe state slot with
   | none => none
   | some f => fill f.test (fun i => (f.children i).bind (extract state n))

theorem extract_sound (state : State roles) (fuel : Nat) (s : Slots state) (out : Tree)
 (computed : extract state fuel s = some out) :
 Canonical out ∧ (∀ m, Models state m → Equivalent (m ((Raw state).base.source s)).1 (value out)) := by
 induction fuel generalizing s out with
 | zero => contradiction
 | succ fuel ih =>
   unfold extract at computed
   split at computed
   · contradiction
   · rename_i f has
     obtain ⟨kids,rfl,hit⟩ := filled f.test _ out computed
     have frame := describe_sound state s f has
     have child (i : Fin (arity f.test)) :
       ∃ target, f.children i = some target ∧ Canonical (kids i) ∧
       (∀ m, Models state m → Equivalent (m ((Raw state).base.source target)).1 (value (kids i))) := by
       obtain ⟨d,src,checked⟩ := Option.bind_eq_some_iff.mp (hit i)
       exact ⟨d,src,ih d (kids i) checked⟩
     refine ⟨⟨frame.1,fun i => by obtain ⟨_,_,cert,_⟩ := child i; exact cert⟩,?_⟩
     intro m valid
     have each (i : Fin (arity f.test)) :
       At m (childMode f.test .actual) (project (origin state s) f.test i) (value (kids i)) := by
       have mode : childMode f.test .actual = .actual := by cases f.test <;> rfl
       rw [mode]
       obtain ⟨dst,here,_,ok⟩ := child i
       have matched := frame.2.2 i dst here m valid
       exact transport_value m (origin state dst) _ _ _ (.source _) (ok m valid) (same_symm matched)
     have all := assemble f.test .actual (fun i => value (kids i))
       (GeneralNominalReadbackFunctionality.source_unique m _) (frame.2.1 m valid) each
     exact all.2 _ (.source _)

def seed (state : State roles) (fuel : Nat) : Source :=
 fun id => (sourceSlot state id).bind (extract state fuel)

theorem seed_uniform (state : State roles) (fuel : Nat) : Uniform state (seed state fuel) := by
 intro m valid id tree known
 obtain ⟨slot,found,computed⟩ := Option.bind_eq_some_iff.mp known
 have cert := extract_sound state fuel slot tree computed
 refine ⟨cert.1,?_⟩
 have same := GeneralNominalRecursiveInspection.Origin.source.inj (sourceSlot_sound state id slot found)
 rw [← same]
 exact cert.2 m valid

end Yulang.GeneralRebaseTreeSeedExtract272
