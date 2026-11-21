import Yulang.GeneralVersionedIdentityCenters312

set_option backward.isDefEq.respectTransparency false
/-! Every actual mixed alias edge records source-centered input agreement.
Transport it along the trace and through the alias closure in one model. -/
namespace Yulang.GeneralVersionedAliasCenters312
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models initial)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralDictionaryDefaultIdentityCenters214 (CentersSame)
open GeneralDictionaryDefaultAliasCenters215 (same_inputs centers_symm centers_trans)
open GeneralNominalSaturationState (Alias)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

def Origins (state : State roles) : Prop :=
  ∀ edge ∈ state.core.erased.current.aliases,
    ∃ first ∈ state.core.sites, ∃ last ∈ state.core.sites,
      first.occurrence.identity = edge.1 ∧ last.occurrence.identity = edge.2 ∧
      ∀ m, Models state m → CentersSame m first last

theorem origins (path : B4Target.Steps (Step registry root) (initial ctx root) state) : Origins state := by
  induction path with
  | refl => intro edge member; cases member
  | @tail before after path action ih =>
    have growth := GeneralNominalVersionedMixedGrowth234.step action
    have old edge (member : edge ∈ before.core.erased.current.aliases) :
        ∃ first ∈ after.core.sites, ∃ last ∈ after.core.sites,
          first.occurrence.identity = edge.1 ∧ last.occurrence.identity = edge.2 ∧
          ∀ m, Models after m → CentersSame m first last := by
      obtain ⟨a,ha,b,hb,atA,atB,equal⟩ := ih edge member
      exact ⟨a,growth.legacy.sites ha,b,growth.legacy.sites hb,atA,atB,fun m valid =>
        equal m (GeneralNominalVersionedMixedKernel234.step_models action valid)⟩
    obtain ⟨focus,generated,action⟩ := action
    cases action with
    | administrative action => cases action <;> exact old
    | refresh | install => exact old
    | merge first last one two same _ =>
      intro edge member
      rcases List.mem_cons.mp member with rfl|prior
      · exact ⟨first,one,last,two,rfl,rfl,fun _ valid =>
          same_inputs (GeneralNominalVersionedAdministrative232.merge_restrict valid) first last same⟩
      · exact old _ prior

theorem source_origins (path : B4TargetV8.Reachable (boundary roles) registry root state) : Origins state := by
  obtain ⟨first,⟨legacy,⟨ctx,labels,source,point,ground,coverage,sameLegacy⟩,same⟩,steps⟩ := path
  subst first
  subst legacy
  exact origins steps

theorem same_alias
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (valid : Models state m)
    {first last : Site roles} (one : first ∈ state.core.sites) (two : last ∈ state.core.sites)
    (related : Alias state.core.erased.current first.occurrence.identity last.occurrence.identity) :
    CentersSame m first last := by
  have traverse : ∀ {x y : Nat}, Alias state.core.erased.current x y →
      ∀ a b : Site roles, a ∈ state.core.sites → b ∈ state.core.sites →
        a.occurrence.identity = x → b.occurrence.identity = y → CentersSame m a b := by
    intro x y alias
    induction alias with
    | refl =>
      intro a b ha hb x y
      exact GeneralVersionedIdentityCenters312.same_identity checked path valid a b ha hb (x.trans y.symm)
    | edge found =>
      intro a b ha hb x y
      obtain ⟨src,srcSeen,dst,dstSeen,atSrc,atDst,same⟩ := source_origins path _ found
      exact centers_trans
        (GeneralVersionedIdentityCenters312.same_identity checked path valid a src ha srcSeen (x.trans atSrc.symm))
        (centers_trans (same m valid)
          (GeneralVersionedIdentityCenters312.same_identity checked path valid dst b dstSeen hb (atDst.trans y.symm)))
    | symm _ ih =>
      intro a b ha hb x y
      exact centers_symm (ih b a hb ha y x)
    | @trans x y z left right ihL ihR =>
      intro a b ha hb atA atB
      have exists_center : ∀ {i j : Nat}, Alias state.core.erased.current i j →
          ((∃ s ∈ state.core.sites, s.occurrence.identity = i) ↔
          (∃ s ∈ state.core.sites, s.occurrence.identity = j)) := by
        intro i j relation
        induction relation with
        | refl => exact Iff.rfl
        | edge edge =>
          obtain ⟨src,ha,dst,hb,atA,atB,_⟩ := source_origins path _ edge
          exact ⟨fun _ => ⟨dst,hb,atB⟩,fun _ => ⟨src,ha,atA⟩⟩
        | symm _ ih => exact ih.symm
        | trans _ _ one two => exact one.trans two
      have middle := (exists_center left).mp ⟨a,ha,atA⟩
      obtain ⟨center,found,atCenter⟩ := middle
      exact centers_trans (ihL a center ha found atA atCenter) (ihR center b found hb atCenter atB)
  exact traverse related first last one two rfl rfl

end Yulang.GeneralVersionedAliasCenters312
