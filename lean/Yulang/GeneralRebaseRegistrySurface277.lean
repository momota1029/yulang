import Yulang.GeneralRebaseCompiledRetag277

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRegistrySurface277
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates (Context Metadata report)
open GeneralNominalRecursiveInspection (bindings)
open GeneralNominalVersionedCandidates231
open GeneralNominalVersionedAllocation231 (Fresh propagate propagate_models)
open GeneralNominalCommonBridge (Assignment)

structure Surface (a b : Registry) (ctx : Context) (root : Occurrence roles) : Prop where
  constructors : a.constructors = b.constructors
  visible : ∀ d : Declaration, d.role = root.demand.role →
    (d ∈ a.declarations ↔ d ∈ b.declarations)
  fresh : ∀ d : Declaration, d.role = root.demand.role →
    ∀ bs : List (GeneralNominalInspection.Bounds ctx.state),
      (Fresh ctx.state a root.identity (bindings ctx.state (report ctx d bs)) ↔
       Fresh ctx.state b root.identity (bindings ctx.state (report ctx d bs)))

theorem symmetric (s : Surface a b ctx root) : Surface b a ctx root :=
  ⟨s.constructors.symm,fun d role => (s.visible d role).symm,
    fun d role bs => (s.fresh d role bs).symm⟩

theorem metadata (ctors : a.constructors = b.constructors) :
    Metadata a ctx ↔ Metadata b ctx := by
  unfold Metadata GeneralNominalCandidates.Metadata
  rw [ctors]

theorem head_models (a b : Registry) (ctx : Context) (root : Occurrence roles)
    (d : Declaration) (bs : List (GeneralNominalInspection.Bounds ctx.state)) (m : Assignment) :
    HeadModels a ctx root d bs m ↔ HeadModels b ctx root d bs m := by
  unfold HeadModels privateState
  simp only [GeneralNominalState.extend_models,propagate_models]
  rfl

theorem prepared (s : Surface a b ctx root) {d : Declaration} (role : d.role = root.demand.role) :
    Prepared a ctx root d ↔ Prepared b ctx root d := by
 constructor
 · rintro ⟨metaOK,linked,bs,located,checked,done,m,valid⟩
   exact ⟨(metadata s.constructors).mp metaOK,linked,bs,located,(s.fresh d role bs).mp checked,done,
     m,(head_models a b ctx root d bs m).mp valid⟩
 · rintro ⟨metaOK,linked,bs,located,checked,done,m,valid⟩
   exact ⟨(metadata s.constructors).mpr metaOK,linked,bs,located,(s.fresh d role bs).mpr checked,done,
     m,(head_models a b ctx root d bs m).mpr valid⟩

theorem failed (s : Surface a b ctx root) {d : Declaration} (role : d.role = root.demand.role) :
    Failed a ctx root d ↔ Failed b ctx root d := by
 constructor
 · rintro ⟨metaOK,bs,located,checked,blocked,arity,why⟩
   refine ⟨(metadata s.constructors).mp metaOK,bs,located,(s.fresh d role bs).mp checked,blocked,arity,?_⟩
   exact why.elim Or.inl (fun none => Or.inr (by rintro ⟨m,valid⟩; exact none ⟨m,(head_models a b ctx root d bs m).mpr valid⟩))
 · rintro ⟨metaOK,bs,located,checked,blocked,arity,why⟩
   refine ⟨(metadata s.constructors).mpr metaOK,bs,located,(s.fresh d role bs).mpr checked,blocked,arity,?_⟩
   exact why.elim Or.inl (fun none => Or.inr (by rintro ⟨m,valid⟩; exact none ⟨m,(head_models a b ctx root d bs m).mp valid⟩))

theorem survivor_forward (s : Surface a b ctx root)
    (first : Survivor a ctx root key childrenList) : Survivor b ctx root key childrenList := by
  obtain ⟨known,d,visible,check,identity,role,bs,located,ready,kids⟩ := first
  refine ⟨known,d,(s.visible d role).mp visible,s.constructors ▸ check,identity,role,bs,located,
    (prepared s role).mp ready,?_⟩
  exact kids

theorem survivor (s : Surface a b ctx root) :
    Survivor a ctx root key childrenList ↔ Survivor b ctx root key childrenList :=
  ⟨survivor_forward s,survivor_forward (symmetric s)⟩

theorem unique (s : Surface a b ctx root) :
    Unique a ctx root key childrenList ↔ Unique b ctx root key childrenList := by
 constructor
 · exact fun h => ⟨(survivor s).mp h.1,fun _ _ other => h.2 _ _ ((survivor s).mpr other)⟩
 · exact fun h => ⟨(survivor s).mpr h.1,fun _ _ other => h.2 _ _ ((survivor s).mp other)⟩

theorem inspectionPending (s : Surface a b ctx root) :
    InspectionPending a ctx root ↔ InspectionPending b ctx root := by
 constructor
 · rintro ⟨known,d,visible,role,noFail,noReady⟩
   exact ⟨known,d,(s.visible d role).mp visible,role,
     fun h => noFail ((failed s role).mpr h),fun h => noReady ((prepared s role).mpr h)⟩
 · rintro ⟨known,d,visible,role,noFail,noReady⟩
   exact ⟨known,d,(s.visible d role).mpr visible,role,
     fun h => noFail ((failed s role).mp h),fun h => noReady ((prepared s role).mp h)⟩

end Yulang.GeneralRebaseRegistrySurface277
