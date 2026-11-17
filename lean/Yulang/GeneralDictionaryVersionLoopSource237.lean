import Yulang.GeneralDictionaryGroundCopy218Source
import Yulang.GeneralNominalVersionedMixedSourceBoundary234
set_option backward.isDefEq.respectTransparency false
/-! Investigation fixture only. No infinite trace or target refutation is
asserted here. Ground Pair(Foo(Int),Foo(Int)) with a repeated-capture terminal
head will test reobservation retargeting. -/
namespace Yulang.GeneralDictionaryVersionLoopSource237
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralDeclarationExamples (constructors bareRole)
open Core.PresenceGeneration (TyTerm)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
abbrev roles : Roles.RoleDecls := fun _ => bareRole
abbrev declaration : Declaration := ⟨0,0,[.app 5 [.var 0,.var 0]],[],[],[]⟩
abbrev sourceRegistry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev registry := GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry

theorem declaration_checked : DeclarationChecked constructors roles declaration := by
 constructor
 · simp [Declaration.Signature]
 · simp [Declaration.Identified,Declaration.outputNames]
 · simp [Declaration.Produced]
 · simp [Declaration.OutputOnly,Declaration.outputNames]
 · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
 · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
 · intro clause member; cases member
 · intro clause member; cases member
 · intro clause member; cases member
 · intro clause member; cases member

theorem source_checked : Checked sourceRegistry := by
 refine ⟨by simp,?_⟩
 intro d member
 cases List.mem_singleton.mp member
 exact declaration_checked

theorem checked : Checked registry := GeneralNominalCenteredHeadAllocEncoding.registry_checked source_checked
abbrev equations : List (Fin 4 × TyTerm (Fin 4)) := [(0,.base .int),(1,.base .int)]
abbrev atoms := equations.flatMap fun p => GeneralSourceState.equationAtoms p.1 p.2
abbrev base : GeneralSourceState.State where
 slots := 4
 source := Fin.val
 source_injective := fun _ _ h => Fin.ext h
 rowSource := Fin.val
 ordinary := atoms
 kinds := 0
 shapes := Fin.elim0
 shapes_injective := by intro i; exact Fin.elim0 i
 heads := fun _ => .unresolved
 intervals := []
 heads_sound := by intro _ _ _ _ h; cases h
 intervals_sound := by intro _ _ _ h; cases h
abbrev view : GeneralNormalizedObservation.Snapshot base where
 kinds := 0
 shapes := Fin.elim0
 shapes_injective := by intro i; exact Fin.elim0 i
 canonical := by intro i; exact Fin.elim0 i
 heads := fun _ => .deferred .unresolved
 checked := by intro _ _ h; cases h
abbrev foo : GeneralNominalState.Descriptor 4 := ⟨0,⟨[.type],0⟩,[.type (0,0)],rfl⟩
abbrev pair : GeneralNominalState.Descriptor 4 := ⟨5,⟨[.type,.type],5⟩,[.type (2,2),.type (2,2)],rfl⟩
abbrev snapshot : GeneralNominalState.State where
 base := base
 view := view
 constructors := constructors
 nominals := fun slot => if slot = 2 then some foo else if slot = 3 then some pair else none
 catalogue := by
   intro slot d found
   split at found
   · cases Option.some.inj found; rfl
   · split at found
     · cases Option.some.inj found; rfl
     · cases found
 bodies_opaque := by intro _ _ _; rfl
 seed := 3
abbrev interpretation : GeneralNominalInspection.Interpretation where
 primitives := fun name => if name = 2 then some (.scalar .int) else none
 invariantNominal := fun name => name == 0 || name == 5
 disjoint := by intro name yes; simp_all; omega
abbrev context : GeneralNominalCandidates.Context := ⟨snapshot,interpretation⟩
abbrev root : Occurrence roles := ⟨0,⟨0,fun _ => (3,3),[],by intro _ h; cases h⟩⟩
abbrev initial := GeneralNominalVersionedJournal232.initial context root
abbrev S : Ty := .base .int
abbrev F : Ty := nominal 0 [.inl S]
abbrev P : Ty := nominal 5 [.inl F,.inl F]
def value : Nat → Ty | 0 | 1 => S | 2 => F | 3 => P | _ => F
def model : Assignment := fun source => (value source,Common.rowEmpty)

theorem base_models : GeneralNominalCommonBridge.Models base model := by
 refine And.intro ?_ (And.intro (by intro _ _ h; cases h) (by intro _ h; cases h))
 intro atom member
 simp only [atoms,List.flatMap_cons,List.flatMap_nil,List.cons_append,List.nil_append,
   GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl <;> exact subtype_refl _

theorem source_model : GeneralNominalState.Models snapshot model := by
 refine ⟨base_models,?_,by intro _ h; cases h⟩
 intro slot d found
 change (if slot = 2 then some foo else if slot = 3 then some pair else none) = some d at found
 split at found
 · rename_i same; subst slot; cases Option.some.inj found
   exact ⟨[.inl S],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,⟨subtype_refl _,subtype_refl _⟩⟩
 · split at found
   · rename_i same; subst slot; cases Option.some.inj found
     exact ⟨[.inl F,.inl F],.cons ⟨subtype_refl _,subtype_refl _⟩
       (.cons ⟨subtype_refl _,subtype_refl _⟩ .nil),⟨subtype_refl _,subtype_refl _⟩⟩
   · cases found

theorem metadata : GeneralNominalRecursiveCandidates.Metadata sourceRegistry context := by
 refine ⟨rfl,?_⟩
 intro name primitive found
 change (if name = 2 then some (.scalar .int) else none) = some primitive at found
 split at found
 · rename_i same; subst name; cases Option.some.inj found; exact ⟨_,rfl,rfl⟩
 · cases found

theorem source : GeneralNominalSourceFormation.InitialSource sourceRegistry context root where
 roles_agree := rfl
 metadata := metadata
 linked := ⟨by intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ],by intro _ h; cases h⟩
 intervals := fun _ _ _ => subtype_refl _
 below_seed := by intro identity member; simp [GeneralNominalState.sources,List.ofFn_succ] at member; change identity ≤ 3; omega
 unallocated := rfl

theorem initial_model : GeneralNominalVersionedJournal232.Models initial model := by
 apply (GeneralNominalVersionedJournal232.initial_models context root model).mpr
 exact ⟨source_model,fun _ => ⟨subtype_refl _,subtype_refl _⟩⟩
end Yulang.GeneralDictionaryVersionLoopSource237
