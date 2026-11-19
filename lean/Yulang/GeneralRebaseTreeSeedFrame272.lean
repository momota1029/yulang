import Yulang.GeneralRebaseUniformTree272

namespace Yulang.GeneralRebaseTreeSeedFrame272
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedCycles232 (Equal Head)
open GeneralNominalRecursiveInspection (Test)
open GeneralNominalOriginTerms (arity project)
open GeneralNominalReadbackFunctionality (TestCanonical)
open GeneralRebaseNominalOrigin269 (Raw origin tag)
open GeneralRebaseStructuralOrigin270 (Slots shape)
open GeneralNominalState (Descriptor)
open GeneralRebaseOriginRepresentative270 (tightSlot tightSlot_sound)

structure Frame (state : State roles) where
 test : Test
 children : Fin (arity test) → Option (Slots state)

def Sound (state : State roles) (slot : Slots state) (f : Frame state) : Prop :=
 TestCanonical f.test ∧ Head state (origin state slot) f.test ∧
 ∀ i target, f.children i = some target → Equal state (project (origin state slot) f.test i) (origin state target)

def member (state : State roles) (d : Descriptor (Raw state).base.slots) (i : Fin (arity (tag d))) :
 Option (Slots state) :=
 match d.arguments[i.val]? with
 | some (.type (lo,hi)) => tightSlot state lo hi
 | _ => none

def describe (state : State roles) (slot : Slots state) : Option (Frame state) :=
 match (Raw state).nominals slot with
 | some d => some ⟨tag d,member state d⟩
 | none =>
   match (Raw state).view.heads slot with
   | .scalar b => some ⟨.scalar b,Fin.elim0⟩
   | .structural k children => some ⟨.structural (shape state k),fun i => some (children i)⟩
   | .deferred .unresolved =>
     (GeneralRebaseScalarAtoms271.candidate (Raw state).base slot).map (fun b => ⟨.scalar b,Fin.elim0⟩)
   | .deferred _ => none

theorem nominal_sound (state : State roles) (slot : Slots state) (d : Descriptor (Raw state).base.slots)
 (found : (Raw state).nominals slot = some d) :
 Sound state slot ⟨tag d,member state d⟩ := by
 refine ⟨True.intro,GeneralRebaseNominalOrigin269.head state slot d found,?_⟩
 intro i dst checked
 change member state d i = some dst at checked
 unfold member at checked
 split at checked
 · rename_i lo hi actual
   exact tightSlot_sound state slot d found i.val actual checked
 · contradiction

theorem literal_scalar_sound (state : State roles) (slot : Slots state) (b : Inference.Base)
 (found : GeneralRebaseScalarAtoms271.candidate (Raw state).base slot = some b) :
 Sound state slot ⟨.scalar b,Fin.elim0⟩ := by
 refine ⟨True.intro,?_,fun i => Fin.elim0 i⟩
 intro m ok
 refine ⟨⟨_,.source _⟩,?_⟩
 intro type seen
 cases seen
 exact GeneralNominalCommonBridge.rewrites_sound
   (GeneralRebaseScalarAtoms271.checks (Raw state).base slot b found) m ok.1.1.1


theorem describe_sound (state : State roles) (slot : Slots state) (f : Frame state)
 (found : describe state slot = some f) : Sound state slot f := by
 unfold describe at found
 split at found
 · rename_i d recorded
   cases Option.some.inj found
   exact nominal_sound state slot d recorded
 · split at found
   · rename_i b recorded
     cases Option.some.inj found
     exact ⟨True.intro,GeneralRebaseStructuralOrigin270.scalar_head state slot b recorded,fun i => Fin.elim0 i⟩
   · rename_i k children recorded
     cases Option.some.inj found
     refine ⟨(Raw state).view.canonical k,GeneralRebaseStructuralOrigin270.shape_head state slot k children recorded,?_⟩
     intro i target matched
     cases Option.some.inj matched
     exact GeneralRebaseStructuralOrigin270.projected_equals state slot k children recorded i
   · cases raw : GeneralRebaseScalarAtoms271.candidate (Raw state).base slot with
     | none => simp [raw] at found
     | some b =>
       have eq : (⟨Test.scalar b,Fin.elim0⟩ : Frame state) = f := Option.some.inj (by simpa [raw] using found)
       cases eq
       exact literal_scalar_sound state slot b raw
   · contradiction

end Yulang.GeneralRebaseTreeSeedFrame272
