import Yulang.GeneralRebaseConflictRouting268

namespace Yulang.GeneralRebaseConflictModel268
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded)
open GeneralRebasePartialBool268 (Reflect Answer both neg)
open GeneralRebasePartialFinite268 (transfer)
open GeneralRebaseDiagnosticData268 (Inputs Valid SurvivorSound)
open GeneralRebaseConflictRouting268 (uniqueKey uniqueKey_sound safe safe_sound atKey atKey_sound)
open GeneralRebaseCandidateK2Source268 (focusPlans)
open GeneralRebaseVersionedK2Probe268 (framed)
open GeneralNominalSaturationState (Generated)
open GeneralNominalVersionedDiagnostic232 (ChosenHead ChosenEffects HeadEquations Feasible AtKey)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCenteredHeadMatEffects (Ready)

def HeadFit (state : State roles) (focus : Occurrence roles) (plan : Plan roles) : Prop :=
 ∃ model, Models state model ∧ Ready state.core focus plan ∧ HeadEquations plan model

def EffectsFit (state : State roles) (focus : Occurrence roles) (plan : Plan roles) : Prop :=
 ∃ model, Models state model ∧ Ready state.core focus plan ∧ HeadEquations plan model ∧
   GeneralNominalVersionedEffects231.ClassEffects state.core focus plan model

def SharedFit (state : State roles) (plan : Plan roles) : Prop :=
 ∃ model, Models state model ∧ GeneralDictionaryHeadSharing220.Holds plan model

def HasFrame (registry : Registry) (state : State roles) (focus : Occurrence roles) (key : Nat) : Prop :=
 ∃ plan, Frame (Encoded registry) state.core focus key plan

def HasFit (registry : Registry) (state : State roles) (focus : Occurrence roles) (key : Nat)
 (fit : Plan roles → Prop) : Prop :=
 ∃ plan, Frame (Encoded registry) state.core focus key plan ∧ fit plan

def UniqueAt (registry : Registry) (state : State roles) (focus : Occurrence roles) (key : Nat) : Prop :=
 ∃ children, B4TargetV8.Unique (Boundary roles) registry state focus key children

theorem output_formula (registry : Registry) (state : State roles) (focus : Occurrence roles) (key : Nat) :
 ((Boundary roles).OutputConflict registry state focus key) ↔
 UniqueAt registry state focus key ∧ HasFit registry state focus key (HeadFit state focus) ∧
 ¬ HasFit registry state focus key (EffectsFit state focus) := by
 constructor
 · rintro ⟨⟨model,valid,chosen,plan,frame,ready,head⟩,no⟩
   refine ⟨chosen,⟨plan,frame,model,valid,ready,head⟩,?_⟩
   rintro ⟨alternative,altFrame,fitted,altModel,altReady,altHead,altEffects⟩
   exact no ⟨fitted,altModel,chosen,alternative,altFrame,altReady,altHead,altEffects⟩
 · rintro ⟨chosen,⟨plan,frame,model,valid,ready,head⟩,no⟩
   refine ⟨⟨model,valid,chosen,plan,frame,ready,head⟩,?_⟩
   rintro ⟨alternative,altModel,_,p,pFrame,pReady,pHead,pEffects⟩
   exact no ⟨p,pFrame,alternative,altModel,pReady,pHead,pEffects⟩

theorem feasible_formula (registry : Registry) (state : State roles) (focus : Occurrence roles) (key : Nat) :
 Feasible (Encoded registry) state focus key ↔ HasFit registry state focus key (SharedFit state) :=
 ⟨fun ⟨model,valid,plan,frame,held⟩ => ⟨plan,frame,model,valid,held⟩,
  fun ⟨plan,frame,model,valid,held⟩ => ⟨model,valid,plan,frame,held⟩⟩

def output (x : Inputs (Occurrence roles)) (entries : List (Plan roles))
 (frame head effects : Plan roles → Answer) (key : Nat) : Answer :=
 both (uniqueKey x key) (both (atKey entries frame head key) (neg (atKey entries frame effects key)))

theorem output_sound (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (generated : Generated state.core.erased.current root focus)
 (x : Inputs (Occurrence roles)) (survivors : SurvivorSound (Boundary roles) registry state focus x.survivors)
 (frame head effects : Plan roles → Answer)
 (frameSound : ∀ p ∈ focusPlans registry state root focus checked, Reflect (framed registry state focus p) (frame p))
 (headSound : ∀ p ∈ focusPlans registry state root focus checked, Reflect (HeadFit state focus p) (head p))
 (effectsSound : ∀ p ∈ focusPlans registry state root focus checked, Reflect (EffectsFit state focus p) (effects p))
 (key : Nat) :
 Reflect ((Boundary roles).OutputConflict registry state focus key)
   (output x (focusPlans registry state root focus checked) frame head effects key) :=
 transfer (output_formula registry state focus key).symm
  (GeneralRebasePartialBool268.both_sound (uniqueKey_sound (Boundary roles) registry state focus x survivors key)
    (GeneralRebasePartialBool268.both_sound (atKey_sound registry state root focus checked generated frame head _
      frameSound headSound key) (GeneralRebasePartialBool268.neg_sound
        (atKey_sound registry state root focus checked generated frame effects _ frameSound effectsSound key))))

def sharingAt (entries : List (Plan roles)) (frame shared : Plan roles → Answer) (models : Answer) (key : Nat) :
 Answer := both models (both (atKey entries frame (fun _ => some true) key) (neg (atKey entries frame shared key)))

theorem sharingAt_sound (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (generated : Generated state.core.erased.current root focus)
 (frame shared : Plan roles → Answer) (models : Answer)
 (frameSound : ∀ p ∈ focusPlans registry state root focus checked, Reflect (framed registry state focus p) (frame p))
 (sharedSound : ∀ p ∈ focusPlans registry state root focus checked, Reflect (SharedFit state p) (shared p))
 (modelsSound : Reflect (∃ model, Models state model) models) (key : Nat) :
 Reflect (AtKey (Encoded registry) state focus key)
   (sharingAt (focusPlans registry state root focus checked) frame shared models key) := by
 have hasFrame := transfer (p := HasFit registry state focus key (fun _ => True))
   (q := HasFrame registry state focus key) (by
     constructor
     · rintro ⟨p,f,_⟩; exact ⟨p,f⟩
     · rintro ⟨p,f⟩; exact ⟨p,f,True.intro⟩)
   (atKey_sound registry state root focus checked generated frame (fun _ => some true) _ frameSound
     (fun _ _ => True.intro) key)
 exact GeneralRebasePartialBool268.both_sound modelsSound (GeneralRebasePartialBool268.both_sound hasFrame
   (GeneralRebasePartialBool268.neg_sound (transfer (feasible_formula registry state focus key).symm
     (atKey_sound registry state root focus checked generated frame shared _ frameSound sharedSound key))))

def uniqueSharing (x : Inputs Demand) (query : Nat → Answer) : Answer :=
 match x.survivors with
 | .unique item => query item.1
 | .none | .ambiguous .. => some false
 | .deferred => none

theorem uniqueSharing_sound (b : B4TargetV8.SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand)
 (x : Inputs v.Demand) (valid : SurvivorSound b r s d x.survivors)
 (query : Nat → Answer) (P : Nat → Prop) (witness : ∀ key, Reflect (P key) (query key)) :
 Reflect (∃ key children, B4TargetV8.Unique b r s d key children ∧ P key) (uniqueSharing x query) := by
 unfold uniqueSharing
 cases view : x.survivors with
 | deferred => trivial
 | none =>
   rw [view] at valid
   rintro ⟨key,kids,one,_⟩
   exact valid key kids one.1
 | ambiguous first last =>
   rcases first with ⟨a,one⟩
   rcases last with ⟨z,two⟩
   rw [view] at valid
   rintro ⟨_,_,unique,_⟩
   exact valid.1 ((unique.2 a one valid.2.1).1.trans (unique.2 z two valid.2.2).1.symm)
 | unique item =>
   rcases item with ⟨key,kids⟩
   rw [view] at valid
   apply transfer (p := P key)
   · constructor
     · intro property
       exact ⟨key,kids,valid,property⟩
     · rintro ⟨other,children,found,property⟩
       exact (valid.2 other children found.1).1 ▸ property
   · exact witness key

def sharing (x : Inputs (Occurrence roles)) (entries : List (Plan roles))
 (frame shared : Plan roles → Answer) (models : Answer) : Answer :=
 both (safe x) (uniqueSharing x (sharingAt entries frame shared models))

theorem sharing_sound (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (generated : Generated state.core.erased.current root focus)
 (x : Inputs (Occurrence roles)) (valid : Valid (Boundary roles) registry state focus x)
 (frame shared : Plan roles → Answer) (models : Answer)
 (frameSound : ∀ p ∈ focusPlans registry state root focus checked, Reflect (framed registry state focus p) (frame p))
 (sharedSound : ∀ p ∈ focusPlans registry state root focus checked, Reflect (SharedFit state p) (shared p))
 (modelsSound : Reflect (∃ model, Models state model) models) :
 Reflect ((Boundary roles).SharingConflict registry state focus)
   (sharing x (focusPlans registry state root focus checked) frame shared models) := by
 apply transfer (p := B4TargetV8.SafeKnown (Boundary roles) registry state focus ∧
     ∃ key children, B4TargetV8.Unique (Boundary roles) registry state focus key children ∧
       AtKey (Encoded registry) state focus key)
 · constructor
   · rintro ⟨clear,key,children,unique,bad⟩
     exact ⟨key,children,unique,clear,bad⟩
   · rintro ⟨key,children,unique,clear,bad⟩
     exact ⟨clear,key,children,unique,bad⟩
 · exact GeneralRebasePartialBool268.both_sound (safe_sound (Boundary roles) registry state focus x valid)
     (uniqueSharing_sound (Boundary roles) registry state focus x valid.survivors _ _
      (sharingAt_sound registry state root focus checked generated frame shared models frameSound sharedSound modelsSound))

end Yulang.GeneralRebaseConflictModel268
