import Yulang.GeneralSourceMetadataDefaultDomain291

/-! Exact output-body domain on actual alias-class requests. Unlike a
whole source check, this does not reject unrelated unrequested defaults. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralSourceMetadataLive291
open GeneralDeclarationPatterns (Constructors)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredSteps (State)
open GeneralNominalCenters (Plan)
open GeneralSourceDictionaries (Occurrence)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralObservedMetadataBodies290 (compileFrom)
open GeneralObservedMetadataRequestBook290 (requestBook)
open GeneralObservedMetadataTotal290 (total total_iff_ready)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralSourceMetadataUse291 (Use check check_exact)
open GeneralSourceMetadataSyntax291 (patterns terms pattern_exact term_exact)
open GeneralSourceMetadataExprDomain291 (compiler_domain)
open GeneralSourceMetadataDefaultDomain291 (default_domain)
open GeneralObservedMetadataEntry290 (LocalEqual)
open GeneralObservedMetadataLive290 (liveKeys)

def bodyUses : Body → List Use
  | .explicit eqn => patterns eqn.rhs
  | .default _ _ e => terms e

def bodyCheck (c : Constructors) (i : Interpretation) (b : Body) : Bool :=
  check c i (bodyUses b)

theorem some_iff_exists {α : Type} (value : Option α) :
    value.isSome = true ↔ ∃ result, value = some result := by
  cases value <;> simp

theorem body_exact (c : Constructors) (i : Interpretation) (b : Body) :
    bodyCheck c i b = (compileFrom c i b).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [bodyCheck,check_exact,some_iff_exists]
  cases b with
  | explicit e => exact (pattern_exact c i e.rhs).trans (compiler_domain c i e.rhs).symm
  | default r name t => exact (term_exact c i t).trans (default_domain c i t).symm

def liveCheck (s : State roles) (up : Occurrence roles) (p : Plan roles)
    (c : Constructors) (i : Interpretation) : Bool :=
  (requestBook s up p).all fun entry =>
    match entry.2 with
    | none => false
    | some b => bodyCheck c i b

theorem live_compiler_eq (s : State roles) (up : Occurrence roles) (p : Plan roles)
    (c : Constructors) (i : Interpretation) :
    liveCheck s up p c i = total s up p c i := by
  apply GeneralObservedMetadataAgreement290.all_local
  intro entry _
  cases h : entry.2 with
  | none => rfl
  | some b => exact body_exact c i b

theorem live_ready_exact (s : State roles) (up : Occurrence roles) (p : Plan roles)
    (c : Constructors) (i : Interpretation)
    (agreement : LocalEqual (liveKeys s up p) p.packet.registry.constructors p.packet.context.interpretation c i) :
    liveCheck s up p c i = true ↔ Ready s up p := by
  rw [live_compiler_eq,total_iff_ready s up p c i agreement]

theorem original_live_ready_exact (s : State roles) (up : Occurrence roles) (p : Plan roles) :
    liveCheck s up p p.packet.registry.constructors p.packet.context.interpretation = true ↔ Ready s up p :=
  live_ready_exact _ _ _ _ _ (fun _ _ => ⟨rfl,rfl,rfl⟩)

end Yulang.GeneralSourceMetadataLive291
