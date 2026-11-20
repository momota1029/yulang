import Yulang.GeneralSourceMetadataLive291

/-! Lookup absence and an unsupported live body are distinct. Diagnostics
carry the actual request, without introducing a raw resolver failure rule. -/
namespace Yulang.GeneralSourceMetadataLiveDiagnostics291
open GeneralDeclarationPatterns (Constructors)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredSteps (State)
open GeneralNominalCenters (Plan)
open GeneralSourceDictionaries (Occurrence)
open GeneralSourceState (Output)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralObservedMetadataRequestBook290 (requestBook)
open GeneralSourceMetadataSites291 (Site Entry tag)
open GeneralSourceMetadataDiagnostics291 (Failure issues issues_exact)
open GeneralSourceMetadataLive291 (bodyUses bodyCheck liveCheck)
open GeneralSourceMetadataUse291 (check_exact)

def bodySites (decl : Nat) : Body → List Entry
  | .explicit d => tag (.associated decl d.id) (bodyUses (.explicit d))
  | .default r n term => tag (.roleDefault r n) (bodyUses (.default r n term))

theorem body_queries (decl : Nat) (b : Body) :
    (bodySites decl b).map Entry.query = bodyUses b := by
  cases b <;> simp [bodySites]

inductive Detail
  | missingBody
  | unsupported (constructorUses : List Failure)
  deriving DecidableEq, Repr

structure Fault where
  request : Output
  kind : Detail
  deriving DecidableEq

def diagnose (c : Constructors) (i : Interpretation) (decl : Nat) (request : Output × Option Body) :
    Option Fault :=
  match request.2 with
  | none => some ⟨request.1,.missingBody⟩
  | some b =>
    let bad := issues c i (bodySites decl b)
    if bad.isEmpty then none else some ⟨request.1,.unsupported bad⟩

theorem diagnose_exact (c : Constructors) (i : Interpretation) (decl : Nat)
    (out : Output × Option Body) :
    diagnose c i decl out = none ↔
      (match out.2 with | none => false | some b => bodyCheck c i b) = true := by
  unfold diagnose
  cases out.2 with
  | none => simp
  | some b =>
    by_cases clean : issues c i (bodySites decl b) = []
    · have hold := (issues_exact c i (bodySites decl b)).mp clean
      rw [body_queries] at hold
      have valid : bodyCheck c i b = true := (check_exact ..).mpr hold
      simp [clean,valid]
    · have invalid : bodyCheck c i b ≠ true := by
        intro same
        apply clean
        apply (issues_exact ..).mpr
        rw [body_queries]
        exact (check_exact ..).mp same
      simp [List.isEmpty_iff,clean,invalid]

theorem filterMap_nil_iff {α β : Type} (f : α → Option β) (entries : List α) :
    entries.filterMap f = [] ↔ ∀ e ∈ entries, f e = none := by
  induction entries with
  | nil => simp
  | cons e es ih =>
    cases h : f e <;> simp [h,ih]

def faults (s : State roles) (up : Occurrence roles) (plan : Plan roles)
    (c : Constructors) (i : Interpretation) : List Fault :=
  (requestBook s up plan).filterMap (diagnose c i plan.packet.declaration.id)

theorem all_live_exact (s : State roles) (up : Occurrence roles) (plan : Plan roles)
    (c : Constructors) (i : Interpretation) :
    faults s up plan c i = [] ↔ liveCheck s up plan c i = true := by
  unfold faults liveCheck
  simp only [filterMap_nil_iff,diagnose_exact,List.all_eq_true]
  rfl

end Yulang.GeneralSourceMetadataLiveDiagnostics291
