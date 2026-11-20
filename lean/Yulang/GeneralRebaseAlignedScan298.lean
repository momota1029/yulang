import Yulang.GeneralRebasePackedDepthDecision298

namespace Yulang.GeneralRebaseAlignedScan298
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseHeadProbe267 (Match observation)
open GeneralRebasePartialClassification267 (Verdict classify)
open GeneralRebaseInstallCandidates267 (eligible)
open GeneralRebaseSignedModels297 (Sign)
open GeneralRebaseSymbolicQuestions298 (Body)
open GeneralNominalRebaseJournalView243 (Journal)
open Core.PresenceGeneration (CompTerm)

local instance : DecidableEq (Occurrence roles) := GeneralRebaseOccurrenceEq267.occurrenceEq

structure Entry (roles : Roles.RoleDecls) where
  plan : Plan roles
  head : Option Bool
  reject : Bool
  joint : Bool

def annotate (plans : List (Plan roles)) (head : Plan roles → Option Bool)
    (reject joint : Plan roles → Bool) : List (Entry roles) :=
  plans.map fun p => ⟨p,head p,reject p,joint p⟩

def positive (entries : List (Entry roles)) : List (Match roles) :=
  (entries.filter (fun e => e.head == some true)).map (fun e => observation e.plan)

def unknown (entries : List (Entry roles)) : List (Match roles) :=
  (entries.filter (fun e => e.head.isNone)).map (fun e => observation e.plan)

theorem positive_exact (plans : List (Plan roles)) (head : Plan roles → Option Bool)
    (reject joint : Plan roles → Bool) :
    positive (annotate plans head reject joint) = GeneralRebaseHeadProbe267.positive head plans := by
  induction plans with
  | nil => rfl
  | cons a as ih =>
    by_cases h : head a == some true
    · simp only [positive,annotate,List.map_cons,List.filter_cons,h,↓reduceIte,
        GeneralRebaseHeadProbe267.positive] at ih ⊢
      exact congrArg (observation a :: ·) ih
    · simp only [positive,annotate,List.map_cons,List.filter_cons,Bool.eq_false_iff.mpr h,
        Bool.false_eq_true,↓reduceIte,GeneralRebaseHeadProbe267.positive] at ih ⊢
      exact ih

theorem unknown_exact (plans : List (Plan roles)) (head : Plan roles → Option Bool)
    (reject joint : Plan roles → Bool) :
    unknown (annotate plans head reject joint) =
      (GeneralRebaseHeadProbe267.unresolved head plans).map observation := by
  induction plans with
  | nil => rfl
  | cons a as ih =>
    by_cases h : (head a).isNone
    · simp only [unknown,annotate,List.map_cons,List.filter_cons,h,↓reduceIte,
        GeneralRebaseHeadProbe267.unresolved] at ih ⊢
      exact congrArg (observation a :: ·) ih
    · simp only [unknown,annotate,List.map_cons,List.filter_cons,Bool.eq_false_iff.mpr h,
        Bool.false_eq_true,↓reduceIte,GeneralRebaseHeadProbe267.unresolved] at ih ⊢
      exact ih

def eligibleRow (s : State roles) (target : Match roles) (e : Entry roles) : Bool :=
  eligible s (fun _ => e.head) (fun _ => e.reject) (fun _ => e.joint) target e.plan

def scan (s : State roles) (entries : List (Entry roles)) : List (Plan roles) :=
  match classify (positive entries) (unknown entries) with
  | .unique target => (entries.filter (eligibleRow s target)).map (·.plan)
  | _ => []

theorem filter_exact (s : State roles) (plans : List (Plan roles)) (target : Match roles)
    (head : Plan roles → Option Bool) (reject joint : Plan roles → Bool) :
    ((annotate plans head reject joint).filter (eligibleRow s target)).map (·.plan) =
      plans.filter (eligible s head reject joint target) := by
  induction plans with
  | nil => rfl
  | cons a as ih =>
    have eq : eligibleRow s target (⟨a,head a,reject a,joint a⟩ : Entry roles) =
      eligible s head reject joint target a := rfl
    by_cases h : eligible s head reject joint target a
    · simp only [annotate,List.map_cons,List.filter_cons,eq,h,↓reduceIte] at ih ⊢
      exact congrArg (a :: ·) ih
    · simp only [annotate,List.map_cons,List.filter_cons,eq,Bool.eq_false_iff.mpr h,
        Bool.false_eq_true,↓reduceIte] at ih ⊢
      exact ih

theorem scan_exact (s : State roles) (plans : List (Plan roles)) (head : Plan roles → Option Bool)
    (reject joint : Plan roles → Bool) :
    scan s (annotate plans head reject joint) = GeneralRebaseInstallCandidates267.scan s head reject joint plans := by
  unfold scan GeneralRebaseInstallCandidates267.scan GeneralRebaseSourceClassification267.verdict
  rw [positive_exact,unknown_exact]
  cases classify (GeneralRebaseHeadProbe267.positive head plans)
      ((GeneralRebaseHeadProbe267.unresolved head plans).map observation)
  all_goals first | rfl | exact filter_exact ..

/-- Compile each of the three row questions in place; no semantic-ID or
whole-plan lookup is required even for repeated plans. -/
def symbolic (s : State roles) (plans : List (Plan roles)) (check : Body → Option Bool) :
    List (Entry roles) :=
  annotate plans
    (fun p => check (GeneralRebaseSymbolicQuestions298.compile s CompTerm.var (.head p)))
    (fun p => check (GeneralRebaseSymbolicQuestions298.compile s CompTerm.var (.install p .reject)) == some true)
    (fun p => check (GeneralRebaseSymbolicQuestions298.compile s CompTerm.var (.install p .pass)) == some true)

theorem entry_order (s : State roles) (plans : List (Plan roles)) (check : Body → Option Bool) :
    (symbolic s plans check).map (·.plan) = plans := by
  simp [symbolic,annotate,List.map_map,Function.comp_def]

end Yulang.GeneralRebaseAlignedScan298
