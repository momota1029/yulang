import Yulang.GeneralRebaseSingleQueryObstruction284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseWatchGuardQueries284
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalAssignmentCongruence238 (Same subtype_iff)
open GeneralRebaseActualWatch284 (Cache interpret preserve_coord preserve_rows preserve_models)
open GeneralRebaseSliceJournal283 (journalReads)
open GeneralRebaseCompiledQuery282 (Denoted compare all₂_equiv)
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalDemandMerging (SameOrigin Related)
open Core.PresenceGeneration (CompTerm)
open CommonNominalFullCarrier (Equivalent)

variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles}
  {state : State roles} {watch : List Nat} {defs : List (GeneralPresenceDefinitionRewrite244.Entry Nat)}

def Agree (watch : List Nat) (a b : Assignment) : Prop :=
  (∀ n ∈ watch, a n = b n) ∧ ∀ n, (a n).2 = (b n).2
def Stable (watch : List Nat) (observe : Assignment → Prop) : Prop :=
  ∀ a b, Agree watch a b → (observe a ↔ observe b)
def Cached (state : State roles) (defs : List (GeneralPresenceDefinitionRewrite244.Entry Nat)) (m : Assignment) : Prop :=
  ∃ base, Models state (interpret defs base) ∧ m = interpret defs base

theorem exact_compare (cached : Cache state watch defs) (seen : Reachable r root state)
    (reads : journalReads state ⊆ watch) (p : Assignment → Prop)
    (raw_congr : ∀ a b, Same a b → (p a ↔ p b))
    (known : Stable watch p) :
    (∀ a, Models state a → p a) ↔ ∀ b, Cached state defs b → p b := by
  have record := GeneralNominalVersionedMixedSeedLedger237.reachable seen
  have empty := GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty seen
  have shared (base : Assignment) :
      Models state (interpret defs base) ↔ GeneralRebaseProspective282.Compiled state base :=
    (preserve_models cached record empty reads base).trans (GeneralRebaseProspective282.decoded empty base).symm
  have pred (base : Assignment) : p (interpret defs base) ↔ p (GeneralRebaseHistoryOrder282.decode state base) :=
    known _ _ ⟨preserve_coord cached record base,preserve_rows state defs base⟩
  refine (compare seen raw_congr).trans ⟨?_,?_⟩
  · rintro all a ⟨base,model,rfl⟩
    exact (pred base).mpr (all _ ⟨base,(shared base).mp model,rfl⟩)
  · rintro all a ⟨base,model,rfl⟩
    exact (pred base).mp (all _ ⟨base,(shared base).mpr model,rfl⟩)

theorem equality (cached : Cache state watch defs) (seen : Reachable r root state)
    (reads : journalReads state ⊆ watch) (x y : Nat) (visibleX : x ∈ watch) (visibleY : y ∈ watch) :
    GeneralNominalVersionedMixedKernel234.Equal state x y ↔
    ∀ model, Cached state defs model → Equivalent (model x).1 (model y).1 := by
  apply exact_compare cached seen reads
  · intro a b same
    exact and_congr (subtype_iff (same x).1 (same y).1) (subtype_iff (same y).1 (same x).1)
  · intro a b same
    change Equivalent (a x).1 (a y).1 ↔ Equivalent (b x).1 (b y).1
    rw [same.1 x visibleX,same.1 y visibleY]

def originReads (origin : Origin) :=
  GeneralNominalOriginSupport249.support (GeneralNominalRebaseOriginView243.compile CompTerm.var origin)

theorem shared_stable (first last : Origin) (coverage : originReads first ++ originReads last ⊆ watch) :
    Stable watch (fun m => GeneralNominalOriginTerms.Same m first last) := by
  intro a b agrees
  refine (GeneralNominalRebaseOriginView243.same_exact CompTerm.var a first last).symm.trans
    ((GeneralNominalOriginSupport249.same_iff _ _ a b agrees.2
      (fun n used => congrArg Prod.fst (agrees.1 n (coverage used)))).trans
      (GeneralNominalRebaseOriginView243.same_exact CompTerm.var b first last))

theorem shared (cached : Cache state watch defs) (seen : Reachable r root state)
    (reads : journalReads state ⊆ watch) (first last : Origin)
    (visible : originReads first ++ originReads last ⊆ watch) :
    SameOrigin (Models state) first last ↔ SameOrigin (Cached state defs) first last :=
  exact_compare cached seen reads _ (fun _ _ same => GeneralNominalOriginCongruence238.shared_iff same first last)
    (shared_stable first last visible)

def siteReads (site : Site roles) :=
  site.observed.inputs.flatMap fun item => item.toList.flatMap originReads

theorem site_covers (site : Site roles) (o : Origin) (item : some o ∈ site.observed.inputs) :
    originReads o ⊆ siteReads site := by
  intro n seen
  exact List.mem_flatMap.mpr ⟨some o,item,List.mem_flatMap.mpr ⟨o,List.mem_singleton_self _,seen⟩⟩

theorem same_inputs (cached : Cache state watch defs) (seen : Reachable r root state)
    (reads : journalReads state ⊆ watch) (first last : Site roles)
    (visible : siteReads first ++ siteReads last ⊆ watch) :
    SameInputs (Models state) first last ↔ SameInputs (Cached state defs) first last := by
  unfold SameInputs GeneralNominalDemandMerging.SameInputs
  apply and_congr Iff.rfl
  have forPairs {xs ys : List (Option Origin)}
      (coverFirst : xs ⊆ first.observed.inputs) (coverLast : ys ⊆ last.observed.inputs) :
      GeneralNominalDemandMerging.All₂ (Related (Models state)) xs ys ↔
      GeneralNominalDemandMerging.All₂ (Related (Cached state defs)) xs ys := by
    have convert {α β : Type} {A B : α → β → Prop} {xs : List α} {ys : List β}
        (switch : ∀ a ∈ xs, ∀ b ∈ ys, A a b ↔ B a b) :
        GeneralNominalDemandMerging.All₂ A xs ys ↔ GeneralNominalDemandMerging.All₂ B xs ys := by
      constructor <;> intro held
      · induction held with
        | nil => exact .nil
        | cons h hs ih =>
          exact .cons ((switch _ List.mem_cons_self _ List.mem_cons_self).mp h)
            (ih (fun a ax b bx => switch a (List.mem_cons_of_mem _ ax) b (List.mem_cons_of_mem _ bx)))
      · induction held with
        | nil => exact .nil
        | cons h hs ih =>
          exact .cons ((switch _ List.mem_cons_self _ List.mem_cons_self).mpr h)
            (ih (fun a ax b bx => switch a (List.mem_cons_of_mem _ ax) b (List.mem_cons_of_mem _ bx)))
    apply convert
    intro a listed b present
    unfold Related
    apply exists_congr; intro x
    apply exists_congr; intro y
    apply and_congr_right; intro ax
    apply and_congr_right; intro byy
    apply shared cached seen reads
    intro n used
    rcases List.mem_append.mp used with hx|hy
    · exact visible (List.mem_append_left _ (site_covers first x (ax ▸ coverFirst listed) hx))
    · exact visible (List.mem_append_right _ (site_covers last y (byy ▸ coverLast present) hy))
  exact forPairs (fun {_} h => h) (fun {_} h => h)

end Yulang.GeneralRebaseWatchGuardQueries284
