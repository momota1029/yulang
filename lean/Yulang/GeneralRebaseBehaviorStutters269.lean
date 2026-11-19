import Yulang.GeneralRebaseBehavior269
import Yulang.FiniteBehaviorCanonical269

namespace Yulang.GeneralRebaseBehaviorStutters269
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceState (Output)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseWeakProgress268 (Lull Weak lull_same)
open GeneralRebaseBehavior269 (sourceBasis code code_label)
open FiniteRankBehavior269 (Code)
open FiniteBehaviorClassifier269 (classify)

theorem weak_prepend (before : Lull registry root owners pool first mid)
 (after : Weak registry root owners pool mid last) : Weak registry root owners pool first last := by
 obtain ⟨next,stutters,move,change⟩ := after
 exact ⟨next,GeneralRebaseWeakTerminal268.append before stutters,move,change⟩

theorem filter_embeds (values : List α) (small big : α → Bool)
 (incl : ∀ v, small v = true → big v = true) :
 (values.filter small).Sublist (values.filter big) := by
 induction values with
 | nil => exact .slnil
 | cons v rest ih =>
   cases keep : small v
   · cases kept : big v
     · simpa only [List.filter_cons,keep,kept,Bool.false_eq_true,↓reduceIte] using ih
     · simpa only [List.filter_cons,keep,kept,Bool.false_eq_true,↓reduceIte] using (List.Sublist.cons v ih)
   · have kept := incl v keep
     simpa only [List.filter_cons,keep,kept,↓reduceIte] using (List.Sublist.cons_cons v ih)

theorem children_decline (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (first last : State roles) (stutters : Lull registry root owners pool first last) :
 (code registry root owners pool last).children.Sublist (code registry root owners pool first).children := by
 classical
 let basis := sourceBasis registry root owners pool
 change (classify basis last).children.Sublist (classify basis first).children
 have ranks : basis.rank last = basis.rank first :=
   congrArg (fun s => s.remaining.length) (lull_same stutters)
 rw [classify.eq_1 basis first,classify.eq_1 basis last,ranks]
 apply filter_embeds
 intro child yes
 obtain ⟨next,ends⟩ := of_decide_eq_true yes
 exact decide_eq_true ⟨⟨next.val,weak_prepend stutters next.property⟩,ends⟩

theorem code_ext (one two : Code Label) (atLabel : one.label = two.label)
 (atChildren : one.children = two.children) : one = two := by
 cases one
 cases two
 cases atLabel
 cases atChildren
 rfl

/-- Administrative motion can only lose genuine target behaviors, never
create one that wasn't already weakly reachable before the motion. A change
in the whole code therefore costs one of finitely many possible targets. -/
theorem strict_or_same (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (first last : State roles) (stutters : Lull registry root owners pool first last) :
 code registry root owners pool last = code registry root owners pool first ∨
 (code registry root owners pool last).children.length < (code registry root owners pool first).children.length := by
 have subset := children_decline registry root owners pool first last stutters
 have label : (code registry root owners pool last).label = (code registry root owners pool first).label := by
   rw [code_label,code_label,lull_same stutters]
 by_cases drop : (code registry root owners pool last).children.length < (code registry root owners pool first).children.length
 · exact Or.inr drop
 · exact Or.inl (code_ext _ _ label (subset.eq_of_length_le (by omega)))

theorem eventual (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (chain : Nat → State roles) (stutters : ∀ n, Lull registry root owners pool (chain n) (chain (n+1))) :
 ∃ N, ∀ n ≥ N, code registry root owners pool (chain n) = code registry root owners pool (chain N) :=
 GeneralRebaseEventualProjection265.stabilizes (fun n => code registry root owners pool (chain n))
   (fun c => c.children.length) (fun n => strict_or_same registry root owners pool _ _ (stutters n))

theorem exact_bisim (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (first last : State roles) :
 code registry root owners pool first = code registry root owners pool last ↔
 ∃ relation : State roles → State roles → Prop,
 FiniteBehaviorCanonical269.Bisimulation (sourceBasis registry root owners pool) relation ∧ relation first last :=
 FiniteBehaviorCanonical269.characterizes (sourceBasis registry root owners pool)
   (fun _ _ h => congrArg List.length h) first last

end Yulang.GeneralRebaseBehaviorStutters269
