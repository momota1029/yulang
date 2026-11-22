import Yulang.GeneralDeclarativeCompoundSources338
import Yulang.GeneralDeclarativeInlineEndpoint331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCompoundHeads338
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeInlineTrace331 (Read Fields)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeOrderedRecord326 (order exact_order)
open GeneralDeclarativeCompoundEndpoints338 (order_iff)
open GeneralDeclarativeCompoundPattern338 (peel rebuild rebuild_peel)
open GeneralDeclarativeCompoundSources338 (Source Anchors)
open GeneralDeclarativeInlineEndpoint331 (Matches)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralNominalInspection (Interpretation)
open GeneralNominalMaterialization (Mode)
open CommonRoleCanonicalRows (Row normalize_unique residual)
open CommonRoleOutermostResolver (All₂)

theorem peel_tail (p : Pattern) : (peel (peel p).2).1 = [] := by
  cases p with
  | record k x t => exact peel_tail t
  | var | app | variant | join => rfl
termination_by sizeOf p

theorem tail_binder {p : Pattern} (seen : Source s lo hi t) (cut : peel p = (fs,t)) :
    ∃ n, t = .var n := by
  have empty := peel_tail p
  rw [cut] at empty
  cases seen with
  | binder => exact ⟨_,rfl⟩
  | record shape nonempty =>
    rw [shape] at empty
    exact False.elim (nonempty empty)

abbrev Render (c : Constructors) (i : Interpretation) : (Nat × Pattern) → (Nat × Expr) → Prop :=
  fun p q => p.1 = q.1 ∧ translate c i p.2 = some q.2

theorem translate_spine {fs : Row Pattern} {cs : Row Expr} (matched : All₂ (Render c i) fs cs)
    (binder : translate c i t = some e) :
    translate c i (rebuild fs t) = some (withTail cs e) := by
  induction matched with
  | nil => exact binder
  | cons relates _ ih =>
    obtain ⟨tag,printed⟩ := relates
    simp only [rebuild,withTail,translate,printed,ih,Option.pure_def,tag]
    rfl

def Seen (s : State) (c : Constructors) (i : Interpretation)
    (a b : Expr) (p : Pattern) : Prop :=
  ∃ code, translate c i p = some code ∧
    ∀ mode : Mode, (∃ left, Read s mode a code left) ∧ ∃ right, Read s mode b code right

theorem pair_fields {s : State} {c : Constructors} {i : Interpretation}
    {fs : Row Pattern} {lo hi : Row Expr}
    (ll : lo.map Prod.fst = fs.map Prod.fst) (hh : hi.map Prod.fst = fs.map Prod.fst)
    (comes : ∀ f ∈ fs, ∀ l u, (f.1,l) ∈ lo → (f.1,u) ∈ hi → Seen s c i l u f.2) :
    ∃ codes, All₂ (Render c i) fs codes ∧
      ∀ mode, (∃ l, Fields s mode lo codes l) ∧ ∃ h, Fields s mode hi codes h := by
  induction fs generalizing lo hi with
  | nil =>
    have x : lo = [] := List.map_eq_nil_iff.mp ll
    have y : hi = [] := List.map_eq_nil_iff.mp hh
    subst lo; subst hi
    exact ⟨[],.nil,fun _ => ⟨⟨[],.nil⟩,⟨[],.nil⟩⟩⟩
  | cons f fs ih =>
    rcases f with ⟨k,p⟩
    cases lo with
    | nil => simp at ll
    | cons x xs =>
      cases hi with
      | nil => simp at hh
      | cons y ys =>
        rcases x with ⟨ld,l⟩
        rcases y with ⟨hd,u⟩
        simp only [List.map_cons,List.cons.injEq] at ll hh
        obtain ⟨rl,ll⟩ := ll; obtain ⟨rh,hh⟩ := hh
        subst ld; subst hd
        obtain ⟨code,printed,both⟩ := comes (k,p) List.mem_cons_self _ _
          List.mem_cons_self List.mem_cons_self
        obtain ⟨tail,rendered,observed⟩ := ih ll hh (fun f part a b la ub =>
          comes f (List.mem_cons_of_mem _ part) a b (List.mem_cons_of_mem _ la) (List.mem_cons_of_mem _ ub))
        refine ⟨(k,code)::tail,.cons ⟨rfl,printed⟩ rendered,?_⟩
        intro mode
        obtain ⟨⟨lv,lr⟩,⟨hv,hr⟩⟩ := both mode
        obtain ⟨⟨ltf,lt⟩,⟨utf,ut⟩⟩ := observed mode
        exact ⟨⟨lv++ltf,.cons lr lt⟩,⟨hv++utf,.cons hr ut⟩⟩

open CommonRoleCanonicalRows (normalize) in
theorem record_seen {s : State}
    (shape : peel p = (fs,tail)) (nonempty : fs ≠ []) (unique : (fs.map Prod.fst).Nodup)
    (left : Closed s lo lr le) (right : Closed s hi ur ue)
    (lower : ∀ k ∈ fs.map Prod.fst, ∃ a, (k,a) ∈ normalize lr)
    (upper : ∀ k ∈ fs.map Prod.fst, ∃ a, (k,a) ∈ normalize ur)
    (kids : ∀ f ∈ fs, ∀ l u, (f.1,l) ∈ normalize lr → (f.1,u) ∈ normalize ur → Seen s c i l u f.2)
    (remaining : Source s (withTail (residual (fs.map Prod.fst) (normalize lr)) le)
      (withTail (residual (fs.map Prod.fst) (normalize ur)) ue) tail) :
    Seen s c i lo hi p := by
  obtain ⟨n,rfl⟩ := tail_binder remaining shape
  obtain ⟨orderedLo,l⟩ := (order_iff (normalize_unique lr) (fs.map Prod.fst)).mpr lower
  obtain ⟨orderedHi,h⟩ := (order_iff (normalize_unique ur) (fs.map Prod.fst)).mpr upper
  have ll := exact_order (normalize_unique _) l
  have hh := exact_order (normalize_unique _) h
  obtain ⟨codes,typed,reads⟩ := pair_fields ll.1 hh.1 (fun f seen el eh fl fh =>
    kids f seen el eh (((ll.2 _).mp fl).1) (((hh.2 _).mp fh).1))
  have reconstruction : rebuild fs (.var n) = p := by
    have old := rebuild_peel p
    simpa only [shape] using old
  have nonemptyKeys : fs.map Prod.fst ≠ [] := fun same => nonempty (List.map_eq_nil_iff.mp same)
  refine ⟨withTail codes (.variable n),?_,?_⟩
  · rw [← reconstruction]
    exact translate_spine typed rfl
  · intro mode
    obtain ⟨⟨lf,knownLow⟩,⟨hf,knownHigh⟩⟩ := reads mode
    exact ⟨⟨lf++[⟨n,mode,tailExpr lr (fs.map Prod.fst) le⟩],
        .record left unique nonemptyKeys l knownLow .binder .capture⟩,
      ⟨hf++[⟨n,mode,tailExpr ur (fs.map Prod.fst) ue⟩],
        .record right unique nonemptyKeys h knownHigh .binder .capture⟩⟩

/-- The actual source producer and the pre-existing election observer
agree on the positive nested record fragment without testing a center. -/
theorem candidate {s : State} (source : Source s lo hi p) : Seen s c i lo hi p := by
  induction source with
  | binder => exact ⟨_,rfl,fun _ => ⟨⟨_,.capture⟩,⟨_,.capture⟩⟩⟩
  | record shape nonempty unique l h low high _ tail ih _ =>
    exact record_seen shape nonempty unique l h low high ih tail

theorem move_to_anchor {s : State} (link : GeneralDeclarativeCompoundSources338.Anchored s n e)
    (seen : Read s mode e code uses) : ∃ traced, Read s mode (.variable n) code traced := by
  cases code with
  | «variable» binder => exact ⟨_,.capture⟩
  | primitive | nominal | record | variant | join =>
    obtain ⟨owner,alias,stored⟩ := link
    exact ⟨_,.expose (by intro _ impossible; cases impossible) alias stored seen⟩

theorem positive {s : State} {p : Supported s done}
    (read : Source (restriction p) lo hi (normalize pat))
    (whereFrom : Anchors (restriction p) a lo hi) (valid : Bounds s a) :
    Matches (restriction p) c i a pat := by
  obtain ⟨expr,printed,observed⟩ := candidate (c := c) (i := i) read
  obtain ⟨_,low⟩ := (observed .lower).1
  obtain ⟨_,high⟩ := (observed .upper).2
  obtain ⟨l,nowL⟩ := move_to_anchor whereFrom.1 low
  obtain ⟨h,nowH⟩ := move_to_anchor whereFrom.2 high
  exact ⟨valid,expr,l,h,printed,nowL,nowH⟩

end Yulang.GeneralDeclarativeCompoundHeads338
