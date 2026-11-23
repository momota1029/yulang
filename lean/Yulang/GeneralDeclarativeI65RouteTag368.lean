import Yulang.GeneralDeclarativeI65Selection367

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open CommonRecursiveNominalIntervals (Endpoint)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open CommonDeclaredNominalInspection (Parameter)

/-- Original declaration tag only; this is not a semantic projection
of ordinary equations, and does not select a physical source slot. -/
def originalTag (source : Origin) : Option Nat :=
  match source.endpoint with
  | .nominal name _ => some name
  | .ordinary _ => none

def routedTag (s : State) (logical name : Nat) : Bool :=
  s.origins.any fun source => routeMember s logical source && originalTag source == some name

theorem routed_tag_exact {s : State} {logical name : Nat} :
    routedTag s logical name = true ↔
      ∃ source ∈ s.origins, OriginRoute s source logical ∧ originalTag source = some name := by
  simp only [routedTag,List.any_eq_true,Bool.and_eq_true,actual_route_iff,beq_iff_eq]

/-- A witness of one actual incompatible tag and absence of *any*
exact authored route for the required tag. An empty route set alone
cannot yield this result. A conflicting but also matching route is
retained, not silently overwritten. -/
structure OwnTagClash (s : State) (logical wanted : Nat) where
  seen : Nat
  recorded : routedTag s logical seen = true
  mismatch : seen ≠ wanted
  noWanted : routedTag s logical wanted = false

theorem window_preserves_required_route {s : State} {arg : Capture} {pat : Pattern}
    (w : ModeWindow s arg pat) : routedTag s arg.lower w.name = true := by
  apply routed_tag_exact.mpr
  refine ⟨w.lower,w.lowerAuthored,w.lo,?_⟩
  rw [originalTag,w.firstHead]

structure DifferentAuthoredTag (s : State) (q : Request) (row : Declaration) where
  position : Nat
  arg : Capture
  exactInput : q.demand.arguments[position]? = some arg
  name : Nat
  arguments : List Pattern
  exactHead : row.head[position]? = some (.app name arguments)
  authored : Use s.current.environment name arguments.length
  parameters : List Parameter
  declaredMode : authored.mode = .declared parameters
  incompatible : OwnTagClash s arg.lower name

/-- Excludes an independently authored matching witness without any
fitting model or quantification over hypothetical models. Does not
return a whole language verdict or rule out a K2 prefix inspection. -/
theorem distinct_route_excludes_match {s : State} {q : Request} {row : Declaration}
    (obs : DifferentAuthoredTag s q row) (w : SourceHead s q row) : False := by
  cases w with
  | ordered cap scanned =>
    have same := ordered_head_at scanned obs.exactInput obs.exactHead
    cases same with
    | ordinary h =>
      have missing := declared_application_not_ordinary (s := s) (ps := obs.arguments)
        (obs.declaredMode ▸ obs.authored.sourced)
      obtain ⟨_,e,translated,_⟩ := h
      rw [missing] at translated
      cases translated
    | declared read _ =>
      have expected : .app obs.name (normalizeArgs obs.arguments) = Pattern.app read.name read.arguments := by
        simpa only [normalize] using read.syntaxHead
      have tagEq := (Pattern.app.inj expected).1
      have present := window_preserves_required_route read
      rw [←tagEq,obs.incompatible.noWanted] at present
      cases present
  | joined h =>
    have fromHead := obs.exactHead
    rw [h.head] at fromHead
    cases pos : obs.position with
    | zero =>
      have exactPattern : h.written = .app obs.name obs.arguments := by simpa [pos] using fromHead
      have tag := h.normalized
      rw [exactPattern,normalize] at tag
      cases tag
    | succ n => simp [pos] at fromHead

/-- The exact model-free coherence required of the physical slot
ledger. Distinct physical sites remain independent even if they
route to the same requested logical name. -/
def SlotCoherent (rows : List Origin) : Prop :=
  ∀ a ∈ rows, ∀ b ∈ rows, a.slot = b.slot → a.endpoint = b.endpoint

def readOriginalSlot (rows : List Origin) (slot : Nat) : Option (Endpoint Nat) :=
  (rows.find? fun row => row.slot == slot).map Origin.endpoint

theorem original_slot_is_exact {rows : List Origin} (coherent : SlotCoherent rows)
    {row : Origin} (present : row ∈ rows) :
    readOriginalSlot rows row.slot = some row.endpoint := by
  induction rows with
  | nil => cases present
  | cons head tail ih =>
    by_cases same : head.slot = row.slot
    · have exactEndpoint := coherent head List.mem_cons_self row present same
      simp [readOriginalSlot,same,exactEndpoint]
    · have kept : row ∈ tail := (List.mem_cons.mp present).resolve_left
        (fun eq => same (congrArg Origin.slot eq.symm))
      have keepCoherence : SlotCoherent tail := fun a ma b mb hs =>
        coherent a (List.mem_cons_of_mem _ ma) b (List.mem_cons_of_mem _ mb) hs
      simpa [readOriginalSlot,same] using ih keepCoherence kept

theorem native_interpretation_exact_coherence (rows : List Origin) :
    (∃ f : Nat → Option (Endpoint Nat), ∀ row ∈ rows, f row.slot = some row.endpoint) ↔
      SlotCoherent rows := by
  constructor
  · rintro ⟨f,exactSlot⟩ a aIn b bIn h
    have lhs := exactSlot a aIn
    have rhs := exactSlot b bIn
    rw [h] at lhs
    exact Option.some.inj (lhs.symm.trans rhs)
  · intro coherent
    exact ⟨readOriginalSlot rows,fun _ h => original_slot_is_exact coherent h⟩

theorem fit_exact_on_native_table (s : State)
    (m : GeneralNominalCommonBridge.Assignment)
    (v : GeneralDeclarativeWitnessDeclaredState357.Views) :
    (∃ native, Fits s ⟨m,v,native⟩) ↔
      GeneralDeclarativeWitnessDeclaredState357.ModelsCurrent s.current m v ∧ SlotCoherent s.origins := by
  constructor
  · rintro ⟨f,sem,proof⟩
    exact ⟨sem,(native_interpretation_exact_coherence s.origins).mp ⟨f,proof⟩⟩
  · rintro ⟨sem,coherent⟩
    obtain ⟨f,proof⟩ := (native_interpretation_exact_coherence s.origins).mpr coherent
    exact ⟨f,sem,proof⟩

/-- Route authorization is not derivable by asking whether a model
fits the ordinary and native ledgers; the route table is an
independent source fact. -/
theorem fits_does_not_read_routes (s : State) (differentTable : List Alias) (m : Model) :
    Fits { s with routes := differentTable } m ↔ Fits s m :=
  Iff.rfl

end Yulang.GeneralDeclarativeI65
