import YulangClosure.FormalPermissionSourceOrigin

/-!
Partial successful-source event refinement, at the frozen candidate_effect.rs
constructor owners. The event constructors below compute the state changes;
none takes Origin or Construction as an assumption. Memo hits/misses use the
actual scoped key. Delegated signatures resolve tails before view lookup, then
allocate a port even on a view hit. The two signature calls run in source order.

A native call's successful allocation/resource checks, identifier/term decoding,
and concrete bound insertion are NOT authenticated here. There is deliberately
no theorem that every accepted native execution has such a history. In
particular this is not the row/bound/evidence/context capture recurrence.
-/
namespace YulangClosure.FormalPermissionConstructorRealization

open FormalPermissionCaptureConstruction
open FormalPermissionSourceOrigin
open FormalPermissionLiveCapture (prependPath atPort shift shifted_tuple_origin)
noncomputable section

/-- Scoped effect lookup; the list records actual fresh effect-row births. -/
inductive EffectMemo (scope name : Nat) : State → Nat → State → List Nat → Prop where
  | hit (s : State) (row : Nat) (found : s.effects (scope, name) = some row) :
      EffectMemo scope name s row s []
  | miss (s : State) (absent : s.effects (scope, name) = none) :
      EffectMemo scope name s s.nextEffect
        {s with nextEffect := s.nextEffect + 1, effects := fun key => if key = (scope, name) then some s.nextEffect else s.effects key}
        [s.nextEffect]

theorem effect_memo_refines {scope name row : Nat} {s t : State} {births : List Nat}
    (event : EffectMemo scope name s row t births) : scopedEffect s scope name = (row, t) := by
  cases event with
  | hit row found => simp [scopedEffect, memo, found]
  | miss absent => simp [scopedEffect, memo, absent]

/-- The view cache is annotation-local and keyed by the original row position.
A hit keeps its payload; no equality with a new requested payload is presumed. -/
inductive ViewEvent (c : Context) (position : Nat) (concrete : List Nat) (tail : Option Nat) :
    State → Nat → State → Prop where
  | hit (s : State) (view : Nat) (found : s.views position = some view) :
      ViewEvent c position concrete tail s view s
  | miss (s : State) (absent : s.views position = none) :
      ViewEvent c position concrete tail s s.nextView
        {s with nextView := s.nextView + 1, views := fun p => if p = position then some s.nextView else s.views p, viewData := fun i => if i = s.nextView then some ⟨c.owner, c.scope, position, concrete, tail⟩ else s.viewData i}

/-- Only explicit annotation rows at positive variance and family=None.
The resulting bound is data; actual candidate_insert_bound is still OPEN. -/
inductive SignatureEvent (c : Context) (position : Nat) (concrete : List Nat) (positive : Bool) :
    Option Nat → State → Nat → SignatureBound → State → List Nat → Prop where
  | closed {s v : State} {view : Nat}
      (cached : ViewEvent c position concrete none s view v) :
      SignatureEvent c position concrete positive none s v.nextEffect
        ⟨v.nextEffect, positive, view, none⟩ {v with nextEffect := v.nextEffect + 1}
        [v.nextEffect]
  | tailed {s t v : State} {name tail view : Nat} {births : List Nat}
      (lookup : EffectMemo c.scope name s tail t births)
      (cached : ViewEvent c position concrete (some tail) t view v) :
      SignatureEvent c position concrete positive (some name) s v.nextEffect
        ⟨v.nextEffect, positive, view, some tail⟩ {v with nextEffect := v.nextEffect + 1}
        (births ++ [v.nextEffect])

theorem signature_event_refines {c : Context} {position row : Nat} {concrete : List Nat}
    {p : Bool} {symbolVar : Option Nat} {s t : State} {bound : SignatureBound} {births : List Nat}
    (event : SignatureEvent c position concrete p symbolVar s row bound t births) :
    signatureEffect c position concrete symbolVar p s = (row, bound, t) := by
  cases event with
  | closed cached =>
      cases cached with
      | hit view found => simp [signatureEffect, found]
      | miss absent => simp [signatureEffect, absent]
  | tailed lookup cached =>
      have same := effect_memo_refines lookup
      simp only [signatureEffect, same]
      cases cached with
      | hit view found => simp [found]
      | miss absent => simp [absent]

inductive SignaturePairEvent (c : Context) (position : Nat) (concrete : List Nat)
    (symbolVar : Option Nat) : State → Ports → List SignatureBound → State → List Nat → Prop where
  | pair {s middle t : State} {positive negative : Nat} {pb nb : SignatureBound}
      {first second : List Nat}
      (pos : SignatureEvent c position concrete true symbolVar s positive pb middle first)
      (neg : SignatureEvent c position concrete false symbolVar middle negative nb t second) :
      SignaturePairEvent c position concrete symbolVar s
        ⟨.row positive, .row negative, none⟩ [pb, nb] t (first ++ second)

theorem signature_pair_event_refines {c : Context} {position : Nat} {concrete : List Nat}
    {symbolVar : Option Nat} {s t : State} {ports : Ports} {bounds : List SignatureBound}
    {births : List Nat}
    (event : SignaturePairEvent c position concrete symbolVar s ports bounds t births) :
    signaturePair c position concrete symbolVar s = (ports, bounds, t) := by
  cases event with
  | pair pos neg =>
      simp only [signaturePair, signature_event_refines pos, signature_event_refines neg]

/-- Branches follow candidate_formal_effect_port, including its singleton-symbol
shortcut before the positive delegation. Failure/refusal is not a success event. -/
inductive PortEvent (c : Context) : Bool → SourcePort → State → PortResult → List Nat → Prop where
  | omitted (p : Bool) (s : State) :
      PortEvent c p .omitted s
        ⟨sharedPorts s.nextEffect, [], [], {s with nextEffect := s.nextEffect + 1}⟩ [s.nextEffect]
  | symbolic {p : Bool} {s t : State} {name row : Nat} {births : List Nat}
      (lookup : EffectMemo c.scope name s row t births) :
      PortEvent c p (.symbolic name) s ⟨sharedPorts row, [], [], t⟩ births
  | singleton {p : Bool} {s t : State} {position name row : Nat} {births : List Nat}
      (lookup : EffectMemo c.scope name s row t births) :
      PortEvent c p (.explicit position [] (some name)) s ⟨sharedPorts row, [], [], t⟩ births
  | concrete (s : State) (position : Nat) (concrete : List Nat) (nonempty : concrete ≠ []) :
      PortEvent c false (.explicit position concrete none) s
        ⟨sharedPorts s.nextEffect (some (c.metadata position concrete)),
          [⟨c.metadata position concrete, s.nextEffect⟩], [],
          {s with nextEffect := s.nextEffect + 1}⟩ [s.nextEffect]
  | delegated {s t : State} {position : Nat} {concrete : List Nat} {symbolVar : Option Nat}
      {ports : Ports} {bounds : List SignatureBound} {births : List Nat}
      (notSingleton : ¬ (concrete = [] ∧ symbolVar ≠ none))
      (pair : SignaturePairEvent c position concrete symbolVar s ports bounds t births) :
      PortEvent c true (.explicit position concrete symbolVar) s ⟨ports, [], bounds, t⟩ births

theorem port_event_refines {c : Context} {p : Bool} {source : SourcePort}
    {s : State} {out : PortResult} {births : List Nat}
    (event : PortEvent c p source s out births) : constructPort c p source s = some out := by
  cases event with
  | omitted => rfl
  | symbolic lookup => simp [constructPort, effect_memo_refines lookup]
  | singleton lookup => simp [constructPort, effect_memo_refines lookup]
  | concrete s position concrete nonempty => simp [constructPort, nonempty]
  | delegated notSingleton pair =>
      simp [constructPort, notSingleton, signature_pair_event_refines pair]

/-- Every emitted grant has a row birth in these same successful events.
Memo hits and delegated signatures cannot fabricate an emitted grant. -/
theorem port_event_birth {c : Context} {p : Bool} {source : SourcePort}
    {s : State} {out : PortResult} {births : List Nat}
    (event : PortEvent c p source s out births)
    {entry : FormalPermissionLiveCapture.Emission} (member : entry ∈ out.entries) :
    entry.row ∈ births ∧ entry.row = s.nextEffect ∧
      out.state.nextEffect = s.nextEffect + 1 ∧ entry.metadata.concrete ≠ [] := by
  cases event with
  | concrete s position concrete nonempty =>
      simp only [List.mem_singleton] at member
      subst entry
      exact ⟨by simp, rfl, rfl, nonempty⟩
  | _ => simp at member

/- The structural events retain source order, composed polarity, shared context,
and every path. Their port children are the lower events above, rather than
assumed constructPort equalities. This is a refinement domain, not a claim of
exhaustiveness for native source constructors or source preflight. -/
mutual
  inductive ValueEvents (c : Context) : Bool → State → Shape → List Retained → State → List Nat → Prop where
    | scalar (p : Bool) (s : State) (identity : Nat) :
        ValueEvents c p s (.atom identity) [] s []
    | symbolVar (p : Bool) (s : State) (name : Nat) (hole : Bool) :
        ValueEvents c p s (.atom (scopedValue s c.scope name hole).1) []
          (scopedValue s c.scope name hole).2 []
    | function {p : Bool} {s s₁ s₂ : State} {a r : Shape} {as rs : List Retained}
        {ae re : SourcePort} {ao ro : PortResult} {ab rb aeb reb : List Nat}
        (argument : ValueEvents c (!p) s a as s₁ ab)
        (result : ValueEvents c p s₁ r rs s₂ rb)
        (argumentEffect : PortEvent c (!p) ae s₂ ao aeb)
        (resultEffect : PortEvent c p re ao.state ro reb) :
        ValueEvents c p s (.function a ao.ports r ro.ports)
          (prependPath .argument as ++ prependPath .result rs ++
            atPort .argument ao.entries ++ atPort .result ro.entries) ro.state
          (ab ++ rb ++ aeb ++ reb)
    | tuple {p : Bool} {s t : State} {elements : List Shape} {entries : List Retained} {births : List Nat}
        (children : TupleEvents c p s elements entries t births) (nonempty : elements ≠ []) :
        ValueEvents c p s (.tuple elements) entries t births
  inductive TupleEvents (c : Context) : Bool → State → List Shape → List Retained → State → List Nat → Prop where
    | nil (p : Bool) (s : State) : TupleEvents c p s [] [] s []
    | cons {p : Bool} {s middle t : State} {head : Shape} {tail : List Shape}
        {first rest : List Retained} {hb tb : List Nat}
        (child : ValueEvents c p s head first middle hb)
        (remaining : TupleEvents c p middle tail rest t tb) :
        TupleEvents c p s (head :: tail) (prependPath (.element 0) first ++ shift rest) t (hb ++ tb)
end

mutual
  theorem value_events_refine {c : Context} {p : Bool} {s t : State} {shape : Shape}
      {entries : List Retained} {births : List Nat}
      (events : ValueEvents c p s shape entries t births) : Construction c p s shape entries t := by
    cases events with
    | scalar p s identity => exact .scalar p s identity
    | symbolVar p s name hole => exact .symbolVar p s name hole
    | function argument result argumentEffect resultEffect =>
        exact .function (value_events_refine argument) (value_events_refine result)
          (port_event_refines argumentEffect) (port_event_refines resultEffect)
    | tuple children nonempty => exact .tuple (tuple_events_refine children) nonempty
  theorem tuple_events_refine {c : Context} {p : Bool} {s t : State} {elements : List Shape}
      {entries : List Retained} {births : List Nat}
      (events : TupleEvents c p s elements entries t births) : TupleConstruction c p s elements entries t := by
    cases events with
    | nil p s => exact .nil p s
    | cons child remaining => exact .cons (value_events_refine child) (tuple_events_refine remaining)
end

mutual
  theorem value_events_birth {c : Context} {p : Bool} {s t : State} {shape : Shape}
      {entries : List Retained} {births : List Nat}
      (events : ValueEvents c p s shape entries t births) :
      ∀ entry ∈ entries, entry.allocatedRow ∈ births := by
    cases events with
    | scalar => simp
    | symbolVar => simp
    | function argument result argumentEffect resultEffect =>
        intro entry member
        simp only [List.mem_append] at member ⊢
        rcases member with ((first | second) | third) | fourth
        · obtain ⟨e, mem, rfl⟩ := List.mem_map.mp first
          exact .inl (.inl (.inl (value_events_birth argument e mem)))
        · obtain ⟨e, mem, rfl⟩ := List.mem_map.mp second
          exact .inl (.inl (.inr (value_events_birth result e mem)))
        · obtain ⟨e, mem, rfl⟩ := List.mem_map.mp third
          exact .inl (.inr (port_event_birth argumentEffect mem).1)
        · obtain ⟨e, mem, rfl⟩ := List.mem_map.mp fourth
          exact .inr (port_event_birth resultEffect mem).1
    | tuple children _ => exact tuple_events_birth children
  theorem tuple_events_birth {c : Context} {p : Bool} {s t : State} {elements : List Shape}
      {entries : List Retained} {births : List Nat}
      (events : TupleEvents c p s elements entries t births) :
      ∀ entry ∈ entries, entry.allocatedRow ∈ births := by
    cases events with
    | nil => simp
    | cons child remaining =>
        intro entry member
        rcases List.mem_append.mp member with first | rest
        · obtain ⟨e, mem, rfl⟩ := List.mem_map.mp first
          exact List.mem_append_left _ (value_events_birth child e mem)
        · obtain ⟨e, mem, rfl⟩ := List.mem_map.mp rest
          exact List.mem_append_right _ (tuple_events_birth remaining e mem)
end

/-- One shared retained entry supplies its original metadata, complete path,
and allocated row to both the structural Origin and the event birth witness. -/
theorem event_origins_and_births {c : Context} {p : Bool} {s t : State} {shape : Shape}
    {entries : List Retained} {births : List Nat}
    (events : ValueEvents c p s shape entries t births) :
    ∀ entry ∈ entries, Origin shape p entry.path entry.allocatedRow entry.metadata ∧
      Owned c entry.metadata ∧ entry.allocatedRow ∈ births := by
  intro entry member
  obtain ⟨origin, owned⟩ := construction_origins (value_events_refine events) entry member
  exact ⟨origin, owned, value_events_birth events entry member⟩

/-- Application to the preceding finite-catalog parent. This supplies neither
live endpoint arrival nor native graph writes, canonical transport or export. -/
theorem event_catalog_export {c : Context} {s t : State} {shape : Shape}
    {entries : List Retained} {births : List Nat}
    (events : ValueEvents c false s shape entries t births) :
    projectAll shape entries = some (entries.map (fun e =>
      ⟨e.metadata, e.path, image shape (.effect (.row e.allocatedRow) false)⟩)) :=
  constructed_catalog_export (value_events_refine events)

end
end YulangClosure.FormalPermissionConstructorRealization
