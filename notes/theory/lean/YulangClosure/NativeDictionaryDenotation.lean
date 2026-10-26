import Init

/-!
Denotation of the actual chronological dictionary Word/Substitution DAGs in
tools/inference-playground/src/runtime/dispatch.rs. Scope identities are Nat;
Step is arbitrary and therefore retains the whole native Kind/Site payload.
This is dictionary algebra, not a definition of source typing or ValueMem.
-/
namespace YulangClosure.NativeDictionaryDenotation

structure Context (Step : Type) where
  base : Option Nat
  word : List Step
  deriving DecidableEq

structure RawContext where
  base : Option Nat
  word : Option Nat
  deriving DecidableEq

inductive WordNode (Step : Type) where
  | step (previous : Option Nat) (item : Step)
  | join (left right : Nat)

inductive WordArena (Step : Type) where
  | empty
  | push (old : WordArena Step) (node : WordNode Step)

def WordArena.size : WordArena Step → Nat
  | .empty => 0
  | .push old _ => old.size + 1

def wordAt : WordArena Step → Nat → Option (List Step)
  | .empty, _ => none
  | .push old node, i =>
      if i = old.size then
        match node with
        | .step previous item =>
            ((previous.map (wordAt old)).getD (some [])).map (· ++ [item])
        | .join left right => do
            let a ← wordAt old left
            let b ← wordAt old right
            pure (a ++ b)
      else wordAt old i

def word (arena : WordArena Step) (handle : Option Nat) : Option (List Step) :=
  match handle with
  | none => some []
  | some i => wordAt arena i

def context (arena : WordArena Step) (raw : RawContext) : Option (Context Step) :=
  (word arena raw.word).map (fun w => ⟨raw.base, w⟩)

theorem wordAt_bound {arena : WordArena Step} {i : Nat} {w : List Step}
    (found : wordAt arena i = some w) : i < arena.size := by
  induction arena with
  | empty => cases found
  | push old node ih =>
      simp only [wordAt] at found
      split at found
      · rename_i same
        subst i
        exact Nat.lt_succ_self _
      · exact Nat.lt_trans (ih found) (Nat.lt_succ_self _)

theorem wordAt_push_old {arena : WordArena Step} {i : Nat} {w : List Step}
    (found : wordAt arena i = some w) (node : WordNode Step) :
    wordAt (.push arena node) i = some w := by
  simp only [wordAt, ite_eq_right (Nat.ne_of_lt (wordAt_bound found)), found]

theorem word_push_old {arena : WordArena Step} {h : Option Nat} {w : List Step}
    (found : word arena h = some w) (node : WordNode Step) :
    word (.push arena node) h = some w := by
  cases h with
  | none => exact found
  | some i => exact wordAt_push_old found node

def append (arena : WordArena Step) (raw : RawContext) (item : Step) :
    WordArena Step × RawContext :=
  (.push arena (.step raw.word item), ⟨raw.base, some arena.size⟩)

theorem append_denotes {arena : WordArena Step} {raw : RawContext} {c : Context Step}
    (denotes : context arena raw = some c) (item : Step) :
    context (append arena raw item).1 (append arena raw item).2 =
      some ⟨c.base, c.word ++ [item]⟩ := by
  cases raw with
  | mk base handle =>
      cases handle with
      | none =>
          cases denotes
          simp [append, context, word, wordAt]
      | some i =>
          simp only [context, word] at denotes
          cases found : wordAt arena i with
          | none => simp [found] at denotes
          | some xs =>
              simp only [found, Option.map_some] at denotes
              cases denotes
              simp [append, context, word, wordAt, found]

def join (arena : WordArena Step) (a b : Option Nat) : WordArena Step × Option Nat :=
  match a, b with
  | none, h | h, none => (arena, h)
  | some i, some j => (.push arena (.join i j), some arena.size)

theorem join_denotes {arena : WordArena Step} {a b : Option Nat} {x y : List Step}
    (ha : word arena a = some x) (hb : word arena b = some y) :
    word (join arena a b).1 (join arena a b).2 = some (x ++ y) := by
  cases a with
  | none => cases ha; exact hb
  | some i =>
      cases b with
      | none => cases hb; simpa only [join, Prod.fst, Prod.snd, List.append_nil] using ha
      | some j => simp [join, word, wordAt, word] at *; simp_all

structure Assignment (Step : Type) where
  scope : Nat
  replacement : Context Step

def assign (a : Assignment Step) (c : Context Step) : Context Step :=
  if c.base = some a.scope then
    ⟨a.replacement.base, a.replacement.word ++ c.word⟩
  else c

def action (as : List (Assignment Step)) (c : Context Step) : Context Step :=
  as.foldl (fun c a => assign a c) c

theorem action_append (a b : List (Assignment Step)) (c : Context Step) :
    action (a ++ b) c = action b (action a c) := by
  exact List.foldl_append

inductive SubNode where
  | assign (scope : Nat) (replacement : RawContext)
  | then (first second : Nat)

inductive SubArena where
  | empty
  | push (old : SubArena) (node : SubNode)

def SubArena.size : SubArena → Nat
  | .empty => 0
  | .push old _ => old.size + 1

def subAt (words : WordArena Step) : SubArena → Nat → Option (List (Assignment Step))
  | .empty, _ => none
  | .push old node, i =>
      if i = old.size then
        match node with
        | .assign scope raw => (context words raw).map (fun c => [⟨scope, c⟩])
        | .then first second => do
            let a ← subAt words old first
            let b ← subAt words old second
            pure (a ++ b)
      else subAt words old i

def substitution (words : WordArena Step) (subs : SubArena) (h : Option Nat) :
    Option (List (Assignment Step)) :=
  match h with
  | none => some []
  | some i => subAt words subs i

theorem subAt_bound {words : WordArena Step} {subs : SubArena} {i : Nat}
    {as : List (Assignment Step)} (h : subAt words subs i = some as) : i < subs.size := by
  induction subs with
  | empty => cases h
  | push old node ih =>
      simp only [subAt] at h
      split at h
      · rename_i same
        subst i
        exact Nat.lt_succ_self _
      · exact Nat.lt_trans (ih h) (Nat.lt_succ_self _)

theorem subAt_push_old {words : WordArena Step} {subs : SubArena} {i : Nat}
    {as : List (Assignment Step)} (h : subAt words subs i = some as) (node : SubNode) :
    subAt words (.push subs node) i = some as := by
  simp only [subAt, ite_eq_right (Nat.ne_of_lt (subAt_bound h)), h]

theorem substitution_push_old {words : WordArena Step} {subs : SubArena} {i : Option Nat}
    {as : List (Assignment Step)} (h : substitution words subs i = some as) (node : SubNode) :
    substitution words (.push subs node) i = some as := by
  cases i with
  | none => exact h
  | some i => exact subAt_push_old h node

def compose (subs : SubArena) (first second : Option Nat) : SubArena × Option Nat :=
  match first, second with
  | none, h | h, none => (subs, h)
  | some a, some b => (.push subs (.then a b), some subs.size)

theorem then_denotes {words : WordArena Step} {subs : SubArena}
    {first second : Option Nat} {a b : List (Assignment Step)}
    (ha : substitution words subs first = some a)
    (hb : substitution words subs second = some b) :
    substitution words (compose subs first second).1 (compose subs first second).2 =
      some (a ++ b) := by
  cases first with
  | none => cases ha; exact hb
  | some i =>
      cases second with
      | none => cases hb; simpa only [compose, Prod.fst, Prod.snd, List.append_nil] using ha
      | some j => simp [compose, substitution, subAt, substitution] at *; simp_all

theorem then_action {words : WordArena Step} {subs : SubArena}
    {first second : Option Nat} {a b : List (Assignment Step)}
    (ha : substitution words subs first = some a)
    (hb : substitution words subs second = some b) (c : Context Step) :
    (substitution words (compose subs first second).1 (compose subs first second).2).map
      (fun as => action as c) = some (action b (action a c)) := by
  rw [then_denotes ha hb]
  exact congrArg some (action_append a b c)

/-- The decoded Name action, retaining the raw current context in its Assign.
The actual arena theorem below supplies the same ordered list for raw Name. -/
def nameAction (value current : List (Assignment Step)) (caller : Context Step)
    (cell : Nat) (instantiate : Option Step) : List (Assignment Step) :=
  match instantiate with
  | none => value ++ current
  | some item => value ++ [⟨cell, ⟨caller.base, caller.word ++ [item]⟩⟩] ++ current

theorem name_action_none (value current : List (Assignment Step))
    (caller input : Context Step) (cell : Nat) :
    action (nameAction value current caller cell none) input =
      action current (action value input) := action_append _ _ _

theorem name_action_some (value current : List (Assignment Step))
    (caller input : Context Step) (cell : Nat) (item : Step) :
    action (nameAction value current caller cell (some item)) input =
      action current
        (assign ⟨cell, ⟨caller.base, caller.word ++ [item]⟩⟩ (action value input)) := by
  simp only [nameAction]
  rw [action_append, action_append]
  rfl


/-- Successful meanings of old word handles suffice; invalid future handles are
not required to stay invalid after arena allocation. -/
theorem context_transport {old new : WordArena Step}
    (keep : ∀ h w, word old h = some w → word new h = some w)
    {raw : RawContext} {c : Context Step} (h : context old raw = some c) :
    context new raw = some c := by
  cases hw : word old raw.word with
  | none => simp [context, hw] at h
  | some w =>
      have hn := keep raw.word w hw
      simpa only [context, hw, hn] using h

theorem subAt_word_transport {old new : WordArena Step}
    (keep : ∀ h w, word old h = some w → word new h = some w)
    {subs : SubArena} {i : Nat} {as : List (Assignment Step)}
    (h : subAt old subs i = some as) : subAt new subs i = some as := by
  induction subs generalizing i as with
  | empty => cases h
  | push before node ih =>
      by_cases eq : i = before.size
      · subst i
        cases node with
        | assign scope raw =>
            simp only [subAt, ite_true] at h ⊢
            cases hc : context old raw with
            | none => simp [hc] at h
            | some c =>
                have hn := context_transport keep hc
                simpa only [hc, hn] using h
        | «then» first second =>
            simp only [subAt, ite_true] at h ⊢
            cases ha : subAt old before first with
            | none => simp [ha] at h
            | some a =>
                cases hb : subAt old before second with
                | none => simp [ha, hb] at h
                | some b =>
                    have hna := ih ha
                    have hnb := ih hb
                    simpa only [ha, hb, hna, hnb] using h
      · simp only [subAt, ite_eq_right eq] at h ⊢
        exact ih h

theorem substitution_word_push {words : WordArena Step} {subs : SubArena}
    {handle : Option Nat} {as : List (Assignment Step)}
    (h : substitution words subs handle = some as) (node : WordNode Step) :
    substitution (.push words node) subs handle = some as := by
  cases handle with
  | none => exact h
  | some i => exact subAt_word_transport (fun _ _ hw => word_push_old hw node) h

theorem compose_keeps_old {words : WordArena Step} {subs : SubArena}
    {handle : Option Nat} {as : List (Assignment Step)}
    (h : substitution words subs handle = some as) (first second : Option Nat) :
    substitution words (compose subs first second).1 handle = some as := by
  cases first with
  | none => exact h
  | some first =>
      cases second with
      | none => exact h
      | some second => exact substitution_push_old h (.then first second)

structure State where
  context : RawContext
  substitution : Option Nat

structure NameResult (Step : Type) where
  words : WordArena Step
  substitutions : SubArena
  result : Option Nat

/-- Allocation-success branch of Rust `Machine::name`. The entry check that an
instantiated cell has a default is exposed separately by `nameChecked`. -/
def name (words : WordArena Step) (subs : SubArena) (value : Option Nat)
    (current : State) (cell : Nat) (instantiate : Option Step) : NameResult Step :=
  match instantiate with
  | none =>
      let result := compose subs value current.substitution
      ⟨words, result.1, result.2⟩
  | some item =>
      let appended := append words current.context item
      let assigned := SubArena.push subs (.assign cell appended.2)
      let first := compose assigned value (some subs.size)
      let result := compose first.1 first.2 current.substitution
      ⟨appended.1, result.1, result.2⟩

def nameChecked (defaults : Nat → Option RawContext) (words : WordArena Step)
    (subs : SubArena) (value : Option Nat) (current : State) (cell : Nat)
    (instantiate : Option Step) : Option (NameResult Step) :=
  match instantiate with
  | none => some (name words subs value current cell none)
  | some item =>
      match defaults cell with
      | none => none
      | some _ => some (name words subs value current cell (some item))

/-- The actual arena Name construction decodes to precisely the value action,
optional symbolic assignment, and caller action in that order. -/
theorem name_denotes {words : WordArena Step} {subs : SubArena}
    {value : Option Nat} {current : State} {v c : List (Assignment Step)}
    {caller : Context Step}
    (hv : substitution words subs value = some v)
    (hc : substitution words subs current.substitution = some c)
    (hcaller : context words current.context = some caller)
    (cell : Nat) (instantiate : Option Step) :
    substitution (name words subs value current cell instantiate).words
      (name words subs value current cell instantiate).substitutions
      (name words subs value current cell instantiate).result =
        some (nameAction v c caller cell instantiate) := by
  cases instantiate with
  | none => exact then_denotes hv hc
  | some item =>
      let newWords := (append words current.context item).1
      let replacement := (append words current.context item).2
      let assigned := SubArena.push subs (.assign cell replacement)
      let first := compose assigned value (some subs.size)
      have hvw : substitution newWords subs value = some v :=
        substitution_word_push hv (.step current.context.word item)
      have hcw : substitution newWords subs current.substitution = some c :=
        substitution_word_push hc (.step current.context.word item)
      have hva : substitution newWords assigned value = some v :=
        substitution_push_old hvw (.assign cell replacement)
      have hca : substitution newWords assigned current.substitution = some c :=
        substitution_push_old hcw (.assign cell replacement)
      have fresh : substitution newWords assigned (some subs.size) =
          some [⟨cell, ⟨caller.base, caller.word ++ [item]⟩⟩] := by
        simp only [substitution, assigned, subAt, ite_true]
        have hr : context newWords replacement =
            some ⟨caller.base, caller.word ++ [item]⟩ := append_denotes hcaller item
        rw [hr]
        rfl
      have hf := then_denotes hva fresh
      have hcf := compose_keeps_old hca value (some subs.size)
      exact then_denotes hf hcf

theorem name_checked_denotes {defaults : Nat → Option RawContext}
    {words : WordArena Step} {subs : SubArena} {value : Option Nat} {current : State}
    {v c : List (Assignment Step)} {caller : Context Step}
    (hv : substitution words subs value = some v)
    (hc : substitution words subs current.substitution = some c)
    (hcaller : context words current.context = some caller)
    (cell : Nat) (instantiate : Option Step)
    (ready : instantiate.isSome = true → (defaults cell).isSome = true) :
    (nameChecked defaults words subs value current cell instantiate).bind
      (fun result => substitution result.words result.substitutions result.result) =
        some (nameAction v c caller cell instantiate) := by
  cases instantiate with
  | none => exact name_denotes hv hc hcaller cell none
  | some item =>
      cases hd : defaults cell with
      | none => simp [hd] at ready
      | some raw =>
          simpa only [nameChecked, hd, Option.bind_some] using
            name_denotes hv hc hcaller cell (some item)


theorem context_fields {words : WordArena Step} {raw : RawContext} {c : Context Step} :
    context words raw = some c ↔
      raw.base = c.base ∧ word words raw.word = some c.word := by
  cases c with
  | mk base items =>
      cases h : word words raw.word with
      | none => simp [context, h]
      | some items' => simp [context, h, Context.mk.injEq]

theorem join_keeps_old {words : WordArena Step} {handle : Option Nat} {items : List Step}
    (h : word words handle = some items) (left right : Option Nat) :
    word (join words left right).1 handle = some items := by
  cases left with
  | none => exact h
  | some left =>
      cases right with
      | none => exact h
      | some right => exact word_push_old h (.join left right)

/-- Exact matching-base branch of `apply_bounded`; replacement words precede
existing words. Nonmatching assignments perform no allocation. -/
def assignRaw (words : WordArena Step) (scope : Nat) (replacement input : RawContext) :
    WordArena Step × RawContext :=
  if input.base = some scope then
    let joined := join words replacement.word input.word
    ⟨joined.1, ⟨replacement.base, joined.2⟩⟩
  else ⟨words, input⟩

theorem assignRaw_denotes {words : WordArena Step} {replacement input : RawContext}
    {r c : Context Step} (hr : context words replacement = some r)
    (hc : context words input = some c) (scope : Nat) :
    context (assignRaw words scope replacement input).1
      (assignRaw words scope replacement input).2 = some (assign ⟨scope, r⟩ c) := by
  obtain ⟨rb, rw⟩ := context_fields.mp hr
  obtain ⟨cb, cw⟩ := context_fields.mp hc
  by_cases h : input.base = some scope
  · have h' : c.base = some scope := cb ▸ h
    simp only [assignRaw, h, ite_true, assign, h']
    simp only [context]
    rw [join_denotes rw cw]
    simp only [Option.map_some, rb]
  · have h' : c.base ≠ some scope := by simpa only [cb] using h
    simpa only [assignRaw, h, ite_false, assign, h'] using hc

theorem assignRaw_keeps_old {words : WordArena Step} {handle : Option Nat} {items : List Step}
    (h : word words handle = some items) (scope : Nat) (replacement input : RawContext) :
    word (assignRaw words scope replacement input).1 handle = some items := by
  by_cases eq : input.base = some scope
  · simp only [assignRaw, eq, ite_true]
    exact join_keeps_old h replacement.word input.word
  · simpa only [assignRaw, eq, ite_false] using h

/-- Mathematical application of the actual substitution DAG. Backward children
are evaluated in native pending-stack order. Allocator failure and WORK_LIMIT
remain runtime gates; this function does not assert that those gates pass. -/
def applyDag (words : WordArena Step) : SubArena → Nat → RawContext →
    Option (WordArena Step × RawContext)
  | .empty, _, _ => none
  | .push before node, i, input =>
      if i = before.size then
        match node with
        | .assign scope replacement => some (assignRaw words scope replacement input)
        | .then first second => do
            let middle ← applyDag words before first input
            applyDag middle.1 before second middle.2
      else applyDag words before i input

/-- The raw DAG application is constructed from its node meanings. In the same
result it preserves all existing word handles and realizes the ordered action. -/
theorem applyDag_denotes {words : WordArena Step} {subs : SubArena} {i : Nat}
    {as : List (Assignment Step)} {raw : RawContext} {input : Context Step}
    (hs : subAt words subs i = some as) (hi : context words raw = some input) :
    ∃ result, applyDag words subs i raw = some result ∧
      context result.1 result.2 = some (action as input) ∧
      (∀ handle items, word words handle = some items → word result.1 handle = some items) := by
  induction subs generalizing words i as raw input with
  | empty => cases hs
  | push before node ih =>
      by_cases eq : i = before.size
      · subst i
        cases node with
        | assign scope replacement =>
            simp only [subAt, ite_true] at hs
            cases hr : context words replacement with
            | none => simp [hr] at hs
            | some r =>
                simp only [hr, Option.map_some] at hs
                cases hs
                refine ⟨assignRaw words scope replacement raw, ?_, ?_, ?_⟩
                · simp only [applyDag, ite_true]
                · simpa only [action, List.foldl_cons, List.foldl_nil] using
                    assignRaw_denotes hr hi scope
                · intro handle items h
                  exact assignRaw_keeps_old h scope replacement raw
        | «then» first second =>
            simp only [subAt, ite_true] at hs
            cases ha : subAt words before first with
            | none => simp [ha] at hs
            | some a =>
                cases hb : subAt words before second with
                | none => simp [ha, hb] at hs
                | some b =>
                    simp only [ha, hb, pure] at hs
                    cases hs
                    obtain ⟨middle, hfirst, hm, keepFirst⟩ := ih ha hi
                    have hb' := subAt_word_transport keepFirst hb
                    obtain ⟨result, hsecond, hout, keepSecond⟩ := ih hb' hm
                    refine ⟨result, ?_, ?_, ?_⟩
                    · simp only [applyDag, ite_true, hfirst]
                      exact hsecond
                    · simpa only [action_append] using hout
                    · intro handle items h
                      exact keepSecond handle items (keepFirst handle items h)
      · simp only [subAt, ite_eq_right eq] at hs
        obtain ⟨result, hr, hc, keep⟩ := ih hs hi
        refine ⟨result, ?_, hc, keep⟩
        simpa only [applyDag, ite_eq_right eq] using hr

/-- The native initializer inserts its raw parent even on a duplicate-cell
error. Allocation failures are outside this mathematical success branch. -/
def initializer (defaults : Nat → Option RawContext) (cell : Nat) (parent : State) :
    (Nat → Option RawContext) × Option State :=
  (fun scope => if scope = cell then some parent.context else defaults scope,
   if (defaults cell).isSome then none
   else some ⟨⟨some cell, none⟩, parent.substitution⟩)

theorem initialize_fresh (defaults : Nat → Option RawContext) (cell : Nat) (parent : State)
    (fresh : defaults cell = none) :
    (initializer defaults cell parent).1 cell = some parent.context ∧
    (initializer defaults cell parent).2 =
      some ⟨⟨some cell, none⟩, parent.substitution⟩ := by
  simp [initializer, fresh]

/-- Finite default-chain interpretation. Fuel counts default unfoldings, not
Rust's combined WORK_LIMIT counter. It retains cyclic/missing defaults as failure. -/
def resolve (defaults : Nat → Option (Context Step)) (sub : List (Assignment Step)) :
    Nat → Context Step → Option (List Step)
  | fuel, input =>
      match input.base with
      | none => some input.word
      | some scope =>
          match fuel with
          | 0 => none
          | n + 1 => do
              let parent ← defaults scope
              let applied := action sub parent
              resolve defaults sub n ⟨applied.base, applied.word ++ input.word⟩

def dispatchMeaning (words : WordArena Step) (subs : SubArena)
    (defaults : Nat → Option (Context Step)) (fuel : Nat) (state : State) :
    Option (List Step) := do
  let input ← context words state.context
  let sub ← substitution words subs state.substitution
  resolve defaults sub fuel (action sub input)

theorem resolve_default {defaults : Nat → Option (Context Step)}
    {scope : Nat} {parent : Context Step} (hd : defaults scope = some parent)
    (sub : List (Assignment Step)) (fuel : Nat) (items : List Step) :
    resolve defaults sub (fuel + 1) ⟨some scope, items⟩ =
      resolve defaults sub fuel
        ⟨(action sub parent).base, (action sub parent).word ++ items⟩ := by
  change (defaults scope).bind (fun parent =>
    resolve defaults sub fuel
      ⟨(action sub parent).base, (action sub parent).word ++ items⟩) = _
  rw [hd]
  rfl

theorem name_keeps_context {words : WordArena Step} {raw : RawContext} {input : Context Step}
    (h : context words raw = some input) (subs : SubArena) (value : Option Nat)
    (current : State) (cell : Nat) (instantiate : Option Step) :
    context (name words subs value current cell instantiate).words raw = some input := by
  cases instantiate with
  | none => exact h
  | some item =>
      exact context_transport (fun _ _ hw => word_push_old hw (.step current.context.word item)) h

/-- Every finite default unfolding and the whole resulting word are retained.
The right side can still fail; this is not a success or termination assumption. -/
theorem name_dispatch_meaning {words : WordArena Step} {subs : SubArena}
    {value : Option Nat} {current : State} {v c : List (Assignment Step)}
    {caller input : Context Step} {raw : RawContext}
    (hv : substitution words subs value = some v)
    (hc : substitution words subs current.substitution = some c)
    (hcaller : context words current.context = some caller)
    (hinput : context words raw = some input)
    (defaults : Nat → Option (Context Step)) (fuel cell : Nat) (instantiate : Option Step) :
    dispatchMeaning (name words subs value current cell instantiate).words
      (name words subs value current cell instantiate).substitutions defaults fuel
      ⟨raw, (name words subs value current cell instantiate).result⟩ =
        resolve defaults (nameAction v c caller cell instantiate) fuel
          (action (nameAction v c caller cell instantiate) input) := by
  simp only [dispatchMeaning]
  rw [name_keeps_context hinput, name_denotes hv hc hcaller]
  rfl

/-- The dictionary is fixed at the same arbitrary world/witness parameter on
both sides. This gives the exact selected label, not a source certificate for it. -/
theorem name_dictionary_denotation {World Site Binding : Type}
    (dictionary : World → List Step → Site → Option Binding) (witness : World) (site : Site)
    {words : WordArena Step} {subs : SubArena} {value : Option Nat} {current : State}
    {v c : List (Assignment Step)} {caller input : Context Step} {raw : RawContext}
    (hv : substitution words subs value = some v)
    (hc : substitution words subs current.substitution = some c)
    (hcaller : context words current.context = some caller)
    (hinput : context words raw = some input)
    (defaults : Nat → Option (Context Step)) (fuel cell : Nat) (instantiate : Option Step) :
    (dispatchMeaning (name words subs value current cell instantiate).words
      (name words subs value current cell instantiate).substitutions defaults fuel
      ⟨raw, (name words subs value current cell instantiate).result⟩).bind
        (fun key => dictionary witness key site) =
      (resolve defaults (nameAction v c caller cell instantiate) fuel
        (action (nameAction v c caller cell instantiate) input)).bind
          (fun key => dictionary witness key site) := by
  rw [name_dispatch_meaning hv hc hcaller hinput]

/-- Same finite concrete assignment sequence as the native regression witness. -/
def orderedExample : List (Assignment Nat) :=
  [⟨1, ⟨none, []⟩⟩, ⟨0, ⟨some 1, []⟩⟩]

theorem caller_action_not_idempotent :
    action orderedExample ⟨some 0, []⟩ = ⟨some 1, []⟩ ∧
    action orderedExample (action orderedExample ⟨some 0, []⟩) = ⟨none, []⟩ := by
  decide

theorem name_applies_caller_once :
    action (nameAction [] orderedExample ⟨some 0, []⟩ 2 (some 7)) ⟨some 2, []⟩ =
      ⟨some 1, [7]⟩ := by
  decide

theorem cyclic_default_fails (fuel : Nat) :
    resolve (fun _ => some (⟨some 0, []⟩ : Context Nat)) [] fuel ⟨some 0, []⟩ = none := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
      change resolve (fun _ => some (⟨some 0, []⟩ : Context Nat)) [] n ⟨some 0, []⟩ = none
      exact ih


/-- Raw default entries, exactly as stored by `initializer`, interpreted only
through the word arena. No descriptor or source-typing predicate occurs here. -/
def defaultMeaning (words : WordArena Step) (defaults : Nat → Option RawContext)
    (cell : Nat) : Option (Context Step) :=
  (defaults cell).bind (context words)

def DefaultsValid (words : WordArena Step) (defaults : Nat → Option RawContext) : Prop :=
  ∀ cell raw, defaults cell = some raw → ∃ c, context words raw = some c

theorem empty_defaults_valid (words : WordArena Step) :
    DefaultsValid words (fun _ => none) := by
  intro cell raw h
  cases h

theorem initializer_defaults_valid {words : WordArena Step} {defaults : Nat → Option RawContext}
    (valid : DefaultsValid words defaults) (cell : Nat) (parent : State)
    {c : Context Step} (hp : context words parent.context = some c) :
    DefaultsValid words (initializer defaults cell parent).1 := by
  intro scope raw h
  by_cases eq : scope = cell
  · simp only [initializer, eq, ite_true] at h
    cases h
    exact ⟨c, hp⟩
  · simp only [initializer, eq, ite_false] at h
    exact valid scope raw h

theorem name_defaults_unchanged {words : WordArena Step} {defaults : Nat → Option RawContext}
    (valid : DefaultsValid words defaults) (subs : SubArena) (value : Option Nat)
    (current : State) (cell : Nat) (instantiate : Option Step) :
    defaultMeaning (name words subs value current cell instantiate).words defaults =
      defaultMeaning words defaults := by
  funext scope
  cases hd : defaults scope with
  | none => simp only [defaultMeaning, hd, Option.bind_none]
  | some raw =>
      obtain ⟨c, hc⟩ := valid scope raw hd
      have hn := name_keeps_context hc subs value current cell instantiate
      simp only [defaultMeaning, hd, Option.bind_some, hn, hc]

/-- Native raw-default version of the lookup equation. The same complete raw
default map, dictionary, witness and member site occur on both sides. -/
theorem name_raw_dictionary_denotation {World Site Binding : Type}
    (dictionary : World → List Step → Site → Option Binding) (witness : World) (site : Site)
    {words : WordArena Step} {subs : SubArena} {value : Option Nat} {current : State}
    {v c : List (Assignment Step)} {caller input : Context Step} {raw : RawContext}
    {defaults : Nat → Option RawContext} (valid : DefaultsValid words defaults)
    (hv : substitution words subs value = some v)
    (hc : substitution words subs current.substitution = some c)
    (hcaller : context words current.context = some caller)
    (hinput : context words raw = some input)
    (fuel cell : Nat) (instantiate : Option Step) :
    (dispatchMeaning (name words subs value current cell instantiate).words
      (name words subs value current cell instantiate).substitutions
      (defaultMeaning (name words subs value current cell instantiate).words defaults) fuel
      ⟨raw, (name words subs value current cell instantiate).result⟩).bind
        (fun key => dictionary witness key site) =
      (resolve (defaultMeaning words defaults) (nameAction v c caller cell instantiate) fuel
        (action (nameAction v c caller cell instantiate) input)).bind
          (fun key => dictionary witness key site) := by
  rw [name_defaults_unchanged valid]
  exact name_dictionary_denotation dictionary witness site hv hc hcaller hinput
    (defaultMeaning words defaults) fuel cell instantiate


/-- Checked native entry guard and complete dictionary equation in one theorem.
The constructor's success is derived from its actual raw inputs and ready-cell
condition; dictionary/default resolution is allowed to return `none`. -/
theorem name_checked_dictionary_denotation {World Site Binding : Type}
    (dictionary : World → List Step → Site → Option Binding) (witness : World) (site : Site)
    {words : WordArena Step} {subs : SubArena} {value : Option Nat} {current : State}
    {v c : List (Assignment Step)} {caller input : Context Step} {raw : RawContext}
    {defaults : Nat → Option RawContext} (valid : DefaultsValid words defaults)
    (hv : substitution words subs value = some v)
    (hc : substitution words subs current.substitution = some c)
    (hcaller : context words current.context = some caller)
    (hinput : context words raw = some input)
    (fuel cell : Nat) (instantiate : Option Step)
    (ready : instantiate.isSome = true → (defaults cell).isSome = true) :
    (nameChecked defaults words subs value current cell instantiate).bind
      (fun result =>
        (dispatchMeaning result.words result.substitutions
          (defaultMeaning result.words defaults) fuel ⟨raw, result.result⟩).bind
            (fun key => dictionary witness key site)) =
      (resolve (defaultMeaning words defaults) (nameAction v c caller cell instantiate) fuel
        (action (nameAction v c caller cell instantiate) input)).bind
          (fun key => dictionary witness key site) := by
  cases instantiate with
  | none =>
      exact name_raw_dictionary_denotation dictionary witness site valid hv hc hcaller hinput
        fuel cell none
  | some item =>
      cases hd : defaults cell with
      | none => simp [hd] at ready
      | some parent =>
          simpa only [nameChecked, hd, Option.bind_some] using
            name_raw_dictionary_denotation dictionary witness site valid hv hc hcaller hinput
              fuel cell (some item)

end YulangClosure.NativeDictionaryDenotation
