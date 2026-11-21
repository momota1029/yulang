import Yulang.GeneralOrderedDictionaryCheck309

namespace Yulang.GeneralOrderedDictionaryFault309
open CommonRoleOutermostResolver (Dictionary)
open GeneralOrderedDictionaryCheck309 (Error ordered validate)
open GeneralGeneratedDictionaryRun299 (Read Entry)

def Earlier (check : Nat → Dictionary → Except Error Unit) (is : List Nat)
    (ds : List Dictionary) (pos : Nat) : Prop :=
  ∀ before < pos, ∃ i d, is[before]? = some i ∧ ds[before]? = some d ∧ check i d = .ok ()

/-- These premises describe the actual mismatch, not a resolver outcome.
At a nested failure all ancestors have passed their local key/arity gates. -/
inductive Explains (read : Read) : Nat → Nat → Dictionary → Error → Prop where
  | fuel (i : Nat) (d : Dictionary) : Explains read 0 i d (.fuel i)
  | missing (n i : Nat) (d : Dictionary) :
      read i = none → Explains read (n+1) i d (.missing i)
  | key (n i k : Nat) (ds : List Dictionary) (row : Entry) :
      read i = some row → k ≠ row.key →
      Explains read (n+1) i (.node k ds) (.wrongKey i row.key k)
  | arity (n i : Nat) (ds : List Dictionary) (row : Entry) :
      read i = some row → ds.length ≠ row.children.length →
      Explains read (n+1) i (.node row.key ds) (.wrongArity i row.children.length ds.length)
  | child (n i pos j : Nat) (row : Entry) (ds : List Dictionary) (d : Dictionary) (fault : Error) :
      read i = some row → ds.length = row.children.length →
      row.children[pos]? = some j → ds[pos]? = some d →
      Earlier (validate read n) row.children ds pos →
      Explains read n j d fault →
      Explains read (n+1) i (.node row.key ds) (.child i pos fault)

theorem ordered_failure (check : Nat → Dictionary → Except Error Unit) (parent : Nat)
    (pos : Nat) (xs : List Nat) (ds : List Dictionary) (error : Error)
    (count : ds.length = xs.length) (bad : ordered check parent pos xs ds = .error error) :
    ∃ offset i d fault, xs[offset]? = some i ∧ ds[offset]? = some d ∧
      check i d = .error fault ∧ Earlier check xs ds offset ∧ error = .child parent (pos+offset) fault := by
  induction xs generalizing ds pos with
  | nil =>
    cases ds
    · cases bad
    · simp at count
  | cons x xs ih =>
    cases ds with
    | nil => simp at count
    | cons d ds =>
      cases checked : check x d with
      | error problem =>
        have same : Error.child parent pos problem = error := by simpa [ordered,checked] using bad
        exact ⟨0,x,d,problem,rfl,rfl,checked,by intro _ impossible; omega,by simpa using same.symm⟩
      | ok got =>
        obtain ⟨offset,i,fragment,fault,a,b,run,early,e⟩ := ih (pos+1) ds
          (by simpa using count) (by simpa [ordered,checked] using bad)
        refine ⟨offset+1,i,fragment,fault,a,b,run,?_,?_⟩
        · intro k lt
          cases k with
          | zero =>
            cases got
            exact ⟨x,d,rfl,rfl,checked⟩
          | succ k => exact early k (by omega)
        · have assoc : pos+1+offset = pos+(offset+1) := by omega
          rw [e,assoc]

theorem explains (read : Read) (fuel i : Nat) (d : Dictionary) (fault : Error)
    (failure : validate read fuel i d = .error fault) : Explains read fuel i d fault := by
  induction fuel generalizing i d fault with
  | zero =>
    have eq : Error.fuel i = fault := Except.error.inj failure
    cases eq
    exact .fuel i d
  | succ n ih =>
    cases d with
    | node key ds =>
      cases hit : read i with
      | none =>
        have eq : Error.missing i = fault := by simpa [validate,hit] using failure
        cases eq
        exact .missing n i _ hit
      | some row =>
        by_cases keyed : key = row.key
        · subst key
          by_cases len : ds.length = row.children.length
          · have orderedBad : ordered (validate read n) i 0 row.children ds = .error fault := by
              simpa [validate,hit,len] using failure
            obtain ⟨pos,j,frag,inner,first,last,childBad,earlier,same⟩ :=
              ordered_failure _ i 0 _ _ _ len orderedBad
            simp only [Nat.zero_add] at same
            rw [same]
            exact .child n i pos j row ds frag inner hit len first last earlier (ih j frag inner childBad)
          · have eq : Error.wrongArity i row.children.length ds.length = fault := by
              simpa [validate,hit,len] using failure
            subst fault
            exact .arity n i ds row hit len
        · have eq : Error.wrongKey i row.key key = fault := by simpa [validate,hit,keyed] using failure
          subst fault
          exact .key n i key ds row hit keyed

theorem ordered_reports (check : Nat → Dictionary → Except Error Unit) (parent offset pos : Nat)
    (xs : List Nat) (ds : List Dictionary) (i : Nat) (d : Dictionary) (fault : Error)
    (one : xs[offset]? = some i) (two : ds[offset]? = some d)
    (bad : check i d = .error fault) (early : Earlier check xs ds offset) :
    ordered check parent pos xs ds = .error (.child parent (pos+offset) fault) := by
  induction offset generalizing pos xs ds with
  | zero =>
    cases xs with
    | nil => cases one
    | cons head rest =>
      cases ds with
      | nil => cases two
      | cons first many =>
        cases Option.some.inj one
        cases Option.some.inj two
        simp [ordered,bad]
  | succ k ih =>
    cases xs with
    | nil => cases one
    | cons head rest =>
      cases ds with
      | nil => cases two
      | cons first many =>
        obtain ⟨j,g,headEq,firstEq,ok⟩ := early 0 (by omega)
        cases Option.some.inj headEq
        cases Option.some.inj firstEq
        have prior : Earlier check rest many k := by
          intro q lt
          exact early (q+1) (by omega)
        have further := ih (pos+1) rest many one two prior
        have offsets : pos+1+k = pos+(k+1) := by omega
        simpa [ordered,ok,offsets] using further

theorem reports {read : Read} {fuel i : Nat} {d : Dictionary} {fault : Error}
    (reason : Explains read fuel i d fault) : validate read fuel i d = .error fault := by
  induction reason with
  | fuel => rfl
  | missing _ _ d h => cases d; simp [validate,h]
  | key _ _ _ _ _ h neq => simp [validate,h,neq]
  | arity _ _ _ _ hit neq => simp [validate,hit,neq]
  | child n i pos j row ds d fault hit len index piece prior chosen ih =>
    have failure := ordered_reports (validate read n) i pos 0 _ _ j d fault index piece ih prior
    simpa [validate,hit,len] using failure

theorem exact {read : Read} {fuel i : Nat} {d : Dictionary} {fault : Error} :
    validate read fuel i d = .error fault ↔ Explains read fuel i d fault :=
  ⟨explains _ _ _ _ _,reports⟩

end Yulang.GeneralOrderedDictionaryFault309
