import YulangClosure.Contracts

namespace YulangClosure
variable {C K W R O B : Type}
variable (m : Machine C K W R O) (a : Analysis C B O)
variable (laws : LocalLaws m a) (cert : Certificate a)

/-- Independent typing and ONE joint concrete/abstract witness at this point. -/
def Invariant (c : C) : Prop :=
  laws.typed c ∧ ∃ b, a.represents c b ∧ cert.contains b

theorem initial_invariant {c : C} (hc : laws.initial c) :
    Invariant m a laws cert c := by
  obtain ⟨b, hs, hr⟩ := laws.initial_seed c hc
  exact ⟨laws.initial_typing c hc, b, hr, cert.seeds c b hs⟩

theorem step_invariant {c d : C}
    (hc : Invariant m a laws cert c) (h : Step m c d) :
    Invariant m a laws cert d := by
  obtain ⟨ht, b, hr, hu⟩ := hc
  cases h with
  | internal hi =>
    obtain ⟨b', he, hr'⟩ := laws.internal_simulation c d b ht hr hi
    exact ⟨laws.internal_preservation c d ht hi,
      b', hr', cert.closed b b' hu he⟩
  | resume hs hw ha hx =>
    obtain ⟨b', he, hr'⟩ := laws.resume_simulation _ _ _ _ _ _ ht hr hs hw ha hx
    exact ⟨laws.resume_formation _ _ _ _ _ ht hs hw ha hx,
      b', hr', cert.closed b b' hu he⟩

/-- No upper bound on prefix length or on the number of external resumptions. -/
theorem prefix_invariant {n : Nat} {c d : C}
    (hc : Invariant m a laws cert c) (h : Prefix (Step m) n c d) :
    Invariant m a laws cert d := by
  induction h with
  | refl => exact hc
  | snoc hp hs ih => exact step_invariant m a laws cert (ih hc) hs

structure Conclusion (c : C) : Prop where
  typed : laws.typed c
  cell : ∃ b, a.represents c b ∧ cert.contains b
  noBad : ¬ m.bad c
  progress : m.returned c ∨ m.requested c ∨ m.failed c ∨ ∃ d, m.internal c d
  outputs : ∀ o, m.exposed c o → cert.allowed o

theorem invariant_conclusion {c : C} (hc : Invariant m a laws cert c) :
    Conclusion m a laws cert c := by
  obtain ⟨ht, b, hr, hu⟩ := hc
  refine ⟨ht, ⟨b, hr, hu⟩, laws.no_bad c ht, laws.progress c ht, ?_⟩
  intro o ho
  exact cert.outputs b o hu (laws.observation c b o ht hr ho)

/-- Conditional theorem C: the local interfaces imply every finite-prefix claim. -/
theorem finite_prefix_composition {n : Nat} {c d : C}
    (hc : laws.initial c) (h : Prefix (Step m) n c d) :
    Conclusion m a laws cert d := by
  apply invariant_conclusion m a laws cert
  exact prefix_invariant m a laws cert (initial_invariant m a laws cert hc) h

/-- Every position of an arbitrary run, including runs with infinitely many resumes. -/
theorem run_at_every_time (run : Nat → C)
    (h0 : laws.initial (run 0)) (hs : ∀ n, Step m (run n) (run (n + 1))) :
    ∀ n, Conclusion m a laws cert (run n) := by
  have inv : ∀ n, Invariant m a laws cert (run n) := by
    intro n
    induction n with
    | zero => exact initial_invariant m a laws cert h0
    | succ n ih => exact step_invariant m a laws cert ih (hs n)
  intro n
  exact invariant_conclusion m a laws cert (inv n)

/-- Reuse is not consumption: k is the SAME parameter in both judgments.
The two configurations/current worlds and responses need not be equal. -/
theorem saved_reusable {c₁ c₂ d₁ d₂ : C} {k : K} {w₁ w₂ : W} {r₁ r₂ : R}
    (h₁ : Invariant m a laws cert c₁) (h₂ : Invariant m a laws cert c₂)
    (s₁ : m.suspended c₁ k) (s₂ : m.suspended c₂ k)
    (cw₁ : m.current c₁ w₁) (cw₂ : m.current c₂ w₂)
    (ar₁ : m.admissible k w₁ r₁) (ar₂ : m.admissible k w₂ r₂)
    (re₁ : m.resume k w₁ r₁ d₁) (re₂ : m.resume k w₂ r₂ d₂) :
    Invariant m a laws cert d₁ ∧ Invariant m a laws cert d₂ := by
  exact ⟨step_invariant m a laws cert h₁ (.resume s₁ cw₁ ar₁ re₁),
    step_invariant m a laws cert h₂ (.resume s₂ cw₂ ar₂ re₂)⟩

end YulangClosure

namespace YulangClosure.SourceProblem

/-- The native, inference and elaboration obligations compose with ONE source
scope and witness. None of the three obligations is discharged by this theorem.
Connecting the resulting core judgment to LocalLaws.initial is a further,
concrete initialization obligation. -/
theorem native_success_elaborates {S C X E D A N : Type}
    (p : SourceProblem S C X E D A N)
    (hnative : p.NativeCorrespondence)
    (hinfer : p.InferenceSoundness) (helab : p.Elaboration)
    {s : S} {x : X} {n : N}
    (hs : p.supported s) (hn : p.nativeSuccess s x n) :
    ∃ d a e c,
      p.generates s x d ∧ p.nativeRealizes n d a ∧ p.solves d a ∧
      p.sourceJudgment s x e ∧ p.sameScoped s x e a ∧
      p.elaborates s c ∧ p.coreJudgment c x e ∧
      p.sameObservations s c x e := by
  obtain ⟨d, a, hg, hr, hsolve⟩ := hnative s x n hn
  obtain ⟨e, hsource, hscope⟩ := hinfer s x d a hs hg hsolve
  obtain ⟨c, he, hc, ho⟩ := helab s x e hs hsource
  exact ⟨d, a, e, c, hg, hr, hsolve, hsource, hscope, he, hc, ho⟩

end YulangClosure.SourceProblem
