import Init

/-! Conditional interfaces for the original closure obligations.
No concrete Yulang judgment is defined by execution safety here. -/
namespace YulangClosure

structure Machine (Config Saved World Response Output : Type) where
  internal : Config → Config → Prop
  suspended : Config → Saved → Prop
  /-- Current world supplied by a lawful host/context, not saved in `Saved`. -/
  current : Config → World → Prop
  admissible : Saved → World → Response → Prop
  /-- The same immutable saved object can be used with different current worlds. -/
  resume : Saved → World → Response → Config → Prop
  returned : Config → Prop
  requested : Config → Prop
  failed : Config → Prop
  bad : Config → Prop
  exposed : Config → Output → Prop

inductive Step {C K W R O : Type} (m : Machine C K W R O) : C → C → Prop
  | internal {c d} : m.internal c d → Step m c d
  | resume {c d k w r} :
      m.suspended c k → m.current c w → m.admissible k w r →
      m.resume k w r d → Step m c d

/-- Length-indexed prefixes include every legal external resumption. -/
inductive Prefix {C : Type} (step : C → C → Prop) : Nat → C → C → Prop
  | refl (c) : Prefix step 0 c c
  | snoc {n a b c} : Prefix step n a b → step b c →
      Prefix step (n + 1) a c

structure Analysis (Config Cell Output : Type) where
  represents : Config → Cell → Prop
  seed : Config → Cell → Prop
  edge : Cell → Cell → Prop
  observes : Cell → Output → Prop
  /-- Finiteness is supplied independently; the composition proof needs no bound on time. -/
  cardinality : Nat
  index : Cell → Fin cardinality
  index_injective : ∀ a b, index a = index b → a = b

structure Certificate {C B O : Type} (a : Analysis C B O) where
  contains : B → Prop
  allowed : O → Prop
  seeds : ∀ c b, a.seed c b → contains b
  closed : ∀ b d, contains b → a.edge b d → contains d
  outputs : ∀ b o, contains b → a.observes b o → allowed o

/-- Local obligations, independent of the finite-prefix conclusion.
`typed` must be instantiated by the original syntax-directed judgment.
In particular it must not be defined as reachability or absence of Bad. -/
structure LocalLaws {C K W R O B : Type}
    (m : Machine C K W R O) (a : Analysis C B O) where
  Result : Type
  result : Result
  typing : Result → C → Prop
  initial : C → Prop
  initial_typing : ∀ c, initial c → typing result c
  initial_seed : ∀ c, initial c → ∃ b, a.seed c b ∧ a.represents c b
  internal_preservation : ∀ c d, typing result c → m.internal c d → typing result d
  resume_formation : ∀ c d k w r, typing result c → m.suspended c k →
    m.current c w → m.admissible k w r → m.resume k w r d → typing result d
  internal_simulation : ∀ c d b, typing result c → a.represents c b →
    m.internal c d → ∃ b', a.edge b b' ∧ a.represents d b'
  resume_simulation : ∀ c d b k w r, typing result c → a.represents c b →
    m.suspended c k → m.current c w → m.admissible k w r →
    m.resume k w r d → ∃ b', a.edge b b' ∧ a.represents d b'
  observation : ∀ c b o, typing result c → a.represents c b →
    m.exposed c o → a.observes b o
  no_bad : ∀ c, typing result c → ¬ m.bad c
  progress : ∀ c, typing result c → m.returned c ∨ m.requested c ∨ m.failed c ∨
    ∃ d, m.internal c d

/-- The result index is fixed throughout this instance, including resume. -/
def LocalLaws.typed {C K W R O B : Type}
    {m : Machine C K W R O} {a : Analysis C B O}
    (laws : LocalLaws m a) : C → Prop := laws.typing laws.result

/-- Reachability entirely inside one immutable birth-level induced graph. -/
inductive LevelPath {V : Type} (ref : V → V → Prop) (birth : V → Nat)
    (level : Nat) : V → V → Prop
  | refl {v} : birth v = level → LevelPath ref birth level v v
  | cons {u v w} : birth u = level → birth v = level → ref u v →
      LevelPath ref birth level v w → LevelPath ref birth level u w

structure ExtrusionOccurrence (Value TypeVar OccurrenceId : Type) where
  id : OccurrenceId
  origin : Value
  receiver : Value
  /-- Actual retained parent/copy pairs; polarity remains part of each entry. -/
  pairs : List (TypeVar × TypeVar × Bool)

def Qualifies {V T I : Type} (ref : V → V → Prop) (birth : V → Nat)
    (e : ExtrusionOccurrence V T I) : Prop :=
  ∃ level, LevelPath ref birth level e.origin e.receiver ∧
    LevelPath ref birth level e.receiver e.origin

/-! Uninstantiated ORIGINAL roots. These are proposition definitions, not axioms
or proved instances. Witness objects carry the entire shared lexical package.
`sameScoped` must retain rigid imports, one hidden witness, all uses and futures;
its concrete definition cannot be replaced by endpoint equality. -/
structure SourceProblem (Source Core Scope Witness Constraint Solution Native : Type) where
  /-- Supported syntax/domain; this does not assert that the program is typable. -/
  supported : Source → Prop
  sourceJudgment : Source → Scope → Witness → Prop
  coreJudgment : Core → Scope → Witness → Prop
  elaborates : Source → Core → Prop
  sameObservations : Source → Core → Scope → Witness → Prop
  generates : Source → Scope → Constraint → Prop
  solves : Constraint → Solution → Prop
  sameScoped : Source → Scope → Witness → Solution → Prop
  nativeStep : Native → Native → Prop
  nativeRealizes : Native → Constraint → Solution → Prop
  nativeSuccess : Source → Scope → Native → Prop
  inferInitial : Source → Scope → Native → Prop
  inferStep : Native → Native → Prop

namespace SourceProblem
variable {S C X E D A N : Type} (p : SourceProblem S C X E D A N)

/-- Forward elaboration preserves the SAME source scope and shared witness. -/
def Elaboration : Prop :=
  ∀ s x e, p.supported s → p.sourceJudgment s x e →
    ∃ c, p.elaborates s c ∧ p.coreJudgment c x e ∧ p.sameObservations s c x e

/-- Successful generated solutions must produce an original source derivation. -/
def InferenceSoundness : Prop :=
  ∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
    ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a

/-- Source-scoped coverage, not preservation of every arbitrary native model. -/
def SourceScopedCoverage : Prop :=
  ∀ s x e d, p.supported s → p.sourceJudgment s x e → p.generates s x d →
    ∃ a, p.solves d a ∧ p.sameScoped s x e a

/-- Principality additionally needs the original instance/ordering relation. -/
def PrincipalCoverage (principal : S → X → D → A → Prop)
    (instanceOf : X → A → A → Prop) : Prop :=
  ∀ s x d, p.supported s → p.generates s x d →
    (∃ e, p.sourceJudgment s x e) →
    ∃ a, principal s x d a ∧ p.solves d a ∧
      ∀ e, p.sourceJudgment s x e →
        ∃ b, p.solves d b ∧ p.sameScoped s x e b ∧ instanceOf x a b

/-- Native success is a separate bridge, not a consequence of a scalar model. -/
def NativeCorrespondence : Prop :=
  ∀ s x n, p.nativeSuccess s x n →
    ∃ d a, p.generates s x d ∧ p.nativeRealizes n d a ∧ p.solves d a

/-- Algorithmic termination only; it does not assert program evaluation terminates. -/
def InferenceTermination : Prop :=
  ∀ s x n, p.supported s → p.inferInitial s x n →
    Acc (fun next prev => p.inferStep prev next) n

end SourceProblem
end YulangClosure
