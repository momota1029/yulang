import Yulang.GeneralDeclarativeWitnessNominalRelation359
import Yulang.GeneralDeclarativeWitnessModeCoverage357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessNominalExact359
open GeneralDeclarativeWitnessNominalSource359 (Route SlotRead lower argumentSlot AtSource)
open GeneralDeclarativeWitnessNominalRelation359 (SourceUse Reads lower_sound)
open GeneralDeclarativeWitnessConstructorModes357 (Environment SourceMode Use Mode readUse)
open GeneralDeclarativeWitnessSparseIntervals357 (names Legal hasLicense visited visitedList)
open GeneralDeclarativeWitnessModeCoverage357 (readUse_exact)
open CommonDeclaredNominalInspection (Registry Parameter)
open CommonRecursiveNominalIntervals (Endpoint childContext effectiveParameter)

theorem authored_mode_unique {e : Environment} {name a b}
    (first : SourceMode e name a) (second : SourceMode e name b) : a = b := by
  cases first with
  | primitive fa absent =>
    cases second with
    | primitive sa _ => exact congrArg Mode.primitive (Option.some.inj (fa.symm.trans sa))
    | invariant inv _ =>
      have none : GeneralSourceMetadataRows291.primitives e.source.snapshot name = none :=
        GeneralSourceMetadataRows291.exclusive e.source.snapshot.rows name inv
      rw [none] at fa
      cases fa
    | declared present _ _ => rw [absent] at present; cases present
  | invariant inv absent =>
    cases second with
    | primitive prim _ =>
      have none : GeneralSourceMetadataRows291.primitives e.source.snapshot name = none :=
        GeneralSourceMetadataRows291.exclusive e.source.snapshot.rows name inv
      rw [none] at prim
      cases prim
    | invariant _ _ => rfl
    | declared present _ _ => rw [absent] at present; cases present
  | declared fa p i =>
    cases second with
    | primitive active _ => rw [p] at active; cases active
    | invariant active _ => rw [i] at active; cases active
    | declared sa _ _ => exact congrArg Mode.declared (Option.some.inj (fa.symm.trans sa))

theorem use_finite {e : Environment} {key arity} {table : Registry} {params}
    (where_ : SourceUse e table key arity params) :
    ∃ actual : Use e key arity,readUse e key arity = some actual ∧ names actual.mode arity = some params := by
  obtain ⟨known,layout⟩ := where_.native
  have yes := readUse_exact.mpr ⟨known⟩
  cases loaded : readUse e key arity with
  | none => rw [loaded] at yes; cases yes
  | some actual =>
    exact ⟨actual,rfl, (authored_mode_unique known.sourced actual.sourced) ▸ layout⟩

theorem read_compile {e table slots inherited route endpoint}
    (read : Reads e table slots inherited route endpoint) :
    lower e table slots inherited route = some endpoint := by
  induction read with
  | point loaded => simp [lower,loaded]
  | const usage =>
    obtain ⟨u,loaded,modes⟩ := use_finite usage
    simp [lower,loaded,modes,usage.current]
  | atValue usage kind loaded mode =>
    obtain ⟨u,ctor,modes⟩ := use_finite usage
    simp [lower,ctor,modes,kind,usage.current,loaded,argumentSlot,mode]
  | atInterval usage kind loaded mode =>
    obtain ⟨u,ctor,modes⟩ := use_finite usage
    simp [lower,ctor,modes,kind,usage.current,loaded,argumentSlot,mode]
  | nested usage kind notBinder downstream ih =>
    obtain ⟨u,ctor,modes⟩ := use_finite usage
    rename_i inherited key other endpoint p
    cases other with
    | bind b => exact False.elim (notBinder b rfl)
    | nullary k =>
      rw [lower]
      simp [bind,Option.bind,pure,ctor,modes,kind,usage.current,ih]
    | unary k inner =>
      rw [lower]
      simp [bind,Option.bind,pure,ctor,modes,kind,usage.current,ih]

theorem lower_exact {e table slots inherited route endpoint} :
    lower e table slots inherited route = some endpoint ↔ Reads e table slots inherited route endpoint :=
  ⟨lower_sound,read_compile⟩

theorem trigger {e : Environment} {table : Registry} {key arity params}
    (usage : SourceUse e table key arity params) : hasLicense e table (key,arity) = true := by
  obtain ⟨actual,loaded,modes⟩ := use_finite usage
  simp [hasLicense,loaded,modes,usage.current]

theorem every_nested_source {e table slots context route endpoint}
    (read : Reads e table slots context route endpoint) :
    ∀ site ∈ visited endpoint,hasLicense e table site = true := by
  induction read with
  | point _ => simp [visited]
  | const usage =>
    intro site there
    simp [visited,visitedList] at there
    subst site
    exact trigger usage
  | atValue usage _ _ _ =>
    intro site there
    simp [visited,visitedList] at there
    subst site
    exact trigger usage
  | atInterval usage _ _ _ =>
    intro site there
    simp [visited,visitedList] at there
    subst site
    exact trigger usage
  | nested usage _ _ _ inner =>
    intro site there
    simp only [visited,visitedList,List.length_cons,List.length_nil,Nat.zero_add,
      List.append_nil,List.mem_cons] at there
    exact there.elim (fun h => h ▸ trigger usage) (inner site)

end Yulang.GeneralDeclarativeWitnessNominalExact359
