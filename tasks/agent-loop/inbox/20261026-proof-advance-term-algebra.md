# Paper term substitution algebra — frozen producer handoff

Status: **CHECKED AND INDEPENDENTLY REVIEWED for the stated component scope**.
Producer: primary `/root`. Independent reviewer: `/root/paper_allocation_execution`,
who did not author or edit this module. Baseline:
`adfed0dbcc8875ac0c9e66c40a0b967b3e9df073`, branch `yulang3`.
No whole-language, semantic-adoption, production or inference gate is closed.

## Original obligation, source correspondence and improvement

The operational manuscript `docs/yulang-operational-type-safety-ja.tex` states
capture-avoiding substitution and binder conventions at 952–977, fresh rec
allocation using shared replacement in RHSs/body at 324–326 and 980–990, and
saved continuation/response formation at 458–466. Corrected V1 in
`notes/theory/2026-10-24-corrected-core-value-continuation.md` retains the full
source/guard obligations. Its correction has precedence over historical
manuscript shortcuts. This work changes no source authority or semantics.

`PaperTermSubstitution` already supplied typed replacement, support and
`TermSubstitutionTyped.compose`. The new module identifies the actual nested
raw replacement with the composed vector. It derives response-after-capture,
graph-formal and typed public-API composition from these actual equations;
no algebra law or second-substitution success is assumed as a premise.

## Exact construction and retained boundary

- Renaming identity/composition and one-/N-binder lifting use the actual raw
  value/computation functions.
- Type substitution commutes with renaming and replacement, mapping both the
  original syntax and replacement values. Type abstractions use type shift;
  term, tuple and response binders use their matching term lifts.
- Replacement composes outer-after-inner, has both identities, and makes
  substitution-vector composition associative.
- Graph formal IDs and list order remain literal constants on both sides.
- `response_after_environment` gives exactly `0 ↦ response`, `k + 1 ↦ rho k`:
  captured values are not substituted twice.
- The two typed composition theorems identify the two-pass `Option.bind` API
  with one composed substitution, preserving the original result type.
  Original typing and independently typed substitutions imply the second
  support check through actual typed replacement.

Bulk proofs use strong induction on original syntax size with actual list-member
size decreases. No bound on replacement size is assumed. Existing omitted raw
constructors remain opaque. These equations do not establish source substitution
for unsupported rec, handler, operation-mapper, nominal or variant constructors.
No syntax, support predicate, typing rule or prior theorem was changed.

## Verification and retained failure evidence

Pinned toolchain: Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Direct checks use `-j1 -M1024`;
Lake uses the existing one-thread/1024 MiB configuration. The initial sandbox
could not resolve the toolchain application path; authorized native execution
reported the expected version. This runner limitation is not a proof result.

Intermediate elaboration attempts remain in task-local `term-algebra-check-01`
through `-10` logs. Repairs included attached-list map congruence, eta-explicit
lifted composition, correct fallback discriminator simplification, quoting the
reserved `variable` constructor, and unfolding irreducible variable equations.
Final `term-algebra-check-11.log` is empty and its checker exited 0. The focused
module build passed 11 jobs; the integrated default build passed 58 jobs.
No new-module warning remains. The unused-simp-argument linter is locally
suppressed on uniform constructor induction proofs; proof checking is unchanged.

The originating-module audit checked 306 theorem constants, including private
and generated helpers: 294 depend on `propext`/`Quot.sound`, 3 on `Quot.sound`
only, and 9 on no axioms. There is no `Classical.choice`, `sorryAx`, project
axiom or unchecked-evaluation axiom in these dependencies. All 58 authored
theorem types (31 public, 27 private) are retained below. The committed
`AuditProofAdvancement.lean` reproduces the inventory within the complete
538-theorem integration audit, which exited 0.

## Frozen hashes and local import closure


| Artifact | SHA-256 |
| --- | --- |
| Proof source | `b35a14e1872cec5284a68cb38e9ea6fd0c9dc23cbd6d8017c82a550ec60a379d` |
| Complete module audit log | `87c14204604cc51c97c864ef012fbe89539ad73785b8d656498114606b9faa0d` |
| Focused build log | `65e5aab98907fcac0598d37a7473f516a539955f8b6145b93f26c24faf792ac8` |
| Independent review | `f829de97f8de50093672723454f962d1dd1025dd51004f3ab3dc1193164d2386` |

The recursive local import closure has 10 source files including this module.
All prior dependencies remain byte-equal to the baseline tracked files.

| Local source | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/DeclSubst.lean` | `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258` |
| `notes/theory/lean/YulangClosure/PaperCoreStep.lean` | `6357b14217e82421eed87da981cef8e94014dcaea634d746ad0b4bb39bff6144` |
| `notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean` | `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a` |
| `notes/theory/lean/YulangClosure/PaperExecutionGraphWeakening.lean` | `313a550a550716e235e73690d238f1040838aeebd2cc0cf0b7753979ab6fe38d` |
| `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean` | `78f23b9e946b0259cdb63797ed226706112f71375a013e0b9cc8745ad5afe8b0` |
| `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean` | `fae64aa9a5c37572a3f654c403b7fb8ff7eb7adccaa4e3540fff85e61ce84819` |
| `notes/theory/lean/YulangClosure/PaperTermSubstitution.lean` | `42d7f46d992e715443a7116066b51ae1748849718f6c4e716d9169ea069059d9` |
| `notes/theory/lean/YulangClosure/PaperTermSubstitutionAlgebra.lean` | `b35a14e1872cec5284a68cb38e9ea6fd0c9dc23cbd6d8017c82a550ec60a379d` |
| `notes/theory/lean/YulangClosure/PaperTypeFormation.lean` | `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13` |
| `notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean` | `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861` |

## Review and original remaining obligations

Fresh non-author review read the full source, all 58 authored printed types,
base definitions and manuscript clauses, and independently parsed all 306
audit records. No blocking, major or minor finding remains. The reviewer did
not rerun Lean; the [receipt](20261026-proof-advance-term-algebra-review.md)
explicitly distinguishes log inspection from independent checker execution.

Full source-rec construction/order, omitted syntax coverage, guardedness,
Force/View/scope and owner/current-world semantics, progress/no-Bad,
source/native correspondence and original inference A/B remain OPEN.

## Complete authored theorem types and actual axiom reports

### `map_eq_self_iff`

```text
@_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.map_eq_self_iff : ∀
  {α : Type} (f : α → α) (xs : List α), List.map f xs = xs ↔ ∀ (x : α), x ∈ xs → f x = x
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.map_eq_self_iff' depends on axioms: [propext,
 Quot.sound]
```

### `map_attach_map_iff`

```text
@_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.map_attach_map_iff : ∀
  {α β : Type} (xs : List α) (f : { x // x ∈ xs } → β) (g : α → β),
  List.map f xs.attach = List.map g xs ↔ ∀ (x : α) (h : x ∈ xs), f ⟨x, h⟩ = g x
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.map_attach_map_iff' depends on axioms: [propext,
 Quot.sound]
```

### `rename_record`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.rename_record : ∀
  (f : Nat → Nat)
  (fields : List (YulangClosure.PaperTypes.Label × YulangClosure.PaperTypes.Presence × YulangClosure.PaperTypes.Value)),
  YulangClosure.PaperTypes.renameTermValue f (YulangClosure.PaperTypes.Value.record fields) =
    YulangClosure.PaperTypes.Value.record
      (List.map (fun x => (x.fst, x.snd.fst, YulangClosure.PaperTypes.renameTermValue f x.snd.snd)) fields)
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.rename_record' depends on axioms: [propext,
 Quot.sound]
```

### `liftRenaming_id`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.liftRenaming_id : YulangClosure.PaperTypes.liftTermRenaming id = id
'YulangClosure.PaperTypes.PaperTermAlgebra.liftRenaming_id' depends on axioms: [Quot.sound]
```

### `liftRenamingN_id`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.liftRenamingN_id : ∀ (n : Nat),
  YulangClosure.PaperTypes.liftTermRenamingN n id = id
'YulangClosure.PaperTypes.PaperTermAlgebra.liftRenamingN_id' depends on axioms: [propext, Quot.sound]
```

### `liftRenaming_comp`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.liftRenaming_comp : ∀ (f g : Nat → Nat),
  YulangClosure.PaperTypes.liftTermRenaming (f ∘ g) =
    YulangClosure.PaperTypes.liftTermRenaming f ∘ YulangClosure.PaperTypes.liftTermRenaming g
'YulangClosure.PaperTypes.PaperTermAlgebra.liftRenaming_comp' depends on axioms: [Quot.sound]
```

### `liftRenamingN_comp`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.liftRenamingN_comp : ∀ (n : Nat) (f g : Nat → Nat),
  YulangClosure.PaperTypes.liftTermRenamingN n (f ∘ g) =
    YulangClosure.PaperTypes.liftTermRenamingN n f ∘ YulangClosure.PaperTypes.liftTermRenamingN n g
'YulangClosure.PaperTypes.PaperTermAlgebra.liftRenamingN_comp' depends on axioms: [propext, Quot.sound]
```

### `lift_comp_eta`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.lift_comp_eta : ∀
  (f g : Nat → Nat),
  (fun x => YulangClosure.PaperTypes.liftTermRenaming f (YulangClosure.PaperTypes.liftTermRenaming g x)) =
    YulangClosure.PaperTypes.liftTermRenaming fun x => f (g x)
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.lift_comp_eta' depends on axioms: [Quot.sound]
```

### `liftN_comp_eta`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.liftN_comp_eta : ∀
  (n : Nat) (f g : Nat → Nat),
  (fun x => YulangClosure.PaperTypes.liftTermRenamingN n f (YulangClosure.PaperTypes.liftTermRenamingN n g x)) =
    YulangClosure.PaperTypes.liftTermRenamingN n fun x => f (g x)
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.liftN_comp_eta' depends on axioms: [propext,
 Quot.sound]
```

### `renameAt_all`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.renameAt_all : ∀
  (n : Nat), _private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.RenameAt n
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.renameAt_all' depends on axioms: [propext,
 Quot.sound]
```

### `renameValue_comp`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.renameValue_comp : ∀ (f g : Nat → Nat) (v : YulangClosure.PaperTypes.Value),
  YulangClosure.PaperTypes.renameTermValue f (YulangClosure.PaperTypes.renameTermValue g v) =
    YulangClosure.PaperTypes.renameTermValue (f ∘ g) v
'YulangClosure.PaperTypes.PaperTermAlgebra.renameValue_comp' depends on axioms: [propext, Quot.sound]
```

### `renameComputation_comp`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.renameComputation_comp : ∀ (f g : Nat → Nat)
  (c : YulangClosure.PaperTypes.Computation),
  YulangClosure.PaperTypes.renameTermComputation f (YulangClosure.PaperTypes.renameTermComputation g c) =
    YulangClosure.PaperTypes.renameTermComputation (f ∘ g) c
'YulangClosure.PaperTypes.PaperTermAlgebra.renameComputation_comp' depends on axioms: [propext, Quot.sound]
```

### `identityAt_all`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.identityAt_all : ∀
  (n : Nat),
  _private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.IdentityAt n
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.identityAt_all' depends on axioms: [propext,
 Quot.sound]
```

### `renameValue_id`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.renameValue_id : ∀ (v : YulangClosure.PaperTypes.Value),
  YulangClosure.PaperTypes.renameTermValue id v = v
'YulangClosure.PaperTypes.PaperTermAlgebra.renameValue_id' depends on axioms: [propext, Quot.sound]
```

### `renameComputation_id`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.renameComputation_id : ∀ (c : YulangClosure.PaperTypes.Computation),
  YulangClosure.PaperTypes.renameTermComputation id c = c
'YulangClosure.PaperTypes.PaperTermAlgebra.renameComputation_id' depends on axioms: [propext, Quot.sound]
```

### `map_record`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.map_record : ∀
  (σ : Nat → YulangClosure.PaperTypes.Ty)
  (fields : List (YulangClosure.PaperTypes.Label × YulangClosure.PaperTypes.Presence × YulangClosure.PaperTypes.Value)),
  YulangClosure.PaperTypes.mapPaperValue σ (YulangClosure.PaperTypes.Value.record fields) =
    YulangClosure.PaperTypes.Value.record
      (List.map (fun x => (x.fst, x.snd.fst, YulangClosure.PaperTypes.mapPaperValue σ x.snd.snd)) fields)
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.map_record' depends on axioms: [propext,
 Quot.sound]
```

### `typeRenameAt_all`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.typeRenameAt_all : ∀
  (n : Nat),
  _private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.TypeRenameAt n
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.typeRenameAt_all' depends on axioms: [propext,
 Quot.sound]
```

### `mapType_renameValue`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.mapType_renameValue : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  (f : Nat → Nat) (v : YulangClosure.PaperTypes.Value),
  YulangClosure.PaperTypes.mapPaperValue σ (YulangClosure.PaperTypes.renameTermValue f v) =
    YulangClosure.PaperTypes.renameTermValue f (YulangClosure.PaperTypes.mapPaperValue σ v)
'YulangClosure.PaperTypes.PaperTermAlgebra.mapType_renameValue' depends on axioms: [propext, Quot.sound]
```

### `mapType_renameComputation`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.mapType_renameComputation : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  (f : Nat → Nat) (c : YulangClosure.PaperTypes.Computation),
  YulangClosure.PaperTypes.mapPaperComputation σ (YulangClosure.PaperTypes.renameTermComputation f c) =
    YulangClosure.PaperTypes.renameTermComputation f (YulangClosure.PaperTypes.mapPaperComputation σ c)
'YulangClosure.PaperTypes.PaperTermAlgebra.mapType_renameComputation' depends on axioms: [propext, Quot.sound]
```

### `replace_record`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.replace_record : ∀
  (rho : Nat → YulangClosure.PaperTypes.Value)
  (fields : List (YulangClosure.PaperTypes.Label × YulangClosure.PaperTypes.Presence × YulangClosure.PaperTypes.Value)),
  YulangClosure.PaperTypes.replaceTermValue rho (YulangClosure.PaperTypes.Value.record fields) =
    YulangClosure.PaperTypes.Value.record
      (List.map (fun x => (x.fst, x.snd.fst, YulangClosure.PaperTypes.replaceTermValue rho x.snd.snd)) fields)
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.replace_record' depends on axioms: [propext,
 Quot.sound]
```

### `precompose_lift`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.precompose_lift : ∀
  (rho : Nat → YulangClosure.PaperTypes.Value) (f : Nat → Nat),
  (fun n => YulangClosure.PaperTypes.liftTermSubstitution rho (YulangClosure.PaperTypes.liftTermRenaming f n)) =
    YulangClosure.PaperTypes.liftTermSubstitution fun n => rho (f n)
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.precompose_lift' depends on axioms: [propext,
 Quot.sound]
```

### `precompose_liftN`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.precompose_liftN : ∀
  (k : Nat) (rho : Nat → YulangClosure.PaperTypes.Value) (f : Nat → Nat),
  (fun n => YulangClosure.PaperTypes.liftTermSubstitutionN k rho (YulangClosure.PaperTypes.liftTermRenamingN k f n)) =
    YulangClosure.PaperTypes.liftTermSubstitutionN k fun n => rho (f n)
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.precompose_liftN' depends on axioms: [propext,
 Quot.sound]
```

### `precompose_shift`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.precompose_shift : ∀
  (rho : Nat → YulangClosure.PaperTypes.Value) (f : Nat → Nat),
  (fun n => YulangClosure.PaperTypes.shiftTermSubstitution rho (f n)) =
    YulangClosure.PaperTypes.shiftTermSubstitution fun n => rho (f n)
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.precompose_shift' depends on axioms: [propext,
 Quot.sound]
```

### `replaceRenameAt_all`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.replaceRenameAt_all : ∀
  (n : Nat),
  _private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.ReplaceRenameAt n
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.replaceRenameAt_all' depends on axioms: [propext,
 Quot.sound]
```

### `replace_renameValue`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.replace_renameValue : ∀ (rho : Nat → YulangClosure.PaperTypes.Value)
  (f : Nat → Nat) (v : YulangClosure.PaperTypes.Value),
  YulangClosure.PaperTypes.replaceTermValue rho (YulangClosure.PaperTypes.renameTermValue f v) =
    YulangClosure.PaperTypes.replaceTermValue (fun n => rho (f n)) v
'YulangClosure.PaperTypes.PaperTermAlgebra.replace_renameValue' depends on axioms: [propext, Quot.sound]
```

### `replace_renameComputation`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.replace_renameComputation : ∀ (rho : Nat → YulangClosure.PaperTypes.Value)
  (f : Nat → Nat) (c : YulangClosure.PaperTypes.Computation),
  YulangClosure.PaperTypes.replaceTermComputation rho (YulangClosure.PaperTypes.renameTermComputation f c) =
    YulangClosure.PaperTypes.replaceTermComputation (fun n => rho (f n)) c
'YulangClosure.PaperTypes.PaperTermAlgebra.replace_renameComputation' depends on axioms: [propext, Quot.sound]
```

### `rename_lift`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.rename_lift : ∀
  (rho : Nat → YulangClosure.PaperTypes.Value) (f : Nat → Nat),
  (fun n =>
      YulangClosure.PaperTypes.renameTermValue (YulangClosure.PaperTypes.liftTermRenaming f)
        (YulangClosure.PaperTypes.liftTermSubstitution rho n)) =
    YulangClosure.PaperTypes.liftTermSubstitution fun n => YulangClosure.PaperTypes.renameTermValue f (rho n)
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.rename_lift' depends on axioms: [propext,
 Quot.sound]
```

### `rename_liftN`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.rename_liftN : ∀
  (k : Nat) (rho : Nat → YulangClosure.PaperTypes.Value) (f : Nat → Nat),
  (fun n =>
      YulangClosure.PaperTypes.renameTermValue (YulangClosure.PaperTypes.liftTermRenamingN k f)
        (YulangClosure.PaperTypes.liftTermSubstitutionN k rho n)) =
    YulangClosure.PaperTypes.liftTermSubstitutionN k fun n => YulangClosure.PaperTypes.renameTermValue f (rho n)
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.rename_liftN' depends on axioms: [propext,
 Quot.sound]
```

### `rename_shift`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.rename_shift : ∀
  (rho : Nat → YulangClosure.PaperTypes.Value) (f : Nat → Nat),
  (fun n => YulangClosure.PaperTypes.renameTermValue f (YulangClosure.PaperTypes.shiftTermSubstitution rho n)) =
    YulangClosure.PaperTypes.shiftTermSubstitution fun n => YulangClosure.PaperTypes.renameTermValue f (rho n)
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.rename_shift' depends on axioms: [propext,
 Quot.sound]
```

### `renameReplaceAt_all`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.renameReplaceAt_all : ∀
  (n : Nat),
  _private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.RenameReplaceAt n
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.renameReplaceAt_all' depends on axioms: [propext,
 Quot.sound]
```

### `rename_replaceValue`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.rename_replaceValue : ∀ (f : Nat → Nat)
  (rho : Nat → YulangClosure.PaperTypes.Value) (v : YulangClosure.PaperTypes.Value),
  YulangClosure.PaperTypes.renameTermValue f (YulangClosure.PaperTypes.replaceTermValue rho v) =
    YulangClosure.PaperTypes.replaceTermValue (fun n => YulangClosure.PaperTypes.renameTermValue f (rho n)) v
'YulangClosure.PaperTypes.PaperTermAlgebra.rename_replaceValue' depends on axioms: [propext, Quot.sound]
```

### `rename_replaceComputation`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.rename_replaceComputation : ∀ (f : Nat → Nat)
  (rho : Nat → YulangClosure.PaperTypes.Value) (c : YulangClosure.PaperTypes.Computation),
  YulangClosure.PaperTypes.renameTermComputation f (YulangClosure.PaperTypes.replaceTermComputation rho c) =
    YulangClosure.PaperTypes.replaceTermComputation (fun n => YulangClosure.PaperTypes.renameTermValue f (rho n)) c
'YulangClosure.PaperTypes.PaperTermAlgebra.rename_replaceComputation' depends on axioms: [propext, Quot.sound]
```

### `mapType_lift`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.mapType_lift : ∀
  (σ : Nat → YulangClosure.PaperTypes.Ty) (rho : Nat → YulangClosure.PaperTypes.Value),
  (fun n => YulangClosure.PaperTypes.mapPaperValue σ (YulangClosure.PaperTypes.liftTermSubstitution rho n)) =
    YulangClosure.PaperTypes.liftTermSubstitution fun n => YulangClosure.PaperTypes.mapPaperValue σ (rho n)
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.mapType_lift' depends on axioms: [propext,
 Quot.sound]
```

### `mapType_liftN`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.mapType_liftN : ∀
  (k : Nat) (σ : Nat → YulangClosure.PaperTypes.Ty) (rho : Nat → YulangClosure.PaperTypes.Value),
  (fun n => YulangClosure.PaperTypes.mapPaperValue σ (YulangClosure.PaperTypes.liftTermSubstitutionN k rho n)) =
    YulangClosure.PaperTypes.liftTermSubstitutionN k fun n => YulangClosure.PaperTypes.mapPaperValue σ (rho n)
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.mapType_liftN' depends on axioms: [propext,
 Quot.sound]
```

### `mapType_shift`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.mapType_shift : ∀
  (σ : Nat → YulangClosure.PaperTypes.Ty) (rho : Nat → YulangClosure.PaperTypes.Value),
  (fun n =>
      YulangClosure.PaperTypes.mapPaperValue (YulangClosure.PaperTypes.liftSub σ)
        (YulangClosure.PaperTypes.shiftTermSubstitution rho n)) =
    YulangClosure.PaperTypes.shiftTermSubstitution fun n => YulangClosure.PaperTypes.mapPaperValue σ (rho n)
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.mapType_shift' depends on axioms: [propext,
 Quot.sound]
```

### `typeReplaceAt_all`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.typeReplaceAt_all : ∀
  (n : Nat),
  _private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.TypeReplaceAt n
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.typeReplaceAt_all' depends on axioms: [propext,
 Quot.sound]
```

### `mapType_replaceValue`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.mapType_replaceValue : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  (rho : Nat → YulangClosure.PaperTypes.Value) (v : YulangClosure.PaperTypes.Value),
  YulangClosure.PaperTypes.mapPaperValue σ (YulangClosure.PaperTypes.replaceTermValue rho v) =
    YulangClosure.PaperTypes.replaceTermValue (fun n => YulangClosure.PaperTypes.mapPaperValue σ (rho n))
      (YulangClosure.PaperTypes.mapPaperValue σ v)
'YulangClosure.PaperTypes.PaperTermAlgebra.mapType_replaceValue' depends on axioms: [propext, Quot.sound]
```

### `mapType_replaceComputation`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.mapType_replaceComputation : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  (rho : Nat → YulangClosure.PaperTypes.Value) (c : YulangClosure.PaperTypes.Computation),
  YulangClosure.PaperTypes.mapPaperComputation σ (YulangClosure.PaperTypes.replaceTermComputation rho c) =
    YulangClosure.PaperTypes.replaceTermComputation (fun n => YulangClosure.PaperTypes.mapPaperValue σ (rho n))
      (YulangClosure.PaperTypes.mapPaperComputation σ c)
'YulangClosure.PaperTypes.PaperTermAlgebra.mapType_replaceComputation' depends on axioms: [propext, Quot.sound]
```

### `compose_lift`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.compose_lift : ∀ (outer inner : Nat → YulangClosure.PaperTypes.Value),
  YulangClosure.PaperTypes.composeTermSubstitution (YulangClosure.PaperTypes.liftTermSubstitution outer)
      (YulangClosure.PaperTypes.liftTermSubstitution inner) =
    YulangClosure.PaperTypes.liftTermSubstitution (YulangClosure.PaperTypes.composeTermSubstitution outer inner)
'YulangClosure.PaperTypes.PaperTermAlgebra.compose_lift' depends on axioms: [propext, Quot.sound]
```

### `compose_liftN`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.compose_liftN : ∀ (k : Nat)
  (outer inner : Nat → YulangClosure.PaperTypes.Value),
  YulangClosure.PaperTypes.composeTermSubstitution (YulangClosure.PaperTypes.liftTermSubstitutionN k outer)
      (YulangClosure.PaperTypes.liftTermSubstitutionN k inner) =
    YulangClosure.PaperTypes.liftTermSubstitutionN k (YulangClosure.PaperTypes.composeTermSubstitution outer inner)
'YulangClosure.PaperTypes.PaperTermAlgebra.compose_liftN' depends on axioms: [propext, Quot.sound]
```

### `compose_shift`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.compose_shift : ∀ (outer inner : Nat → YulangClosure.PaperTypes.Value),
  YulangClosure.PaperTypes.composeTermSubstitution (YulangClosure.PaperTypes.shiftTermSubstitution outer)
      (YulangClosure.PaperTypes.shiftTermSubstitution inner) =
    YulangClosure.PaperTypes.shiftTermSubstitution (YulangClosure.PaperTypes.composeTermSubstitution outer inner)
'YulangClosure.PaperTypes.PaperTermAlgebra.compose_shift' depends on axioms: [propext, Quot.sound]
```

### `compositionAt_all`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.compositionAt_all : ∀
  (n : Nat),
  _private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.CompositionAt n
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.compositionAt_all' depends on axioms: [propext,
 Quot.sound]
```

### `replaceValue_comp`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.replaceValue_comp : ∀ (outer inner : Nat → YulangClosure.PaperTypes.Value)
  (v : YulangClosure.PaperTypes.Value),
  YulangClosure.PaperTypes.replaceTermValue outer (YulangClosure.PaperTypes.replaceTermValue inner v) =
    YulangClosure.PaperTypes.replaceTermValue (YulangClosure.PaperTypes.composeTermSubstitution outer inner) v
'YulangClosure.PaperTypes.PaperTermAlgebra.replaceValue_comp' depends on axioms: [propext, Quot.sound]
```

### `replaceComputation_comp`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.replaceComputation_comp : ∀
  (outer inner : Nat → YulangClosure.PaperTypes.Value) (c : YulangClosure.PaperTypes.Computation),
  YulangClosure.PaperTypes.replaceTermComputation outer (YulangClosure.PaperTypes.replaceTermComputation inner c) =
    YulangClosure.PaperTypes.replaceTermComputation (YulangClosure.PaperTypes.composeTermSubstitution outer inner) c
'YulangClosure.PaperTypes.PaperTermAlgebra.replaceComputation_comp' depends on axioms: [propext, Quot.sound]
```

### `lift_variables`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.lift_variables : YulangClosure.PaperTypes.liftTermSubstitution
    YulangClosure.PaperTypes.Value.variable =
  YulangClosure.PaperTypes.Value.variable
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.lift_variables' depends on axioms: [propext,
 Quot.sound]
```

### `liftN_variables`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.liftN_variables : ∀
  (k : Nat),
  YulangClosure.PaperTypes.liftTermSubstitutionN k YulangClosure.PaperTypes.Value.variable =
    YulangClosure.PaperTypes.Value.variable
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.liftN_variables' depends on axioms: [propext,
 Quot.sound]
```

### `shift_variables`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.shift_variables : YulangClosure.PaperTypes.shiftTermSubstitution
    YulangClosure.PaperTypes.Value.variable =
  YulangClosure.PaperTypes.Value.variable
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.shift_variables' depends on axioms: [propext,
 Quot.sound]
```

### `replaceIdentityAt_all`

```text
_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.replaceIdentityAt_all : ∀
  (n : Nat),
  _private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.ReplaceIdentityAt n
'_private.YulangClosure.PaperTermSubstitutionAlgebra.0.YulangClosure.PaperTypes.PaperTermAlgebra.replaceIdentityAt_all' depends on axioms: [propext,
 Quot.sound]
```

### `replaceValue_id`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.replaceValue_id : ∀ (v : YulangClosure.PaperTypes.Value),
  YulangClosure.PaperTypes.replaceTermValue YulangClosure.PaperTypes.Value.variable v = v
'YulangClosure.PaperTypes.PaperTermAlgebra.replaceValue_id' depends on axioms: [propext, Quot.sound]
```

### `replaceComputation_id`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.replaceComputation_id : ∀ (c : YulangClosure.PaperTypes.Computation),
  YulangClosure.PaperTypes.replaceTermComputation YulangClosure.PaperTypes.Value.variable c = c
'YulangClosure.PaperTypes.PaperTermAlgebra.replaceComputation_id' depends on axioms: [propext, Quot.sound]
```

### `compose_associative`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.compose_associative : ∀
  (outer middle inner : Nat → YulangClosure.PaperTypes.Value),
  YulangClosure.PaperTypes.composeTermSubstitution outer
      (YulangClosure.PaperTypes.composeTermSubstitution middle inner) =
    YulangClosure.PaperTypes.composeTermSubstitution (YulangClosure.PaperTypes.composeTermSubstitution outer middle)
      inner
'YulangClosure.PaperTypes.PaperTermAlgebra.compose_associative' depends on axioms: [propext, Quot.sound]
```

### `compose_identity_left`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.compose_identity_left : ∀ (rho : Nat → YulangClosure.PaperTypes.Value),
  YulangClosure.PaperTypes.composeTermSubstitution YulangClosure.PaperTypes.Value.variable rho = rho
'YulangClosure.PaperTypes.PaperTermAlgebra.compose_identity_left' depends on axioms: [propext, Quot.sound]
```

### `compose_identity_right`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.compose_identity_right : ∀ (rho : Nat → YulangClosure.PaperTypes.Value),
  YulangClosure.PaperTypes.composeTermSubstitution rho YulangClosure.PaperTypes.Value.variable = rho
'YulangClosure.PaperTypes.PaperTermAlgebra.compose_identity_right' depends on axioms: [propext, Quot.sound]
```

### `compose_graphFormals`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.compose_graphFormals : ∀ (formals : List (Nat × YulangClosure.PaperTypes.Ty))
  (outer inner : Nat → YulangClosure.PaperTypes.Value),
  YulangClosure.PaperTypes.composeTermSubstitution outer
      (YulangClosure.PaperTypes.graphFormalReplacements formals inner) =
    YulangClosure.PaperTypes.graphFormalReplacements formals
      (YulangClosure.PaperTypes.composeTermSubstitution outer inner)
'YulangClosure.PaperTypes.PaperTermAlgebra.compose_graphFormals' depends on axioms: [propext, Quot.sound]
```

### `graphFormals_computation`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.graphFormals_computation : ∀
  (formals : List (Nat × YulangClosure.PaperTypes.Ty)) (outer inner : Nat → YulangClosure.PaperTypes.Value)
  (body : YulangClosure.PaperTypes.Computation),
  YulangClosure.PaperTypes.replaceTermComputation outer
      (YulangClosure.PaperTypes.replaceTermComputation (YulangClosure.PaperTypes.graphFormalReplacements formals inner)
        body) =
    YulangClosure.PaperTypes.replaceTermComputation
      (YulangClosure.PaperTypes.graphFormalReplacements formals
        (YulangClosure.PaperTypes.composeTermSubstitution outer inner))
      body
'YulangClosure.PaperTypes.PaperTermAlgebra.graphFormals_computation' depends on axioms: [propext, Quot.sound]
```

### `response_after_environment`

```text
YulangClosure.PaperTypes.PaperTermAlgebra.response_after_environment : ∀ (rho : Nat → YulangClosure.PaperTypes.Value)
  (response : YulangClosure.PaperTypes.Value) (body : YulangClosure.PaperTypes.Computation),
  YulangClosure.PaperTypes.replaceTermComputation (YulangClosure.PaperTypes.PaperCoreStep.singleReplacement response)
      (YulangClosure.PaperTypes.replaceTermComputation (YulangClosure.PaperTypes.liftTermSubstitution rho) body) =
    YulangClosure.PaperTypes.replaceTermComputation
      (fun n =>
        match n with
        | 0 => response
        | k.succ => rho k)
      body
'YulangClosure.PaperTypes.PaperTermAlgebra.response_after_environment' depends on axioms: [propext, Quot.sound]
```

### `typed_value_composition`

```text
@YulangClosure.PaperTypes.PaperTermAlgebra.typed_value_composition : ∀ {d : YulangClosure.PaperTypes.DeclarationTable}
  {g : YulangClosure.PaperTypes.GraphEnvironment} {source middle target : YulangClosure.PaperTypes.TypeEnvironment}
  {v : YulangClosure.PaperTypes.Value} {a : YulangClosure.PaperTypes.Ty}
  {inner outer : Nat → YulangClosure.PaperTypes.Value},
  YulangClosure.PaperTypes.PaperValueTyped d g source v a →
    YulangClosure.PaperTypes.TermSubstitutionTyped d g source middle inner →
      YulangClosure.PaperTypes.TermSubstitutionTyped d g middle target outer →
        (YulangClosure.PaperTypes.termSubstituteValue inner v).bind
              (YulangClosure.PaperTypes.termSubstituteValue outer) =
            YulangClosure.PaperTypes.termSubstituteValue (YulangClosure.PaperTypes.composeTermSubstitution outer inner)
              v ∧
          YulangClosure.PaperTypes.PaperValueTyped d g target
            (YulangClosure.PaperTypes.replaceTermValue (YulangClosure.PaperTypes.composeTermSubstitution outer inner) v)
            a
'YulangClosure.PaperTypes.PaperTermAlgebra.typed_value_composition' depends on axioms: [propext, Quot.sound]
```

### `typed_computation_composition`

```text
@YulangClosure.PaperTypes.PaperTermAlgebra.typed_computation_composition : ∀
  {d : YulangClosure.PaperTypes.DeclarationTable} {g : YulangClosure.PaperTypes.GraphEnvironment}
  {source middle target : YulangClosure.PaperTypes.TypeEnvironment} {c : YulangClosure.PaperTypes.Computation}
  {a : YulangClosure.PaperTypes.Ty} {inner outer : Nat → YulangClosure.PaperTypes.Value},
  YulangClosure.PaperTypes.PaperComputationTyped d g source c a →
    YulangClosure.PaperTypes.TermSubstitutionTyped d g source middle inner →
      YulangClosure.PaperTypes.TermSubstitutionTyped d g middle target outer →
        (YulangClosure.PaperTypes.termSubstituteComputation inner c).bind
              (YulangClosure.PaperTypes.termSubstituteComputation outer) =
            YulangClosure.PaperTypes.termSubstituteComputation
              (YulangClosure.PaperTypes.composeTermSubstitution outer inner) c ∧
          YulangClosure.PaperTypes.PaperComputationTyped d g target
            (YulangClosure.PaperTypes.replaceTermComputation
              (YulangClosure.PaperTypes.composeTermSubstitution outer inner) c)
            a
'YulangClosure.PaperTypes.PaperTermAlgebra.typed_computation_composition' depends on axioms: [propext, Quot.sound]
```
