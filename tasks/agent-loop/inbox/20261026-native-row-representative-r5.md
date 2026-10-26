# Native row representative construction — r5 handoff

Author: current primary `/root`. This author does not independently accept its own proof.

## Result and unchanged parent

The exact native root-link, birth and saved-old-parent compression operations construct the representative maps needed by `NativeReplayCurrent.currentPair_absorb` and `operand_transport`. `generated_transport` applies the derived absorption equation to the original consumer; map idempotence and absorption are not assumed invariant fields. Full `SourceProblem.InferenceSoundness`, committed native-history authentication, original Call/context/world meanings, principality and whole-solver termination remain OPEN.

The explanatory note is `notes/theory/2026-10-26-native-row-representative-r5.md`. Scope, actual source owner crosswalk, construction, limits and mathematical argument are fixed there. No Rust/configuration/root-import/shared-scheduler write occurred. All production semantics and the supported source domain are unchanged.

## Frozen files and direct inputs

| Path | SHA256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeRowRepresentative.lean` | `91b29ddd33db8b8b67308dff14b655619763d5ecb153b715f03b02c031371ee2` |
| `notes/theory/2026-10-26-native-row-representative-r5.md` | `974c05ab78c6133fedb033c8ba73a85382b3bb7043b1e3693aa36dd2add6039a` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `notes/theory/lean/YulangClosure/NativeReplayCurrent.lean` | `fdd7dfa32f944f09b2cfc7440caeff95edcfad1fd5c839094f186d27168d9088` |
| `notes/theory/lean/YulangClosure/NativeMergeExpansion.lean` | `f14bd35e8f7a6b9f326dadf003797c63f4a48fd0d0c0c9d68891c579560baf6e` |
| `notes/theory/lean/YulangClosure/NativeReplayCoverage.lean` | `e65d925ab5222fd6bbc4bf63e756701aaba1273fff677ceb052d7f66e6450b7e` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `cab85ff9a8a7dc5103fe932739dcea0dfc02e6420b1277565449882c802473bd` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |

## Actual verification and resource accounting

Task-local official Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake 5.0.0-src+eb6cafb. Isolated project `/workspace/scratch/c10e953a5453/representative-r5/project`; all scratch under `representative-r5/` outside the repository. Each check has one Lean thread, `-M1024`, and a 120-second total deadline. Ten of 24 initial focused calls used. No deadline or memory limit exceeded.

- Check 01: ordinary errors (reserved `from` binder; a missing reduced write equality). Exit 1, retained.
- Check 02: accidentally invoked Lake from repository root instead of the isolated project; no lakefile there. Exit 1, retained; no proof conclusion.
- Check 03: rank inequality and unused simp argument repair. Exit 1, retained.
- Check 04: first local certificate passes; one deprecated lemma warning subsequently removed.
- Check 05: unknown two-argument congruence helper in vector bridge. Exit 1, retained.
- Check 06: reserved `prefix` binder, constructor case names and vector projection reduction repairs. Exit 1, retained.
- Check 07: redundant solved-goal tactic and dependent nil case name. Exit 1, retained.
- Check 08: exact final module build, exit 0, no warnings.
- Check 09: bundled `check_lean.py` runs pinned versions, focused build and all 26 authored theorem audits. Exit 0, all named roots proved under printed premises; no non-theorem mistaken for a theorem.
- Check 10: all-origin declaration census, exit 0; 180 balanced unique complete blocks, 98 theorem constants. Counts and hashes are in `audit-summary.json`; allowed axiom union is exactly `propext`, `Classical.choice`, `Quot.sound`.

The named audit command is recorded as an argument vector in `audit-command.json`, not reconstructed shell quoting. The census source is `project/AuditNativeRowRepresentative.lean`. The complete log is `check10-origin-census.log`, SHA256 `b728cb9a812fbc34220d13ad4feb6e4cf5ffd49206c7d1d638787654bc48cf43`. The parser verifies complete ordered BEGIN/END identity, EOF count and every axiom list. All material failed logs remain preserved.

## Frozen authored theorem types and complete axiom outputs

### YulangClosure.NativeRowRepresentative.find_correct

```lean
@YulangClosure.NativeRowRepresentative.find_correct : ∀ {f : YulangClosure.NativeRowRepresentative.Forest}
  (c : YulangClosure.NativeRowRepresentative.Certificate f) (fuel row : Nat),
  c.rank row < fuel →
    YulangClosure.NativeRowRepresentative.find f fuel row = Option.some (c.root row) ∧
      f.parent (c.root row) = c.root row ∧ c.rank (c.root row) ≤ c.rank row
'YulangClosure.NativeRowRepresentative.find_correct' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeRowRepresentative.root_fixed

```lean
@YulangClosure.NativeRowRepresentative.root_fixed : ∀ {f : YulangClosure.NativeRowRepresentative.Forest}
  (c : YulangClosure.NativeRowRepresentative.Certificate f) (row : Nat), f.parent (c.root row) = c.root row
'YulangClosure.NativeRowRepresentative.root_fixed' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeRowRepresentative.root_idempotent

```lean
@YulangClosure.NativeRowRepresentative.root_idempotent : ∀ {f : YulangClosure.NativeRowRepresentative.Forest}
  (c : YulangClosure.NativeRowRepresentative.Certificate f) (row : Nat), c.root (c.root row) = c.root row
'YulangClosure.NativeRowRepresentative.root_idempotent' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeRowRepresentative.root_rank_le

```lean
@YulangClosure.NativeRowRepresentative.root_rank_le : ∀ {f : YulangClosure.NativeRowRepresentative.Forest}
  (c : YulangClosure.NativeRowRepresentative.Certificate f) (row : Nat), c.rank (c.root row) ≤ c.rank row
'YulangClosure.NativeRowRepresentative.root_rank_le' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeRowRepresentative.root_rank_lt

```lean
@YulangClosure.NativeRowRepresentative.root_rank_lt : ∀ {f : YulangClosure.NativeRowRepresentative.Forest}
  (c : YulangClosure.NativeRowRepresentative.Certificate f) (row : Nat),
  f.parent row ≠ row → c.rank (c.root row) < c.rank row
'YulangClosure.NativeRowRepresentative.root_rank_lt' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeRowRepresentative.find_bounded

```lean
@YulangClosure.NativeRowRepresentative.find_bounded : ∀ {f : YulangClosure.NativeRowRepresentative.Forest}
  (c : YulangClosure.NativeRowRepresentative.Certificate f) {fuel row result : Nat},
  row < f.size → YulangClosure.NativeRowRepresentative.find f fuel row = Option.some result → result < f.size
'YulangClosure.NativeRowRepresentative.find_bounded' depends on axioms: [propext]
```

### YulangClosure.NativeRowRepresentative.root_bounded

```lean
@YulangClosure.NativeRowRepresentative.root_bounded : ∀ {f : YulangClosure.NativeRowRepresentative.Forest}
  (c : YulangClosure.NativeRowRepresentative.Certificate f) {row : Nat}, row < f.size → c.root row < f.size
'YulangClosure.NativeRowRepresentative.root_bounded' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeRowRepresentative.root_outside

```lean
@YulangClosure.NativeRowRepresentative.root_outside : ∀ {f : YulangClosure.NativeRowRepresentative.Forest}
  (c : YulangClosure.NativeRowRepresentative.Certificate f) (row : Nat), f.size ≤ row → c.root row = row
'YulangClosure.NativeRowRepresentative.root_outside' does not depend on any axioms
```

### YulangClosure.NativeRowRepresentative.link_absorbs

```lean
@YulangClosure.NativeRowRepresentative.link_absorbs : ∀ {f : YulangClosure.NativeRowRepresentative.Forest}
  (c : YulangClosure.NativeRowRepresentative.Certificate f) (source to row : Nat),
  YulangClosure.NativeRowRepresentative.redirect c.root source to (c.root row) =
    YulangClosure.NativeRowRepresentative.redirect c.root source to row
'YulangClosure.NativeRowRepresentative.link_absorbs' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeRowRepresentative.find_lookup

```lean
@YulangClosure.NativeRowRepresentative.find_lookup : ∀ {f : YulangClosure.NativeRowRepresentative.Forest}
  {fuel row result : Nat},
  YulangClosure.NativeRowRepresentative.find f fuel row = Option.some result →
    YulangClosure.NativeRowRepresentative.Lookup f row result
'YulangClosure.NativeRowRepresentative.find_lookup' depends on axioms: [propext]
```

### YulangClosure.NativeRowRepresentative.lookup_unique

```lean
@YulangClosure.NativeRowRepresentative.lookup_unique : ∀ {f : YulangClosure.NativeRowRepresentative.Forest}
  {row first second : Nat},
  YulangClosure.NativeRowRepresentative.Lookup f row first →
    YulangClosure.NativeRowRepresentative.Lookup f row second → first = second
'YulangClosure.NativeRowRepresentative.lookup_unique' does not depend on any axioms
```

### YulangClosure.NativeRowRepresentative.lookup_terminates

```lean
@YulangClosure.NativeRowRepresentative.lookup_terminates : ∀ {f : YulangClosure.NativeRowRepresentative.Forest}
  (c : YulangClosure.NativeRowRepresentative.Certificate f) (row : Nat),
  YulangClosure.NativeRowRepresentative.Lookup f row (c.root row)
'YulangClosure.NativeRowRepresentative.lookup_terminates' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeRowRepresentative.lookup_result

```lean
@YulangClosure.NativeRowRepresentative.lookup_result : ∀ {f : YulangClosure.NativeRowRepresentative.Forest}
  (c : YulangClosure.NativeRowRepresentative.Certificate f) {row result : Nat},
  YulangClosure.NativeRowRepresentative.Lookup f row result → result = c.root row
'YulangClosure.NativeRowRepresentative.lookup_result' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeRowRepresentative.vector_birth

```lean
YulangClosure.NativeRowRepresentative.vector_birth : ∀ (parents : List Nat),
  YulangClosure.NativeRowRepresentative.ofList (parents ++ [parents.length]) =
    YulangClosure.NativeRowRepresentative.birth (YulangClosure.NativeRowRepresentative.ofList parents)
'YulangClosure.NativeRowRepresentative.vector_birth' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeRowRepresentative.vector_write

```lean
YulangClosure.NativeRowRepresentative.vector_write : ∀ (parents : List Nat) (row target : Nat),
  row < parents.length →
    YulangClosure.NativeRowRepresentative.ofList (parents.set row target) =
      YulangClosure.NativeRowRepresentative.write (YulangClosure.NativeRowRepresentative.ofList parents) row target
'YulangClosure.NativeRowRepresentative.vector_write' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeRowRepresentative.merge_constructs

```lean
@YulangClosure.NativeRowRepresentative.merge_constructs : ∀ {f : YulangClosure.NativeRowRepresentative.Forest}
  (c : YulangClosure.NativeRowRepresentative.Certificate f) {fuel copy parent : Nat},
  c.height < fuel →
    copy < f.size →
      parent < f.size →
        ∃ result,
          YulangClosure.NativeRowRepresentative.merge f fuel copy parent = Option.some result ∧
            ∃ cert, ∀ (row : Nat), cert.root (c.root row) = cert.root row
'YulangClosure.NativeRowRepresentative.merge_constructs' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeRowRepresentative.compressPath_constructs

```lean
@YulangClosure.NativeRowRepresentative.compressPath_constructs : ∀ {f : YulangClosure.NativeRowRepresentative.Forest}
  (c : YulangClosure.NativeRowRepresentative.Certificate f) (fuel row : Nat),
  c.rank row < fuel →
    row < f.size →
      ∃ result,
        YulangClosure.NativeRowRepresentative.compressPath f fuel row (c.root row) = Option.some result ∧
          ∃ cert, cert.root = c.root ∧ cert.rank = c.rank
'YulangClosure.NativeRowRepresentative.compressPath_constructs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### YulangClosure.NativeRowRepresentative.compress_constructs

```lean
@YulangClosure.NativeRowRepresentative.compress_constructs : ∀ {f : YulangClosure.NativeRowRepresentative.Forest}
  (c : YulangClosure.NativeRowRepresentative.Certificate f) {fuel row : Nat},
  c.height < fuel →
    row < f.size →
      ∃ result,
        YulangClosure.NativeRowRepresentative.compress f fuel row = Option.some result ∧
          ∃ cert, cert.root = c.root ∧ cert.rank = c.rank
'YulangClosure.NativeRowRepresentative.compress_constructs' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### YulangClosure.NativeRowRepresentative.certificate_unique

```lean
@YulangClosure.NativeRowRepresentative.certificate_unique : ∀ {f : YulangClosure.NativeRowRepresentative.Forest}
  (first second : YulangClosure.NativeRowRepresentative.Certificate f), first.root = second.root
'YulangClosure.NativeRowRepresentative.certificate_unique' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeRowRepresentative.step_constructs

```lean
@YulangClosure.NativeRowRepresentative.step_constructs : ∀ {f g : YulangClosure.NativeRowRepresentative.Forest}
  (c : YulangClosure.NativeRowRepresentative.Certificate f),
  YulangClosure.NativeRowRepresentative.Step f g → ∃ cert, ∀ (row : Nat), cert.root (c.root row) = cert.root row
'YulangClosure.NativeRowRepresentative.step_constructs' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeRowRepresentative.run_constructs

```lean
@YulangClosure.NativeRowRepresentative.run_constructs : ∀ {first last : YulangClosure.NativeRowRepresentative.Forest}
  (c : YulangClosure.NativeRowRepresentative.Certificate first),
  YulangClosure.NativeRowRepresentative.Run first last → ∃ cert, ∀ (row : Nat), cert.root (c.root row) = cert.root row
'YulangClosure.NativeRowRepresentative.run_constructs' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeRowRepresentative.generated_certificate

```lean
@YulangClosure.NativeRowRepresentative.generated_certificate : ∀ {last : YulangClosure.NativeRowRepresentative.Forest},
  YulangClosure.NativeRowRepresentative.Run YulangClosure.NativeRowRepresentative.empty last →
    Nonempty (YulangClosure.NativeRowRepresentative.Certificate last)
'YulangClosure.NativeRowRepresentative.generated_certificate' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeRowRepresentative.run_absorbs

```lean
@YulangClosure.NativeRowRepresentative.run_absorbs : ∀ {first last : YulangClosure.NativeRowRepresentative.Forest},
  YulangClosure.NativeRowRepresentative.Run first last →
    ∀ (before : YulangClosure.NativeRowRepresentative.Certificate first)
      (after : YulangClosure.NativeRowRepresentative.Certificate last) (row : Nat),
      after.root (before.root row) = after.root row
'YulangClosure.NativeRowRepresentative.run_absorbs' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeRowRepresentative.run_operand_transport

```lean
@YulangClosure.NativeRowRepresentative.run_operand_transport : ∀
  {first last : YulangClosure.NativeRowRepresentative.Forest},
  YulangClosure.NativeRowRepresentative.Run first last →
    ∀ (before : YulangClosure.NativeRowRepresentative.Certificate first)
      (after : YulangClosure.NativeRowRepresentative.Certificate last)
      (tables : YulangClosure.NativeMergeExpansion.Effect.Tables) (key : YulangClosure.NativeMergeExpansion.Key),
      YulangClosure.NativeReplayCurrent.operand tables after.root key =
        YulangClosure.NativeMergeExpansion.Effect.renameOutcome after.root
          (YulangClosure.NativeReplayCurrent.operand tables before.root key)
'YulangClosure.NativeRowRepresentative.run_operand_transport' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeRowRepresentative.run_current_pair_transport

```lean
@YulangClosure.NativeRowRepresentative.run_current_pair_transport : ∀
  {first last : YulangClosure.NativeRowRepresentative.Forest},
  YulangClosure.NativeRowRepresentative.Run first last →
    ∀ (before : YulangClosure.NativeRowRepresentative.Certificate first)
      (after : YulangClosure.NativeRowRepresentative.Certificate last) (key : YulangClosure.NativeMergeExpansion.Key),
      YulangClosure.NativeMergeExpansion.Effect.renamePair after.root
          (YulangClosure.NativeReplayCurrent.currentPair before.root key) =
        YulangClosure.NativeReplayCurrent.currentPair after.root key
'YulangClosure.NativeRowRepresentative.run_current_pair_transport' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeRowRepresentative.generated_transport

```lean
@YulangClosure.NativeRowRepresentative.generated_transport : ∀
  {first last : YulangClosure.NativeRowRepresentative.Forest},
  YulangClosure.NativeRowRepresentative.Run YulangClosure.NativeRowRepresentative.empty first →
    YulangClosure.NativeRowRepresentative.Run first last →
      ∃ before after,
        (∀ (row : Nat), after.root (before.root row) = after.root row) ∧
          ∀ (tables : YulangClosure.NativeMergeExpansion.Effect.Tables) (key : YulangClosure.NativeMergeExpansion.Key),
            YulangClosure.NativeReplayCurrent.operand tables after.root key =
              YulangClosure.NativeMergeExpansion.Effect.renameOutcome after.root
                (YulangClosure.NativeReplayCurrent.operand tables before.root key)
'YulangClosure.NativeRowRepresentative.generated_transport' depends on axioms: [propext, Quot.sound]
```

## Handoff

All writes to these frozen code/note/handoff paths stop after this receipt. Fresh independent review is required before an accepted checkpoint. The primary may continue unrelated integration; no descendant authored this packet. A repair requires a new explicit revision and dependent revalidation. The next useful seam is native same-history representative ownership, not another generic map-law wrapper.
