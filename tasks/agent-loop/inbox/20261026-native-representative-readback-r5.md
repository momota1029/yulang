# Native representative readback r5 — frozen producer handoff

Frozen UTC: `2026-10-26T12:31:00.551547+00:00`. Primary-owned construction; fresh independent nonauthor review required. Four of ten bounded checks used; no live checker. No Git mutation belongs to this mathematical handoff.

Exact repository base before this component: `e5d2b7b7a6ec340743668075780e95e8a98c8ef5`. The paired note defines the successful pointer/readback boundary; no original root closure is claimed.

## Frozen inputs

| Path | SHA256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeRepresentativeReadback.lean` | `a2e9d1bc26220c0502e7c92f67b153c066716440a57e4cc4bec3cb110b07128e` |
| `notes/theory/2026-10-26-native-representative-readback-r5.md` | `1a9789b8a93dfc8fdfece7153f714a45c1d05273a6cb0ba6d39c924f7f9b4abe` |
| `notes/theory/lean/YulangClosure/NativeRowRepresentative.lean` | `91b29ddd33db8b8b67308dff14b655619763d5ecb153b715f03b02c031371ee2` |
| `notes/theory/lean/YulangClosure/NativeContextReadback.lean` | `321d087c8d2df5099f67beb75e4316d44114806bbfae2aa64ebda22a34bd83f2` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `cab85ff9a8a7dc5103fe932739dcea0dfc02e6420b1277565449882c802473bd` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |

## Exact receipts

The isolated project/cache and raw log directory is `/workspace/scratch/c10e953a5453/representative-readback-r5`. All commands use the official pinned distribution; no global configuration changed. Every focused command has a 120-second deadline; one checker at a time. No proof check failed in this component.

- `check01.log`: 4343 bytes, SHA256 `ed0241ab77714d8719d6588084c82f2fc424c0d2fcaadc33baed0e1e502635cd`, exit 0.
- `check02.log`: 5564 bytes, SHA256 `ae1b44e10a0fd5f10c0b1d737ab3cfbcf20bca47671ac1aca284d3e6d656bf13`, exit 0.
- `check03.log`: 13468 bytes, SHA256 `c581a40d697a8944aacb9119cbab75c07c8eea7999534089307ca2dc4e2c3970`, exit 0.
- `check04-origin-census.log`: 25324 bytes, SHA256 `b64e4e62ec5f2397bb0bfe8dceda4aca17afee1473dee7b74be62eba8cdd5502`, exit 0.

Origin census: 32 declarations / 16 theorem constants. Every unique balanced block has a complete full type and axiom report; whitelist checked for all declarations, not merely the ten authored roots. Exact theorem-axiom counts: `{"(none)": 4, "Classical.choice,Quot.sound,propext": 2, "Quot.sound": 1, "Quot.sound,propext": 8, "propext": 1}`.

## Full authored theorem output

```text
cwd: /workspace/scratch/c10e953a5453/representative-readback-r5/project
$ /workspace/scratch/c10e953a5453/toolchains/lean-4.35.0-linux/bin/lake --version
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
[exit 0]
cwd: /workspace/scratch/c10e953a5453/representative-readback-r5/project
$ /workspace/scratch/c10e953a5453/toolchains/lean-4.35.0-linux/bin/lake --no-cache env lean --version
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
[exit 0]
cwd: /workspace/scratch/c10e953a5453/representative-readback-r5/project
$ /workspace/scratch/c10e953a5453/toolchains/lean-4.35.0-linux/bin/lake --no-cache build +YulangClosure.NativeRepresentativeReadback
Build completed successfully (10 jobs).
[exit 0]
cwd: /workspace/scratch/c10e953a5453/representative-readback-r5/project
$ /workspace/scratch/c10e953a5453/toolchains/lean-4.35.0-linux/bin/lake --no-cache env lean -j1 -M1024 --root=/tmp/yulang-lean-audit-qci04ytj /tmp/yulang-lean-audit-qci04ytj/YulangProofAudit.lean
YULANG_AUDIT_BEGIN YulangClosure.NativeRepresentativeReadback.certificate_readback
@YulangClosure.NativeRepresentativeReadback.certificate_readback : ∀
  {forest : YulangClosure.NativeRowRepresentative.Forest}
  (certificate : YulangClosure.NativeRowRepresentative.Certificate forest),
  YulangClosure.NativeRepresentativeReadback.Readback forest certificate.root
'YulangClosure.NativeRepresentativeReadback.certificate_readback' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeRepresentativeReadback.certificate_readback
YULANG_AUDIT_BEGIN YulangClosure.NativeRepresentativeReadback.readback_unique
@YulangClosure.NativeRepresentativeReadback.readback_unique : ∀ {forest : YulangClosure.NativeRowRepresentative.Forest}
  {first second : Nat → Nat},
  YulangClosure.NativeRepresentativeReadback.Readback forest first →
    YulangClosure.NativeRepresentativeReadback.Readback forest second → first = second
'YulangClosure.NativeRepresentativeReadback.readback_unique' depends on axioms: [Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeRepresentativeReadback.readback_unique
YULANG_AUDIT_BEGIN YulangClosure.NativeRepresentativeReadback.readback_absorbs
YulangClosure.NativeRepresentativeReadback.readback_absorbs : ∀
  (interval : YulangClosure.NativeRepresentativeReadback.Interval) {before after : Nat → Nat},
  YulangClosure.NativeRepresentativeReadback.Readback interval.before before →
    YulangClosure.NativeRepresentativeReadback.Readback interval.after after →
      ∀ (row : Nat), after (before row) = after row
'YulangClosure.NativeRepresentativeReadback.readback_absorbs' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeRepresentativeReadback.readback_absorbs
YULANG_AUDIT_BEGIN YulangClosure.NativeRepresentativeReadback.construct_readback
YulangClosure.NativeRepresentativeReadback.construct_readback : ∀
  (interval : YulangClosure.NativeRepresentativeReadback.Interval) {before : Nat → Nat},
  YulangClosure.NativeRepresentativeReadback.Readback interval.before before →
    ∃ after,
      YulangClosure.NativeRepresentativeReadback.Readback interval.after after ∧
        ∀ (row : Nat), after (before row) = after row
'YulangClosure.NativeRepresentativeReadback.construct_readback' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeRepresentativeReadback.construct_readback
YULANG_AUDIT_BEGIN YulangClosure.NativeRepresentativeReadback.raw_merge_event
@YulangClosure.NativeRepresentativeReadback.raw_merge_event : ∀ {t : YulangClosure.NativeContextExpansion.Tables}
  (s : YulangClosure.NativeContextReadback.State t)
  (effectRows valueRows : YulangClosure.NativeRepresentativeReadback.Interval) (effect value : Nat → Nat),
  YulangClosure.NativeRepresentativeReadback.Readback effectRows.before s.effectMap →
    YulangClosure.NativeRepresentativeReadback.Readback valueRows.before s.valueMap →
      YulangClosure.NativeRepresentativeReadback.Readback effectRows.after effect →
        YulangClosure.NativeRepresentativeReadback.Readback valueRows.after value →
          s.settling = Bool.true →
            YulangClosure.NativeContextReadback.Step t s
              (YulangClosure.NativeRepresentativeReadback.install s effect value)
'YulangClosure.NativeRepresentativeReadback.raw_merge_event' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeRepresentativeReadback.raw_merge_event
YULANG_AUDIT_BEGIN YulangClosure.NativeRepresentativeReadback.construct_merge_event
@YulangClosure.NativeRepresentativeReadback.construct_merge_event : ∀ {t : YulangClosure.NativeContextExpansion.Tables}
  (s : YulangClosure.NativeContextReadback.State t)
  (effectRows valueRows : YulangClosure.NativeRepresentativeReadback.Interval),
  YulangClosure.NativeRepresentativeReadback.Readback effectRows.before s.effectMap →
    YulangClosure.NativeRepresentativeReadback.Readback valueRows.before s.valueMap →
      s.settling = Bool.true →
        ∃ effect value,
          YulangClosure.NativeRepresentativeReadback.Readback effectRows.after effect ∧
            YulangClosure.NativeRepresentativeReadback.Readback valueRows.after value ∧
              YulangClosure.NativeContextReadback.Step t s
                (YulangClosure.NativeRepresentativeReadback.install s effect value)
'YulangClosure.NativeRepresentativeReadback.construct_merge_event' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeRepresentativeReadback.construct_merge_event
YULANG_AUDIT_BEGIN YulangClosure.NativeRepresentativeReadback.construct_merge_history
@YulangClosure.NativeRepresentativeReadback.construct_merge_history : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} {s : YulangClosure.NativeContextReadback.State t},
  YulangClosure.NativeContextReadback.Run t (YulangClosure.NativeContextReadback.initial t) s →
    ∀ (effectRows valueRows : YulangClosure.NativeRepresentativeReadback.Interval),
      YulangClosure.NativeRepresentativeReadback.Readback effectRows.before s.effectMap →
        YulangClosure.NativeRepresentativeReadback.Readback valueRows.before s.valueMap →
          s.settling = Bool.true →
            ∃ effect value,
              YulangClosure.NativeRepresentativeReadback.Readback effectRows.after effect ∧
                YulangClosure.NativeRepresentativeReadback.Readback valueRows.after value ∧
                  YulangClosure.NativeContextReadback.Run t (YulangClosure.NativeContextReadback.initial t)
                      (YulangClosure.NativeRepresentativeReadback.install s effect value) ∧
                    YulangClosure.NativeContextReadback.Invariant
                        (YulangClosure.NativeRepresentativeReadback.install s effect value) ∧
                      (∃ f fs,
                          (YulangClosure.NativeRepresentativeReadback.install s effect value).control.frames = f :: fs ∧
                            f.phase = YulangClosure.NativeDrainOwnership.Phase.working ∧ f.current = Option.none) ∧
                        (YulangClosure.NativeRepresentativeReadback.install s effect value).control = s.control ∧
                          (YulangClosure.NativeRepresentativeReadback.install s effect value).memo = s.memo ∧
                            (YulangClosure.NativeRepresentativeReadback.install s effect value).owners = s.owners ∧
                              (YulangClosure.NativeRepresentativeReadback.install s effect value).relations =
                                  s.relations ∧
                                (YulangClosure.NativeRepresentativeReadback.install s effect value).tasks = s.tasks ∧
                                  (YulangClosure.NativeRepresentativeReadback.install s effect value).generation =
                                    s.generation + 1
'YulangClosure.NativeRepresentativeReadback.construct_merge_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeRepresentativeReadback.construct_merge_history
YULANG_AUDIT_BEGIN YulangClosure.NativeRepresentativeReadback.single_effect_merge_event
@YulangClosure.NativeRepresentativeReadback.single_effect_merge_event : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} (s : YulangClosure.NativeContextReadback.State t)
  (effects values : YulangClosure.NativeRowRepresentative.Forest),
  YulangClosure.NativeRowRepresentative.Run YulangClosure.NativeRowRepresentative.empty effects →
    YulangClosure.NativeRowRepresentative.Run YulangClosure.NativeRowRepresentative.empty values →
      YulangClosure.NativeRepresentativeReadback.Readback effects s.effectMap →
        YulangClosure.NativeRepresentativeReadback.Readback values s.valueMap →
          ∀ (copy parent : Nat),
            copy < effects.size →
              parent < effects.size →
                s.effectMap copy ≠ s.effectMap parent →
                  s.settling = Bool.true →
                    ∃ effect,
                      YulangClosure.NativeRepresentativeReadback.Readback
                          (YulangClosure.NativeRowRepresentative.write effects (s.effectMap copy) (s.effectMap parent))
                          effect ∧
                        YulangClosure.NativeContextReadback.Step t s
                          (YulangClosure.NativeRepresentativeReadback.install s effect s.valueMap)
'YulangClosure.NativeRepresentativeReadback.single_effect_merge_event' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeRepresentativeReadback.single_effect_merge_event
YULANG_AUDIT_BEGIN YulangClosure.NativeRepresentativeReadback.single_value_merge_event
@YulangClosure.NativeRepresentativeReadback.single_value_merge_event : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} (s : YulangClosure.NativeContextReadback.State t)
  (effects values : YulangClosure.NativeRowRepresentative.Forest),
  YulangClosure.NativeRowRepresentative.Run YulangClosure.NativeRowRepresentative.empty effects →
    YulangClosure.NativeRowRepresentative.Run YulangClosure.NativeRowRepresentative.empty values →
      YulangClosure.NativeRepresentativeReadback.Readback effects s.effectMap →
        YulangClosure.NativeRepresentativeReadback.Readback values s.valueMap →
          ∀ (copy parent : Nat),
            copy < values.size →
              parent < values.size →
                s.valueMap copy ≠ s.valueMap parent →
                  s.settling = Bool.true →
                    ∃ value,
                      YulangClosure.NativeRepresentativeReadback.Readback
                          (YulangClosure.NativeRowRepresentative.write values (s.valueMap copy) (s.valueMap parent))
                          value ∧
                        YulangClosure.NativeContextReadback.Step t s
                          (YulangClosure.NativeRepresentativeReadback.install s s.effectMap value)
'YulangClosure.NativeRepresentativeReadback.single_value_merge_event' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeRepresentativeReadback.single_value_merge_event
YULANG_AUDIT_BEGIN YulangClosure.NativeRepresentativeReadback.compression_keeps_readback
@YulangClosure.NativeRepresentativeReadback.compression_keeps_readback : ∀
  {forest : YulangClosure.NativeRowRepresentative.Forest} {map : Nat → Nat},
  YulangClosure.NativeRowRepresentative.Run YulangClosure.NativeRowRepresentative.empty forest →
    YulangClosure.NativeRepresentativeReadback.Readback forest map →
      ∀ (row : Nat),
        row < forest.size →
          ∃ fuel after,
            YulangClosure.NativeRowRepresentative.compress forest fuel row = Option.some after ∧
              YulangClosure.NativeRepresentativeReadback.Readback after map
'YulangClosure.NativeRepresentativeReadback.compression_keeps_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeRepresentativeReadback.compression_keeps_readback
[exit 0]
PASS: YulangClosure.NativeRepresentativeReadback.certificate_readback, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeRepresentativeReadback.readback_unique, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeRepresentativeReadback.readback_absorbs, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeRepresentativeReadback.construct_readback, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeRepresentativeReadback.raw_merge_event, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeRepresentativeReadback.construct_merge_event, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeRepresentativeReadback.construct_merge_history, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeRepresentativeReadback.single_effect_merge_event, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeRepresentativeReadback.single_value_merge_event, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeRepresentativeReadback.compression_keeps_readback, under its printed hypotheses; axiom whitelist satisfied.
Named declarations only; ordinary-mistake check, not independent review or source correspondence.
```

## Source correspondence and residuals

The before-map input is raw `Lookup` readback, not a representative law. Empty-generated forest histories construct all certificates; deterministic lookup identifies the observed map. `raw_merge_event` applies the derived Effect and Value laws to the existing shared driver event. `construct_merge_event` constructs final maps. `construct_merge_history` extends one already reachable Run and obtains its preserved invariant and actual settlement cut. The two single-link roots match the native same-kind copy-root-to-parent-root write and leave the other map fixed; compression preserves the map without a generation event.

The general Interval theorem is a coarse-driver premise discharge; it does not count the concrete number of native generation increments. Whole Rust history extraction, same native table epochs, checked arithmetic/reservation failures, metadata/capture/bound/replay updates, rollback and original semantic bodies/source-scoped witnesses remain OPEN. No caller-provided absorption, semantic child success or completed-body predicate was moved into a disguised premise.

## Writer stop

The module, note and this handoff are frozen for independent review. No worker descendants, background checker, compiler/configuration/reserved-root/index/status edits. The primary will perform reviewed integration and expected-head Git updates separately.
