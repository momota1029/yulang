# Frozen source handoff — EFFECT-PERMISSION-ORIGIN-TRACE-REPAIR/R101

Assignment-ID / revision: `effect-permission-origin-trace-repair` / 1.
Parent: R101 admitted by Luna at `d0829f48a`; R100 observer candidate remains test-only/provisional. Original parent, source/native bridge, semantics, and production gates remain OPEN.
Baseline `candidate_effect.rs` SHA-256: `114bf61685037e65a7ff5ebb83e089080b7b38433472197eabe7ff1026e03cbc`.
Exact writable paths: `crates/yu-solver/src/candidate_effect.rs` and this handoff only. No descendants.

## Change

Inspected all `origin` trace emitters and consumers in the leased source file. The sole textual-prefix consumer is `formal_permission_live_capture_source_observation_trace`, which requires `origin occurrence=`. Updated the test-only origin formatter to retain that established prefix and field ordering (`occurrence`, parameter, owner, scope, path, source row, concrete members, allocated row), then append `witness` and `constructor`. No emitter outside this test observer, production code, or consumer assertion changed. R100's negative-root domain/node join and memo miss/hit/delegated-tail witness assertions are untouched.

## Checks and limits

Static `rg` inspection found one origin trace emitter and one prefix consumer, now matching. No Cargo/build/test, Git, scratch, environment change, or other path write. No independent review or execution evidence is claimed. This diagnostic trace repair does not prove source-to-constraint, propagation, captured-port, native, or parent theorem correspondence.

Final `candidate_effect.rs` SHA-256: `536942ff167cdd869c5a3a9eade852453bde6c9f53a5e64023194e681d1cebe6`.

All writes ceased before handoff hashing: **STOPPED**. No descendants or disposable scratch were created.
