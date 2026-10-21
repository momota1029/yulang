# R156 implementation stop — source registration event boundary

Status: implementation stage stopped before writes. The result is a concrete source-coverage blocker, not evidence of successful observer implementation. R156 parent sample identity and initializer census remain OPEN.

## Frozen inputs and independent reviews

- R156 contract revision 2 SHA-256: `eb3c281dc0777d5517510327c2bcc14700eee88bb8c063056ea09bce03071f62`.
- Stage A implementation packet revision 2 SHA-256: `a7eeb9d5087bd0d219a8601c497cc35205f7107fb54486de6631d2e2df375fa3`; its independent review was CLEAN after correcting the cache route and output allowlist.
- Y2 oracle commit: `a58eefc31e22141574b6f20c6a5748151c6d79f1`. The oracle worktree remained unchanged by R156.
- Isolated archive: `/tmp/yulang2-r156-observer/oracle/`, produced by `git archive` from the pinned commit. No code edits were made.
- Exact untouched copied source hashes: `sources/src/lib.rs` `1738881e4e177c3d54cfc6f258c3ed1e2fe6d38df85738e3d49a78472721bbdf`; `infer/src/module_map/mod.rs` `05415473b824ce540207e694bf35883536cb5ef0ec67e8dae12f943411388134`; `infer/src/module_map/finish.rs` `e66f9cf348a6d382288d05d368530a04ec7da0d8bd4073fd19191b36ab2708e6`.

## Exact registration producer inventory

The pinned source has twelve `insert_value_with_span` calls in the two leased producer files. Every call must be represented if the artifact claims to be a complete source-route registration census. The shared storage method alone cannot identify origin; source callsite identity must be recorded. Compiled insertion remains a separate route and excluded.

| Producer | Observed origin / source-span behavior |
|---|---|
| `module_map/mod.rs:393` | Source-authored `OpDef`; `Some(info.source_range)` |
| `module_map/mod.rs:519` | Source-authored binding values; optional name range |
| `module_map/mod.rs:634` | Role implementation method; optional method-name range |
| `module_map/mod.rs:666` | Role implementation binding; optional binding-name range |
| `module_map/mod.rs:1141` | Synthetic-value helper; caller-dependent span, including `None` and source-origin enum variants |
| `module_map/mod.rs:1205` | Role companion method; optional method-name range |
| `module_map/mod.rs:1240` | Role companion binding; optional binding-name range |
| `module_map/mod.rs:1335` | Act companion operation; direct or copied-source mode; copied mode may suppress span |
| `module_map/mod.rs:1364` | Act companion method; direct or copied-source mode; copied mode may suppress span |
| `module_map/mod.rs:1402` | Act companion binding; direct or copied-source mode; copied mode may suppress span |
| `module_map/finish.rs:88` | Type companion method; optional method-name range |
| `module_map/finish.rs:120` | Type companion binding; optional binding-name range |

The initial packet named only a generic `source_registration` event. It did not define whether generated synthetic values, source-origin enum variants routed through the synthetic helper, and copied-source act companions were source events or how to tag them. Emitting only ordinary declarations would omit actual appends. Emitting all twelve without an explicit origin taxonomy would overstate source identity for copied/generated records. The implementer correctly stopped before writes.

## Resources and activity

R156 cap: 960 seconds. Issued/charged: 120 prospective contract review + 240 Stage A preparation + 120 independent Stage A packet review + 240 conditional implementation grant = 720 seconds. The implementation grant was charged on issue; the worker stopped before writing. The unissued 120 seconds from the 360-second implementation ceiling are released. Remaining 240 seconds are reserved for independent review of this exact stop result and closeout. Astra 0; no carryover.

No tests, builds, parser/sample execution, expected-output changes, Y3 edits, Git mutations, staging, commits, or pushes occurred. Parent Simple-sub/evaluator A/B, R70/R71, source/native generality, soundness, principality and production remain OPEN. No result establishes the sample declaration census or initializer order.

## Boundary for continuation

Before a new implementation grant, freeze an event taxonomy for all twelve producer sites. Each record needs the physical producer site, the actual loaded module/source join, DefId/name/order/visibility, exact span or explicit span absence, and an origin tag distinguishing direct source, source-derived/synthetic, copied-source, and compiled-route exclusion. Preserve all records without relabeling generated or copied entries as direct source declarations. Review the revised packet independently, then grant only exact paths and a fresh bounded implementation allocation. No build, test, or sample execution authority follows from this stop result.
