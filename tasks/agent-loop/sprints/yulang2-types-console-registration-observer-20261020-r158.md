# Yulang2 Types/Console registration observer — R158

Status: prospective exact implementation contract. Active user goal and `/goal resume` authorize this bounded reversible research instrumentation. Luna activates only after independent CLEAN review and records the exact-path lease. No semantic approval, Y3 implementation, tests, builds, parser/sample execution, expected-output edits, or production cutover is authorized.

## Parent outcome and baseline

The goal remains broader proof-backed inference/evaluator implementation and execution of unchanged Yulang2 Web demo samples. Preserve the original Simple-sub/evaluator A/B claims and quantifiers, source/native correspondence, semantic approval, expected-output protection, and independent review. Parent theorem, sample identity, and production gates remain OPEN. This sprint's measurable outcome is a frozen provisional observer diff that can record each loaded source and all twelve source-route registration appends in the reviewed R157 taxonomy, with one JSONL sink and no manual JSON escaping in `infer`.

Y3 baseline: `85586bb7343b41f286f34b937f2d8e99e8629ced`. Y2 oracle commit: `a58eefc31e22141574b6f20c6a5748151c6d79f1`. Reuse the R156 exact sample/source pins and R157 CLEAN taxonomy; do not repeat the 12-site census. R157 closeout: `notes/progress/2026-10-20-r157-closeout.md`, SHA-256 to be frozen before activation. R157 stop result: `notes/progress/2026-10-20-r157-implementation-stop.md`, SHA-256 `cc684a11d7d273c9358bc6734f33337d77df5b548e9bb1a80ac4dd5bfb5e6722`.

Frozen Y2 source pins:

- `crates/sources/src/lib.rs`: blob `38d85d7dbb76bca11917963af52f72b17769e3c8`, SHA-256 `1738881e4e177c3d54cfc6f258c3ed1e2fe6d38df85738e3d49a78472721bbdf`.
- `crates/infer/src/module_map/mod.rs`: blob `0e20fedcfef410b647b3fc90e70afa3fc0cb73e6`, SHA-256 `05415473b824ce540207e694bf35883536cb5ef0ec67e8dae12f943411388134`.
- `crates/infer/src/module_map/finish.rs`: blob `d7f12816d99d1e410daf2fc7323598082ba39a33`, SHA-256 `e66f9cf348a6d382288d05d368530a04ec7da0d8bd4073fd19191b36ab2708e6`.
- Read-only `crates/sources/Cargo.toml`: SHA-256 `dee68364690ddb824a9d335abf927821cc32ba1ecf876e803be8e661fb4ddd23`.
- Read-only `crates/infer/Cargo.toml`: SHA-256 `3cd89c9b52a3e0d4d0e74c985b53f9b29b41f426141703a30a58486a3fc8d330`.

Dependency premise: `infer` depends on `sources`; `sources` has `serde_json`; both crates have `serde`. No manifest or lockfile edits are in scope. The three source hashes match the unchanged isolated archive; read-only manifest inspection supports the dependency seam.

## One implementation packet — 120 seconds preparation

Work only in `/tmp/yulang2-r156-observer/oracle/`, produced from the pinned Y2 commit. Writable files are exactly:

- `/tmp/yulang2-r156-observer/oracle/crates/sources/src/lib.rs`
- `/tmp/yulang2-r156-observer/oracle/crates/infer/src/module_map/mod.rs`
- `/tmp/yulang2-r156-observer/oracle/crates/infer/src/module_map/finish.rs`

Add an appropriately bounded generic `serde::Serialize` JSONL sink in `sources` using its existing `serde_json` dependency. The two `infer` files pass serializable event records through this sink; they must not manually format or escape JSON. The reviewed implementation design must show that one complete JSON record and newline are written atomically with respect to concurrent records, output path validation is exact, and failures emit the specified failure marker and invalidate the witness without changing source diagnostics or compiler results.

Preserve the R157 schema and semantics: environment variable `YULANG_LOADED_WITNESS_OUT`; only `/tmp/yulang2-r156-observer/out/types.jsonl` and `/tmp/yulang2-r156-observer/out/console.jsonl`; `loaded_file`, all twelve `registration_event` sites with physical producer-site IDs and separate origin provenance, and `observer_failure` records. Preserve actual ModuleOrder, visibility, DefId/name/module joins, span state, copied-mode precedence, and loaded source bytes/CST/operator evidence as pinned in the R157 taxonomy. Compiled insertion remains excluded. With the environment variable absent, do not construct/sort/serialize records, lock, or write; compiler behavior must be unchanged. Do not silently omit records on lock, serialization, or write failure.

The packet freezes actual helper API, synchronization and error strategy, exact source/input pins, and exact intended diff paths. Do not expand scope if an invariant is unclear; stop and report the smallest concrete blocker.

## Prospective independent review — 120 seconds

Review the frozen contract and packet together against R157's CLEAN taxonomy and exact dependency manifests. Check all twelve append sites, LoadedFile construction identity, disabled-mode noninterference, single-record write synchronization, exact path allowlist, serialization and partial-output invalidation, event order/provenance, and unchanged public/compiler behavior. CLEAN permits Luna to issue the implementation grant below. Any changes require a new sequential revision and delta review.

## Conditional Luna/high implementation — 360 seconds

After CLEAN review, Luna grants the exact three-file lease above to one implementation worker for 360 seconds. It may complete related implementation steps inside this envelope. No tests, builds, CLI/parser/sample execution, manifest changes, Y3 writes, expected-output changes, or additional path edits. On an invariant failure, STOP before expanding scope.

## Independent code review and closeout

Fresh independent reviewer receives 120 seconds for the frozen exact diff and dependency pins. Review event coverage, producer/provenance mapping, LoadedFile/source joins, actual order and duplicate preservation, output/error semantics, disabled-mode noninterference, and all changed paths. Luna records a 120-second closeout with exact hashes and remaining premises. Patch remains provisional and isolated; no witness execution or parent gate closure follows.

## Resource ceiling

Fresh R158 cap 840 seconds: 120 packet preparation + 120 prospective review + 360 conditional implementation + 120 independent code review + 120 closeout. Charge grants when issued; Astra 0; no R157 carryover. No build, test, or execution allocation. Only Luna owns state, grants, leases, independent review assignment, adjudication, and Git.

## Lanes, falsifier, and next boundary

Implementation lane: produce the isolated observer diff. Source-evidence lane: Luna compares each emitted registration record's producer and order relation to the CLEAN R157 taxonomy and R154 consumer relation within their stated premises. A missing/duplicated append, wrong source join, order mismatch, source/compiled conflation, output-loss ambiguity, or any changed disabled-mode behavior falsifies the observer result. Independent code review is the seam. Y3 production remains `WAITING_NO_SAFE_CODE_SLICE`; theorem and sample identity gates remain OPEN.

Consult the dispatcher at sprint end or if a new producer/authority dependency, source contradiction, or integration seam appears. A later command to emit witnesses requires a separate exact invocation packet and bounded execution grant.
