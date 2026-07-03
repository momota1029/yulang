# Contract v1: File / Host Resource priority memo

出典: ChatGPT Pro の 2026-07-02 優先順位提案。ユーザ承認済みの
優先順メモとして記録する。

## Verdict

Contract v0 は再び「完成させる対象」ではない。`stable-core` の executable spine は
`docs/language/contract-v0-evidence.md` と `tests/yulang/cases.toml` によって閉じた。

次に Yulang を「完成」に近づける contract slice は:

> **Contract v1: File / Host Resource Contract**

具体的には、ファイルが「耐久性のある `&` 変数」として、mock / native CLI /
unsupported host で同じ意味論を持って動く状態を目標にする。

## Priority Order

1. **File Resource Contract**
   - Contract v1 の箱を作る。
   - pure mock file handler で `text_with` commit / rollback / multi-shot commit を
     fixture 化する。
     - 2026-07-02: public helper shape covers reusable commit, rollback, and
       branch-local buffers. Direct public `ref.update` over local `$buffer` is
       also a `stable-core` contract. Production `text_with` still needs a
       public mockable session boundary; private snapshot helpers must not be
       made public just to satisfy this.
      - 2026-07-02 follow-up: replacing production `open_in` with a plain
        public `read_text` / local `$buffer` / public `ref { ... }` /
        `write_text` helper leaks the handler-local `&buffer#...` effect into
        the public `open_in` / `text_with` signature. This is rejected by the
        public type boundary, so the next implementation path must be a real
        public file-session or host-act boundary that hides resource-local
        state.
   - native host handler を mock と同じ snapshot transaction 意味論へ寄せる。
     - 2026-07-03: added `file_native_meta_file`, so native metadata now has an
       isolated positive file case covering `file_meta.kind`, size, and
       `exists` / `is_file` / `is_dir` wrappers.
     - 2026-07-03: added `file_native_meta_missing`, so native metadata now
       covers a missing target through `file_meta.kind` and proves `exists` /
       `is_file` / `is_dir` stay metadata wrappers.
     - 2026-07-03: added `file_native_meta_directory`, so native metadata also
       covers directory kind and predicate wrappers without asserting
       environment-dependent directory size.
     - 2026-07-02: native normal commit / user-error rollback / nondet
       branch-local snapshot は executable contract 化済み。
     - 2026-07-03: added `file_text_with_native_undet_last_write_wins`, so
       native `text_with` now has executable nondet branch-local
       last-write-wins evidence over the public `load` / `store` protocol.
     - 2026-07-03: added `file_text_with_native_nested_cross_file`, so native
       `text_with` also covers two backing files with independent commits and
       lexical capture of the outer entry snapshot.
     - 2026-07-03: added `file_text_with_native_nested_state_var`, so native
       `text_with` also covers callback-local `&` state captured and mutated
       from an inner `text_with` callback.
     - 2026-07-03: added `file_native_protocol_typed_failures`, so native
       `file::load` missing-target and `file::store` directory failures are
       observed as `io_err::not_found` / `io_err::failed` values rather than
       integer error codes.
     - 2026-07-03: added `file_native_helper_typed_failures`, so public
       `read_text` / `write_text` preserve those typed failures through
       `io_err::wrap`.
     - 2026-07-03: added public signature canaries for
       `std.io.file.io_err.not_found` and `std.io.file.io_err.failed`.
     - 2026-07-03: classified native `InvalidInput` / `InvalidData` host
       failures as `io_err::invalid_path` and added
       `file_native_invalid_path_typed_failure` plus public signature canaries
       for `io_err::denied` and `io_err::invalid_path`.
   - unsupported host は fake success せず typed failure または structured diagnostic にする。
     - 2026-07-02: `file_unsupported_host` で structured runtime failure 化済み。
     - 2026-07-03: added `file_text_unsupported_host`, so the ambient
       operations used by unscoped `file::text` also have structured
       unsupported-host failure coverage.
     - 2026-07-03: added `file_read_text_unsupported_host` and
       `file_write_text_unsupported_host`, so public text helper load/store
       routes also fail structurally under `--host unsupported` instead of
       faking success.
     - 2026-07-03: added `file_text_native_missing_host_io_error`, so native
       missing-file ambient reads now report `yulang.host-io-error` instead of
       falling through as an unhandled effect.
     - 2026-07-03 closeout: ambient operations are integrated into the unified
       `file` act as `ambient_touch`, `ambient_get`, and `ambient_set`.
       `file::text` now performs eager `ambient_touch`, so missing native text
       resources become typed `io_err::not_found` at lens creation time while
       the returned ref stays `ref '[file] str`.
   - packaged binary + bundled std で file-resource contract を走らせる。
     - 2026-07-02: local archive smoke で current `file-resource` subset 通過済み。
     - 2026-07-03: direct `scripts/release-smoke.sh` now runs a focused
       representative `file-resource` contract set against the smoke binary and
       installed std. Full `--contract file-resource` stays in archive/local
       validation because it is too heavy for the direct smoke loop.
   - 残りの大きな blocker は pure mock resource-lifetime parity。
     - 2026-07-02: この blocker の実装指示書が
       `notes/design/2026-07-02-file-session-boundary-plan.md`（Claude 署名・authoritative）
       として確定した。file-resource の次の作業はこの指示書の Stage 0 から始める。
       周辺 case の追加は本工事の代わりにしない。進捗は指示書 Stage 1 の
       fixture 6 件と Stage 2 の削除項目でだけ測る。
     - 2026-07-02 follow-up: 改訂4 の state-passing protocol へ載せ替え済み。
       Stage 1 の mock/protocol fixture 6 件は `--host unsupported` の
       `file-resource` subset で通る。旧 scoped `file_buffer::get/set`、
       transfer probe、`same_path`、callback residual blocker note は撤去済み。
       残りは Stage 2: native registry、int error code 全廃、release/archive
       evidence の更新。
     - 2026-07-03 follow-up: native registry / release/archive evidence /
       `std::io::file` host bridge の int error code 全廃は通過済み。残りは
       `raw-compat` file session replacement/removal と native ambient failure
       typing。raw/provisional isolation 自体は manifest/debug/CLI/unit
       canary で固定済み。
     - 2026-07-03 closeout: legacy snapshot session helpers are retired from
       `std::io::file`; `read_at` / `write_at` are the only remaining
       `raw-compat` range helpers. Contract v1 protocol-center cases are now
       classified as `stable-api`; `raw-compat` remains `migration-canary`.

2. **Host act FFI registry**
   - `host act` manifest 生成。
   - registry dispatch へ移行し、perform 時の文字列 if をなくす。
   - file / console / server / clock / random / future FFI を同じ host handler 機構へ寄せる。
   - 未登録 act は `EscapedEffect` crash ではなく capability failure にする。
   - 2026-07-02 Claude Fable decision: `std::io::file` should move onto the
     `io-resource-api` spec shape. Session operations should become publicly
     catchable, integer error codes should be removed, and dispatch should go
     through the host registry. This is the regular fix for the pure mock
     parity blocker, so priorities 1 and 2 are one implementation track.
   - 2026-07-03 decision: this priority now has two approved authoritative
     instruction docs. `notes/design/2026-07-03-host-abi-v0.md` fixes the host
     implementation ABI (Cranelift-link-first, VM injection as its subset;
     HostOpFn / BoundaryValue / registration-set API; v0 explicitly unstable).
     `notes/design/2026-07-03-host-manifest-compiler-production-plan.md`
     (rev 1, subset of the ABI doc) moves the manifest source of truth from the
     evidence-vm static table to compiler production keyed by a new
     `pub host act` modifier. Work order: manifest Stage 1 and ABI Stage α are
     independent; manifest Stage 2 requires ABI Stage α.
   - 2026-07-03 follow-up: console now has the same public host-act contract
     evidence shape as file for the first routing slice:
     `console_unsupported_host` proves unsupported host denial, and
     `console_mock_out_handler` proves source handlers intercept
     `std::io::console::out.write` before the host registry when native host
     operations are disabled. `std_console_out_write_public_signature` also
     fixes the console host-act public type boundary.
   - 2026-07-03 closeout: ABI Stage α and manifest Stage 2 are implemented for
     the current VM subset. `HostOpFn` / `BoundaryValue` / registration-set
     dispatch are in evidence-vm, std host manifests are compiler-produced from
     `pub host act`, and registry resolution uses plan manifest × registrations
     instead of the removed static runtime table. `std::time::clock.now` is on
     the same host-act path with native / unsupported / mock contract canaries.
     Remaining work in this priority is new host surfaces (server / random),
     suspend-tier execution, band-provided implementations, and Native ABI FFI
     beyond the VM subset.

3. **Diagnostics + LSP / playground parity**
   - role/method diagnostic を specialization oracle bridge から dedicated check-stage owner へ寄せる。
     - 2026-07-03: owner migration complete. Source diagnostics now read
       emission-free `specialize::role_method_check`, while run/backend paths
       still report the existing role method `SpecializeError` variants.
   - CLI / LSP / playground が同じ `SourceDiagnostic` payload を読む。
     - 2026-07-03: wasm `run()` lowering failures now pass through the same
       structured `SourceDiagnostic` conversion as `check()`, with run/check
       parity coverage and a regression keeping runtime failures on the message
       diagnostic path (commit 2ee20770). Runtime errors and route errors other
       than `LoweringDiagnostics` intentionally remain message diagnostics.
     - 2026-07-04: the playground web UI now renders the structured payload:
       label prefix, hint, and related information with line:column ranges and
       origin decoration (commit d624757e).
   - LSP / editor robustness: 2026-07-04 fixed parser EOF recovery panics
     (unterminated string, trailing `::`, and similar EOF paths) with
     prefix-totality tests, so mid-edit sources no longer kill diagnostics /
     semantic tokens (commit eda03d12). Semantic tokens also keep a lexical
     fallback under parse recovery (commit bbb71c17), and yulang-zed now ships
     a thicker tree-sitter baseline with `"semantic_tokens": "combined"`
     guidance (submodule commit 892054a).
   - hover は public projection を出し、内部 evidence や巨大型を漏らさない。
     - 2026-07-03: Stage 1 of
       `notes/design/2026-07-03-hover-public-type-projection.md` is
       implemented: `poly::dump::format_scheme_public(_with_path_rewriter)`
       with a Public style that drops solver stack/subtractability markers and
       redacts internal names / centerless bounds as `…` with a redaction
       counter. LSP hover def path and wasm exported types now use it, with
       dump-parity and leak-canary tests (commits 736dcfd7, 64980b9d).
     - 2026-07-03: Stage 2 (structural truncation numbers, hover local/select
       paths, LSP char-cap replacement) is gated on user review per the design
       doc.
     - 2026-07-04: Stage 2 of the hover public projection is implemented except
       the marker-spelling revision: Public style now has structural
       truncation budgets (depth 10 / 600 rendered chars, `…` with a separate
       truncations counter), hover local-arg and record/select use-site types
       go through the public projection, and the LSP 1200-char cap remains only
       as a final safety net (commits 80032176, a1e55e27). Displaying
       stack-weight / subtractability evidence in a prettier public spelling
       (instead of dropping it) is pending a user decision on notation.
     - 2026-07-04: P2R (user-decided notation) is implemented — public type display now renders stack weights as `@N` boundary ids with `(∅)` / `(∀)` / `[hs]` / `(except [hs])` subtractability and numeric pop parens, eliding the id (and parens for single-symbol marks) when the scheme has a single boundary, e.g. `['c@∅]` and trailing `'e@`; full shapes with floor/filter stay redacted (commits e8b5a330, 6f6c825a).

4. **Release artifact contract**
   - packaged binary で `stable-core` と file-resource representative contract を通す。
     - 2026-07-03: direct release smoke covers the representative file-resource
       set; archive smoke still runs the broader contract tag filters with the
       bundled std.
   - bundled std と repo std の差で結果が変わらないようにする。
   - `yulang server` startup、Zed discovery、cache status を release smoke へ残す。

5. **Server in-process driver**
   - HTTP framework ではなく in-process test driver から始める。
   - `accept` suspend/resume、request resource、one-shot response、double respond failure を固定する。
   - 2026-07-03: serve 実装前の structured concurrency 決定文書を
     `notes/design/2026-07-03-structured-concurrency-decisions.md` に追加した。
     first slice は scheduler branch id / parent id、cancel queue、suspend 中 branch
     の immediate drop から始める。

6. **Static route Stage M1, then conditional Stage 1**
   - `notes/design/2026-07-03-static-route-mono-resolution-plan.md` に従い、mono 側分類器の
     Stage M1 再計測で被覆率を判定する。
   - Stage 1 は Stage 0 の hits と Stage 1a shadow mismatch 0 が揃った場合だけ。
   - 2026-07-03: Stage M0 moved the classification source of truth to
     specialize / mono and Evidence VM now consumes `RuntimeEvidenceSurface`
     routes. `scripts/static-route-stage0-profile.sh` was rerun as the Stage M1
     profile on the representative 4-workload set. All four compare-control
     checks matched and `static_route_mono_join_failures` stayed 0, but
     `static_route_static_tail` and runtime static-tail hits were still 0
     everywhere:
     nondet `3/3 provider_env` with 861 provider-env runtime hits; showcase
     `11 provider_env + 2 hygiene` with 2457 provider-env and 7 hygiene runtime
     hits; `03_for_last` `7/7 provider_env` with 2 provider-env runtime hits;
     `02_refs` `8/8 provider_env` with 10 provider-env runtime hits.
     Stage 1 remains blocked. Do not loosen the classifier to improve these
     numbers.
   - 2026-07-02 Claude Fable decision: evidence VM micro-optimizations stay
     frozen until the mono-time proof emission translation work starts.

7. **Later tracks**
   - package / registry。
   - parser DSL / Yumark。
   - native ABI / native backend。

## File Resource Contract Box

最初の PR / commit 列では、実装を広げすぎず、contract の箱を作る。

追加候補:

- `docs/language/file-resource-contract.md`
- `docs/language/contract-v1-file-evidence.md`
- `docs/status.md` の Public Contract Spine に File Resource Contract 行
- `tests/yulang/cases.toml` の tag policy:
  - `file-resource`
  - `resource-lifetime`
  - `mock-host`
  - `host.native`
  - `host.unsupported`

Done:

- `stable-core` と `file-resource` を混ぜない。
- `migration-canary` と `stable-api` を混ぜない。
- manifest に TODO placeholder を置かない。
- file resource case は runtime output / typed failure / public signature /
  diagnostic のどれかを compact に固定する。

## First Implementation Slice: Mock File Handler

最初の実装はディスクに触らない pure mock handler とする。

必須 fixture:

- `file_text_with_commit`
  - scope exit で write-back。
- `file_text_with_rollback_on_error`
  - effect abort なら rollback。
- `file_text_with_undet_last_write_wins`
  - multi-shot branch ごとの独立 buffer と到達順 last-write-wins。
- `file_text_unscoped_handler_discharge`
  - unscoped resource は handler extent 終端で commit。
- `file_text_mock_matches_native_shape`
  - mock handler と native handler が同じ public surface を見る。

この slice が通ると、Yulang の file API は単なる I/O ではなく、
multi-shot continuation と resource lifetime が同居する標準 API になる。

## Native Host Slice

native 側はまず lock なしでよい。

Done:

- `text_with` 内で通常編集すると temp file が更新される。
- `text_with` 内で error abort すると temp file が無傷。
- `text_with` 内で undet / junction branch を使っても branch-local buffer と
  last-write-wins が観測できる。
- public signature に `#...` / `AllExcept` が漏れない。
- `read_text` / `write_text` は便利 wrapper として残すが、中心 API とは呼ばない。

## Unsupported Host Slice

native success だけで contract を閉じない。

Done:

- wasm / playground / sandboxed host で unsupported file capability が fake success しない。
- capability unsupported / denied と operation failure (`not_found` など) を分ける。
- unsupported behavior を CLI / playground / LSP の structured payload に寄せる。

## Do Not

- Contract v0 を一般論で reopen しない。
- file resource の中心を `read_text` / `write_text` helper にしない。
- HTTP framework を server first slice にしない。
- serve implementation に入る前に structured-concurrency の決定文書を先に書く。
- native ABI FFI や native backend 復活へ先に行かない。
- performance work で Stage 0 の停止条件を飛ばさない。
