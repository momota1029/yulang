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
     - 2026-07-02: native normal commit / user-error rollback / nondet
       branch-local snapshot は executable contract 化済み。
   - unsupported host は fake success せず typed failure または structured diagnostic にする。
     - 2026-07-02: `file_unsupported_host` で structured runtime failure 化済み。
   - packaged binary + bundled std で file-resource contract を走らせる。
     - 2026-07-02: local archive smoke で current `file-resource` subset 通過済み。
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
       raw/provisional isolation と native ambient failure typing。

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

3. **Diagnostics + LSP / playground parity**
   - role/method diagnostic を specialization oracle bridge から dedicated check-stage owner へ寄せる。
   - CLI / LSP / playground が同じ `SourceDiagnostic` payload を読む。
   - hover は public projection を出し、内部 evidence や巨大型を漏らさない。

4. **Release artifact contract**
   - packaged binary で `stable-core` と file-resource representative contract を通す。
   - bundled std と repo std の差で結果が変わらないようにする。
   - `yulang server` startup、Zed discovery、cache status を release smoke へ残す。

5. **Server in-process driver**
   - HTTP framework ではなく in-process test driver から始める。
   - `accept` suspend/resume、request resource、one-shot response、double respond failure を固定する。

6. **Static route Stage 0, then conditional Stage 1**
   - `notes/design/2026-07-02-static-route-promotion-plan.md` に従い、まず被覆率計測だけ行う。
   - Stage 1 は Stage 0 の hits と Stage 1a shadow mismatch 0 が揃った場合だけ。
   - 2026-07-02: Stage 0 counters and deep-profile runtime-hit counters are
     already wired. Use `scripts/static-route-stage0-profile.sh` to collect the
     representative 4-workload table before deciding whether Stage 1 is allowed.
     Generic fallback classification now uses the runtime host manifest to keep
     true host capability escapes separate from non-host sites, and then splits
     non-host generic fallbacks into `ProviderEnvDependent`,
     `MultipleCandidates`, or remaining `Unclassified` by matching handler
     object count.
   - 2026-07-02 representative profile after handler candidate counting:
     nondet / showcase / `03_for_last` have 0 unclassified runtime hits;
     `02_refs` still has 2 unclassified runtime hits. Stage 1 remains blocked
     because static-tail runtime hits are still 0.
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
