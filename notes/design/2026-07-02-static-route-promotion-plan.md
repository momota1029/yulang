# 静的 route 昇格 実装指示書

作成日: 2026-07-02
著者: Claude (Fable 5) — ユーザ承認済み（2026-07-02）。
状態: **指示書（authoritative）**。実行エージェント（Codex 等）はこの文書に従うこと。
改訂: Stage 0 の実装位置と分類根拠は
[2026-07-03-static-route-mono-resolution-plan.md](2026-07-03-static-route-mono-resolution-plan.md)
により差し替え（納品された evidence-vm 内の lowering 由来分類は退役対象）。
Stage 1a / 1b / 2・判定表・rollback 条件は本文書のまま有効。

根拠文書: [2026-07-02-speedup-proof-system.md](2026-07-02-speedup-proof-system.md)
（ユーザ承認済み）。本指示書はその提案 1（静的 route 昇格）と提案 2
（evidence slot 静的インデックス化）を実装段階に落としたもの。
提案 3（scope-delta 正規化）は 2026-06-30-VM高速化計画.md の Phase 3 に合流させ、
本指示書の範囲外。提案 4（Fold 代数 cert）は別指示書を待つこと。

**この指示書の意味論・受理条件・期待値を実装の都合で変えないこと。**
テスト期待値は本指示書と根拠文書から手で導出する。実装出力から逆算しない。
変更が必要に見えたら、実装を止めてユーザに確認する。

## 中心命題（根拠文書 §5 より）

> 一番速い証明は、実行時に検査されない証明である。
> 発行を mono / specialize 時へ移し、検査を消滅させる。

現状: `EvidenceRouteCert::ProviderGrant` の gate 検査
（`provider_grant_gate_passes`、runtime.rs:8378 付近）が signal 毎に走る。
腕の静的分類 `EvidenceVmHandlerArmClass`（lib.rs:120）は既に存在し、
lib.rs:2691 で execution plan に写像されている。
本工事は「静的に解決できる call site では gate 検査を発行時ごと消す」こと。

## 用語の定義

**call site の静的解決**: specialize（mono 後）の時点で、operation call site c
について次がすべて判定できること。

1. c の effect family の handler が一意に定まる（候補 handler が 1 つ）。
2. c と その handler の間に、静的に排除できない遮蔽
   （AddId / handler boundary / provider env の動的差し替え / delayed-callback
   境界）が存在しない。
3. 解決先 handler の該当腕の `EvidenceVmHandlerArmClass` が既知である。

1〜3 のどれかが判定できない site は **Dynamic(reason)** とし、現行の
動的 cert 経路に残す。静的解決は「全部を静的にする」工事ではない。
**判定できる場所だけを昇格し、残りは一切触らない。**

## Stage 0: 被覆率計測 pass（挙動変更なし）

### 目的

提案 1 の利得は静的解決の被覆率に比例する。まず数字を出す。
**この Stage では実行意味論を一切変えない。**

### 実装位置

- `crates/specialize/src/specialize2/runtime_evidence.rs` —
  `RuntimeEvidenceSurface` に計測結果を載せる。導管の前例は
  `known_state_handlers`（`attach_known_state_handlers`、同ファイル 28 行付近）。
  同じ形で `attach_static_route_profile`（名前は合わせてよい）を足す。
- 分類対象: specialize 済み unit 内の全 operation call site。

### 分類

```rust
enum StaticRouteResolution {
    StaticHandler {
        arm_class: /* 解決腕の分類 */,
    },
    Dynamic(StaticRouteDynamicReason),
}

enum StaticRouteDynamicReason {
    OpenRow,                 // effect row が閉じていない
    MultipleCandidates,      // 候補 handler が複数
    HygieneBarrier,          // 静的に排除できない遮蔽がありうる
    ProviderEnvDependent,    // provider env の動的内容に依存
    DelayedBoundary,         // delayed/callback 境界を挟む
    HostEscape,              // どの handler にも catch されず host に逃げる
    Unclassified,            // 上記に当てはまらない（理由をコメントで残す）
}
```

`HostEscape` は将来の host act FFI（2026-07-02-host-act-ffi-decisions.md §F6
sync tier）がそのまま消費する分類なので、独立に数えること。

### counters / 出力

```text
static_route_sites_total
static_route_static_handler
static_route_static_tail_resumptive     // StaticHandler かつ TailResumptive
static_route_static_abortive
static_route_static_other_arm
static_route_dynamic_open_row
static_route_dynamic_multiple_candidates
static_route_dynamic_hygiene_barrier
static_route_dynamic_provider_env
static_route_dynamic_delayed_boundary
static_route_dynamic_host_escape
static_route_dynamic_unclassified
```

静的な site 数に加えて、**動的な発火回数**を重み付けするため、
runtime 側で「この request の call site は Stage 0 でどう分類されていたか」を
突き合わせる counter を debug / deep-profile 時のみ追加する
（known-operation-calls の Stage A 前例に従う。release 通常経路に
traversal を足さないこと）。

```text
static_route_runtime_hits_static_tail
static_route_runtime_hits_static_other
static_route_runtime_hits_dynamic_*
```

### Validation

```bash
cargo fmt --all -- --check
cargo check -q -p specialize -p evidence-vm -p yulang
cargo check -q --release -p specialize -p evidence-vm -p yulang
cargo test -q -p specialize -- --test-threads=1
cargo test -q -p evidence-vm -- --test-threads=1
cargo test -q -p yulang runtime_evidence -- --test-threads=1
tests/yulang/yulang-adversarial-corpus/probe.sh
target/release/yulang --std-root lib debug evidence-vm-run --compare-control bench/nondet_20_discard.yu
target/release/yulang --std-root lib debug evidence-vm-run --compare-control examples/showcase.yu
```

計測値は `notes/progress/daily/<date>.md` に表で残す
（nondet_20_discard / showcase / 03_for_last / 02_refs の 4 本）。

### 判定表

| 観測 | 意味 | 行動 |
| --- | --- | --- |
| `static_tail_resumptive` の runtime hits が全 request の 30% 以上 | 本命に十分な獲物 | Stage 1 へ |
| static は多いが runtime hits が薄い | 静的解決できる場所は冷えている | 停止して報告。Stage 1 に進まない |
| `dynamic_hygiene_barrier` が大半 | 遮蔽判定が粗すぎる可能性 | 判定の細分化を 1 回だけ試み、それでも大半なら停止して報告 |
| `dynamic_open_row` が大半 | mono の row が想定より開いている | 停止して報告（specialize 側の別課題） |
| `unclassified` が 10% 超 | 分類の穴 | 理由を列挙して報告。勝手に分類を増やして塗り潰さない |

**どの停止条件でも、数字と理由の報告までが Stage 0 の完了。**
勝手に Stage 1 へ進まない。

## Stage 1: 静的 direct call（TailResumptive × StaticHandler 限定）

Stage 0 の判定表で「Stage 1 へ」となった場合のみ着手する。

### Stage 1a: shadow（挙動変更なし）

静的解決の判定が動的 cert と一致することを先に確かめる。

- StaticHandler と分類された site の request について、実行時に動的経路が
  実際に選んだ handler / route と突き合わせる。
- counter: `static_route_shadow_match` / `static_route_shadow_mismatch_*`
  （mismatch は handler 不一致 / route 不一致 / 遮蔽検出漏れで分ける）。
- **mismatch が 1 件でもあれば Stage 1b に進まない。** mismatch は
  静的判定側のバグであり、判定を直すか Dynamic に倒す。動的側を変えない。

### Stage 1b: 実行

- gate 定数（例 `STATIC_ROUTE_DIRECT_EXECUTOR_ENABLED`）で全体を戻せる形にする。
- 対象は `StaticHandler × TailResumptive` のみ。Abortive / Yield 系は
  この指示書の範囲外（次の指示書を待つ）。
- 対象 site の operation call を、cert 発行と gate 検査なしの直接実行に落とす。
  fallback として現行経路を残し、僅かでも前提が崩れる site は Dynamic に倒す。
- generic request fallback の真実面（truth surface）を弱めない。

### 維持条件 / rollback

維持:

```text
- compare-control match（nondet / showcase）
- adversarial corpus pass
- shadow mismatch が 0 のまま
- nondet または showcase の中央値が 5% 以上改善
- 他方の代表ワークロードが実質悪化しない
```

rollback:

```text
- compare-control mismatch / adversarial failure / shadow mismatch > 0
- 両代表ワークロードで改善 < 5% のまま複雑さだけ増える
- 衛生性系テスト（blocked route / delayed boundary / 同名別 family）のどれかが変化
```

## Stage 2: evidence slot 静的インデックス化（着手前にユーザ確認）

Stage 1b の結果が出た時点で一度ユーザに報告し、承認を得てから着手する。
概要のみ固定しておく:

- mono 後の閉じた row から effect family ごとの evidence slot 番号を
  静的に割り当て、provider env lookup を配列添字にする。
- `active_add_id_scans` / nearest-ProviderEnv 探索系 counter の減少と
  実時間の改善を両方確認する（counter だけ減って実時間が悪化した
  duplicate marker scope skip の前例を忘れないこと）。

## やってはいけないこと

- path / 関数名 / fixture 名の文字列で分類・分岐すること。
- 静的判定と動的判定が食い違ったとき、**動的側（現行意味論）を変える**こと。
- テスト期待値を実装出力に合わせて書き換えること。
- 「守るべき変数集合」「blocked ペア」型の保護機構を infer / specialize に足すこと。
- native close 三兄弟（NativeProviderPair 等）を本工事で触ること
  （退役は提案 3 = Phase 3 の工事でのみ行う）。
- generic request fallback を弱めること。
- release 通常経路に計測 traversal を乗せること（deep-profile / debug 限定）。
- Stage の停止条件を無視して次へ進むこと。

## 報告形式

各 Stage 完了時に `notes/progress/daily/<date>.md` へ:

- 変更ファイルと gate 定数の状態
- counter 表（Stage 0 の分類表 / Stage 1 の shadow・実行表）
- 代表 4 ワークロードの中央値・最小・最大
- 停止した場合はどの判定行に当たったか

---

*署名: この指示書は Claude (Fable 5) が 2026-07-02 に、ユーザ承認済みの
根拠文書（2026-07-02-speedup-proof-system.md）から実装段階へ落としたものである。
変更にはユーザの明示的な承認を要する。 — Claude (Fable 5)*
