# 静的 route 分類の mono 時再着床 実装指示書

作成日: 2026-07-03
著者: Claude (Fable 5) — ユーザ依頼（2026-07-03、「Koka 風の静的解析を入れたつもりが
動的解析になっている。mono は型が分かっているので静的に入れられるはず」）に基づく。
状態: **指示書（authoritative）**。実行エージェント（Codex 等）はこの文書に従うこと。

根拠文書:
[2026-07-02-speedup-proof-system.md](2026-07-02-speedup-proof-system.md)（承認済み）、
[2026-07-02-static-route-promotion-plan.md](2026-07-02-static-route-promotion-plan.md)
（元指示書）。本文書は元指示書の **Stage 0 の実装位置と分類根拠を差し替える改訂**であり、
元指示書の Stage 1a / 1b / 2 の意味論・受理条件・判定表・rollback 条件は変更しない。

**この指示書の意味論・受理条件・期待値を実装の都合で変えないこと。**
テスト期待値は本指示書と根拠文書から手で導出する。実装出力から逆算しない。
変更が必要に見えたら、実装を止めてユーザに確認する。

---

## 1. 診断 — 何が「動的解析」になっているか

元指示書 Stage 0 は分類 pass の実装位置を
`crates/specialize/src/specialize2/runtime_evidence.rs`
（`known_state_handlers` 導管 = `attach_known_state_handlers`、同ファイル 28 行付近の
前例に従う）と指定した。実装はこれに従わず、分類が
**evidence-vm の中**に置かれた:

- 分類関数: `operation_static_route_resolution`
  （`crates/evidence-vm/src/lib.rs:2747`）。
- 分類の入力: `EvidenceVmOperationLowering`（lib.rs:166）——
  **VM 自身の lowering が動的 routing のためにどの fallback に落としたか**の分岐。
  mono の型・effect row・specialized instance の情報を一切参照していない。

帰結（すべて現行コードと 2026-07-02 daily の計測に現れている）:

1. **`OpenRow` は一度も発行されない**。理由 enum に `#[allow(dead_code)]`
   が付いたまま（lib.rs:331）。row を見ていないのだから当然で、
   これが「型情報を見ていない」ことの最短の証拠である。
2. `GenericFallback` の分類は `matching_handler_count`（lib.rs:2794）=
   **プログラム全体の handler object の名前一致数**で行われる。
   これは経路解決ではなく名前カウントであり、「その call site に届く handler」
   とは無関係。同名 handler が 1 つなら `ProviderEnvDependent`、
   2 つ以上なら `MultipleCandidates` と、解決を試みずにラベルが決まる。
3. 関数境界を一つでも跨ぐ operation call は、mono 側なら閉じた row と
   specialized call graph で解決できる場合でも、全て `ProviderEnvDependent` /
   `MultipleCandidates` / `Unclassified` に落ちる。
4. その結果、Stage 0 代表 4 ワークロードの計測（2026-07-02 daily）は
   **static tail runtime hits 0%** となり、判定表により Stage 1 は永久に
   開始できない。この 0% は「静的に解決できる場所が冷えている」ことの計測では
   なく、**分類器が mono の知識を見ていないこと**の計測である。

つまり現状は、speedup-proof-system §2 が言う
「Koka が静的に済ませる証明を、動的に毎回再演している」状態の**上に**、
動的機構の分岐ラベルを写しただけの分類が「静的分類」を名乗って乗っている。
静的な証明は一枚も発行されていない。

**2026-07-02 daily の Stage 0 判定（「Stage 1 は許可されない」）は本文書により
無効とする。** 判定表そのものは正しい。無効なのは入力の数字である。
Stage M1（§5）で正しい分類器の数字により再判定する。

## 2. 直し方の中心

> 分類の正本を mono / specialize 側へ移す。evidence-vm は分類を**消費**するだけにする。

specialize は既に per-site の材料をすべて持っている:

- `RuntimeEvidenceSiteKind::OperationCall`（def / path / callee / arg）と
  `Catch`（handled_paths）——site の一覧。
- `RuntimeEvidenceExprType`——各 expr の solved `Type`（`EffectRow` を含む）。
- row residuals / effect subtraction——handler が row から何を引いたか。
- specialized instance と call 構造（`callee_instance` は specialize が既知）。
- compiler 生成 host manifest（2026-07-03-host-manifest-compiler-production-plan、
  Stage 1 済み）——host act の静的集合。

これらから operation call site ごとの静的解決を specialize 内で計算し、
`RuntimeEvidenceSurface` の新しい導管で evidence-vm に渡す。
導管の形は `known_state_handlers` / `known_state_accesses` の前例に**厳密に**従う。

## 3. 用語（元指示書から変更なし、再掲）

**call site の静的解決**: specialize（mono 後）の時点で、operation call site c
について次がすべて判定できること。

1. c の effect family の handler が一意に定まる（候補 handler が 1 つ）。
2. c とその handler の間に、静的に排除できない遮蔽
   （AddId / handler boundary / provider env の動的差し替え / delayed-callback
   境界）が存在しない。
3. 解決先 handler の該当腕の `EvidenceVmHandlerArmClass` が既知である。

判定できない site は **Dynamic(reason)** とし、現行の動的経路に残す。
**判定できる場所だけを昇格し、残りは一切触らない。**

## 4. Stage M0: mono 側解決 pass + 導管（挙動変更なし）

この Stage では実行意味論を一切変えない。変わるのは分類の産地と精度だけである。

### 4.1 surface への追加

`RuntimeEvidenceSurface` に追加する（serde 既定値つき、既存 field と同様）:

```rust
pub static_routes: Vec<RuntimeEvidenceStaticRoute>,

pub struct RuntimeEvidenceStaticRoute {
    pub operation_expr: u32,   // OperationCall site の expr
    pub apply: u32,
    pub callee: u32,
    pub family: Vec<String>,   // operation path
    pub resolution: RuntimeEvidenceStaticRouteResolution,
}

pub enum RuntimeEvidenceStaticRouteResolution {
    StaticHandler {
        handler_expr: u32,     // 解決先 Catch site の expr
        // arm_class はここに置かない（§4.4）
    },
    Dynamic(RuntimeEvidenceStaticRouteDynamicReason),
}
```

`Dynamic` の理由は元指示書の 7 分類
（OpenRow / MultipleCandidates / HygieneBarrier / ProviderEnvDependent /
DelayedBoundary / HostEscape / Unclassified）をそのまま使う。

計算の入口は `attach_static_route_profile(&mut self, arena, ...)` とし、
`attach_known_state_handlers` と同じ場所・同じ呼び出し規律で呼ぶ。

### 4.2 解決アルゴリズム

**一回の線形パスで書く。全体を収束まで回す不動点反復を足さないこと**
（ユーザの確立済み方針）。call graph の循環は SCC 縮約の上の一回の伝播で扱う。

**L1（task 内・字句解決）**: OperationCall site c（family F）について、
同一 task の expression 木で c を囲む最内の Catch のうち F を handle するものを探す。

- c と Catch body の間に **Lambda（function value）境界がある場合は L1 不成立**
  （λ は値として catch の外に運ばれうるため。argument_contract の有無で
  精密化できるが、本 Stage では保守的に不成立とする）。
- 見つかれば `StaticHandler { handler_expr = その Catch }`。
  最内を取るので同 family の遮蔽は定義により正しく扱われる。

**L2（instance 伝播）**: L1 で解決しない site は F が instance の row に残って
呼び出し元へ逃げる。specialized call graph（instance → callee_instance の辺）を
SCC 縮約し、roots から**一回だけ**伝播する:

- 各 call 辺について、その apply site を囲む caller 側の L1 handler
  （F を handle する最内 Catch、λ 境界規則は同上）があればそれを文脈とし、
  なければ caller 自身が継承した文脈集合を流す。
- SCC 内は文脈集合を合併して全 member に適用する。
- instance に到達した F の文脈集合で判定する:
  - 単一の handler site → `StaticHandler`
  - 2 つ以上 → `Dynamic(MultipleCandidates)`
  - 空で、F が compiler 生成 host manifest にある → `Dynamic(HostEscape)`
  - 空で、site の row（または instance row）の tail が開いている →
    `Dynamic(OpenRow)`
  - それ以外の空 → `Dynamic(Unclassified)`（理由をコメントで残す）
- 伝播経路に delayed / callback 境界が挟まる辺は文脈を流さず、その site を
  `Dynamic(DelayedBoundary)` に倒す。境界の静的判定に自信が持てない構文は
  `Dynamic(HygieneBarrier)` に倒す。**迷ったら Dynamic。**

`ProviderEnvDependent` は「文脈が call site ごとに異なるため単一に潰れない」
場合の理由として残る（MultipleCandidates との違い: 候補は特定できているが
経路依存で選択が変わる）。区別が付かない実装になるなら MultipleCandidates に
寄せてよいが、どちらに寄せたかを文書コメントに残すこと。

### 4.3 evidence-vm 側の置換

- `operation_static_route_resolution`（lib.rs:2747）と
  `matching_handler_count`（lib.rs:2794）は**退役**させる。
  lowering 由来の再導出を「静的分類」として残さないこと。
- 分類は surface の `static_routes` を導管（plan.rs の
  `known_state_accesses` 消費と同じ形: expr id で突き合わせ）から取る。
- surface に載っていない operation call site は
  `Dynamic(Unclassified)` として数える（分類の穴は隠さず数字に出す）。

### 4.4 arm class の合流

腕の分類（`EvidenceVmHandlerArmClass`）の正本は evidence-vm の lowering にあり、
そこから動かさない。mono 側は handler **site**（Catch expr）まで解決し、
evidence-vm が consumption 時に自分の handler object から arm_class を引いて
`StaticHandler { arm_class }` に合成する。

- 合成に失敗した場合（mono が static と言ったのに VM 側に対応する handler
  object がない）は `Dynamic(Unclassified)` に倒し、専用 counter
  `static_route_mono_join_failures` に数える。**これは mono 側のバグの兆候**
  であり、VM 側で補完しないこと。

### 4.5 counters

counter 名は元指示書のものを**そのまま維持**する
（`static_route_sites_total` / `static_route_static_*` /
`static_route_dynamic_*`、runtime 側 `static_route_runtime_hits_*`）。
既存の profile script（`scripts/static-route-stage0-profile.sh`）と
`debug evidence-vm-plan` の `static_route` 表示は無改修で新分類を映すこと。
追加は `static_route_mono_join_failures` のみ。

runtime hits の計測規律も元指示書のまま: release 通常経路に traversal を
足さない（deep-profile / debug 限定）。

### 4.6 fixtures（期待値は本文書から手で導出する）

specialize のテストとして最低限:

1. **catch 直下**: tail-resumptive 腕を持つ catch の body 直下の operation call
   → `StaticHandler`（L1）。evidence-vm 合成後は static-tail に数えられる。
2. **λ 跨ぎ**: 同じ構造で operation call を λ の中に入れ、λ を catch の外へ
   値として返す → L1 不成立、L2 でも解決しない形なら `Dynamic`。
3. **helper 一文脈**: operation を含む helper 関数を単一の catch 文脈から呼ぶ
   → L2 で `StaticHandler`。**これが現行分類器で 0% になっていた本命ケース。**
4. **helper 二文脈**: 同じ helper を異なる handler の下から 2 回呼ぶ
   → `Dynamic(MultipleCandidates)`。
5. **host escape**: どの handler にも catch されない host act 操作
   → `Dynamic(HostEscape)`（compiler 生成 manifest との突き合わせ）。
6. **join 失敗系**: 合成失敗が `Dynamic(Unclassified)` +
   `static_route_mono_join_failures` に落ちること（unit test でよい）。

### 4.7 Validation

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

compare-control は全て match すること（分類は実行に影響しないのだから、
mismatch が出たら Stage M0 の範囲を逸脱した変更をしている）。

## 5. Stage M1: 再計測と再判定

`scripts/static-route-stage0-profile.sh` を代表 4 ワークロード
（nondet_20_discard / showcase / 03_for_last / 02_refs）で再実行し、
**元指示書 Stage 0 の判定表をそのまま適用し直す**。

- 期待の方向（拘束ではない・数字は計測が正本）: L2 の導入により
  `static_tail_resumptive` が 0 から動き、02_refs の 2 件の unclassified
  （`ref_update::update`、2026-07-02 daily で特定済み）が理由付きの分類に
  置き換わる。
- 新しい数字でも「Stage 1 に進まない」判定が出たら、それが正しい答えである。
  数字と理由を報告して停止する。**分類器を数字が良くなる方向に緩めないこと。**
- `OpenRow` が大半なら specialize 側の row が想定より開いている。
  停止して報告（元指示書と同じ）。

計測値は `notes/progress/daily/<date>.md` に表で残す。

## 6. Stage 1 以降

元指示書の Stage 1a（shadow）/ 1b（実行）/ Stage 2（slot 静的化、着手前に
ユーザ確認）を**そのまま**適用する。一点だけ明確化:

- Stage 1a の shadow 突き合わせの静的側は、本文書の **mono 側分類**である。
  mismatch は mono 側のバグであり、判定を直すか Dynamic に倒す。
  動的側（現行意味論）を変えない。

## 7. やってはいけないこと

元指示書の禁止事項は全て有効。本文書で追加:

- evidence-vm の lowering 分岐から分類を再導出し、それを「静的解決」と
  呼ぶこと（今回直す当のものである）。
- mono 側で判定できなかった site を VM 側のヒューリスティクスで
  StaticHandler に補完すること。
- 解決アルゴリズムに全体収束の不動点反復を足すこと
  （SCC 縮約上の一回の伝播で書けない設計になったら、実装を止めて相談する）。
- 2026-07-02 daily の旧 Stage 0 数字を新分類の期待値として再利用すること
  （旧数字は無効。§1）。
- counter 名の変更・削除（profile script と daily の時系列比較を壊す）。
- path / 関数名 / fixture 名の文字列で分類・分岐すること。
- テスト期待値を実装出力に合わせて書き換えること。

## 8. 報告形式

各 Stage 完了時に `notes/progress/daily/<date>.md` へ:

- 変更ファイルと、退役させた関数（`operation_static_route_resolution` /
  `matching_handler_count`）の処置
- Stage M1 の分類表（旧数字との並記。ただし旧数字は「無効な比較対象」と明記）
- 代表 4 ワークロードの runtime hits 表と compare-control 結果
- 判定表のどの行に当たったか

---

*署名: この指示書は Claude (Fable 5) が 2026-07-03 に、ユーザの指摘
（静的解析のつもりが動的解析になっている）を受けて現行実装
（`operation_static_route_resolution` ほか）と 2026-07-02 daily の計測を調査し、
元指示書 2026-07-02-static-route-promotion-plan.md の Stage 0 を mono 時解決へ
差し替える改訂として作成した。元指示書の Stage 1 以降・判定表・rollback 条件は
温存される。変更にはユーザの明示的な承認を要する。 — Claude (Fable 5)*
