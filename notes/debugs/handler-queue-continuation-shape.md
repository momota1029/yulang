# ⑫b handler が継続を queue に cons する型が principal 形に単純化されない

## テスト
`display::dump::tests::render_compact_results_consolidates_queued_handler_continuation`
— `crates/yulang-infer/src/display/dump.rs`（① `render_compact_results_handles_ref_update_effect` の直後）

※ ⑫ の **Any/top 漏れ**（`tests::handler_continuation_..._avoids_top_in_effect_row`）は
`e533d43` で解決済み（純粋関数 cons の空エフェクトスロットが `Any`→`Never`、cons の render も
クリーン化）。本 doc は **その後に残った「型が汚い」問題**で、テストとしては別物。

## 入力
```yu
type list 'a
pub cons(x: 'a, xs: list 'a): list 'a = xs

my act eff:
    our op: () -> bool
    our handle(x: [eff] 'a, queue: list (bool -> [eff] 'a)) = catch x:
        op(), k -> cons(k, queue)
        value -> queue

eff::handle
```

## バグ表
| | |
|---|---|
| 期待値（正・ユーザ確定）| `α [β & [eff; γ]] -> list<bool -> [β] α> -> [γ] list<bool -> [β] α>` |
| 実際値（誤）| `α [δ & [; ε]] -> (β & list<bool -> [δ \| eff] α \| γ & bool -> [eff] α>) -> [ε] β \| list<bool -> [δ \| eff] α \| γ & bool -> [eff] α>` |

実際値が期待値から崩れている点（同じ制約の**単純化漏れ**——情報は同じで畳めていないだけ）:

1. **継続が2本に分裂**: `bool -> [δ | eff] α | γ & bool -> [eff] α` は同じ継続 `k` が
   - annotation 由来（`bool -> [eff] α`）
   - `cons(k, queue)` で k が queue 要素へ流れた分

   の2本に分かれて union になっている。`bool -> [β] α` **1本に merge** されるべき。
2. **余剰変数**: queue param の `β &`、arrow 内の `γ &` は cooccur で吸収されるべき影武者。
3. **エフェクト変数の分裂**: `[δ | eff]` と `[eff]` がバラバラ。継続の effect は単一 `[β]` に統合されるべき。
4. **注釈 eff が入力行から脱落**: 入力が `[δ & [; ε]]` で **eff が item として出ていない**。
   `x: [eff] 'a` と注釈されている以上、通っている `render_compact_results_handles_annotated_recursive_catch`
   （`α [io; β] -> [β] α` ＝注釈 io が item で残る）と同様に **`[eff; γ]`** と出るのが正。
   これは cosmetic ではなく**本物の脱落**（入力反変位置の注釈エフェクトは開いた行で残すべき）。

## なぜ期待値が正しいか（手計算）
- `op : () -> bool` → 継続 `k` は `bool` を受ける。
- `cons(k, queue)` で k は queue の要素型 `bool -> [eff] 'a` に拘束される（両 arm が list を返すので
  catch の結果型 ＝ queue の型）。よって継続は `bool -> [β] α`（入力 bool・出力 α＝'a・effect β）の**1本**。
- queue param も戻り値も同じ `list<bool -> [β] α>`（`value -> queue` と `cons(k,queue)` が同型）。
- 入力 `x` は eff を行う計算で、handler 通過後の残差が γ。反変位置の注釈エフェクトは**常に開く**ので
  入力は `[eff; γ]`（eff item ＋ tail γ）。k と x の effect 関係から x 側は `β & [eff; γ]`。
- 実際値は上記をすべて含むが、**等価な関数 bound の merge と影武者変数の消去ができていない**ため
  冗長な union/intersection と分裂した変数のまま出ている。期待値はその**単純化形**。

## ⚠️ 非決定性（重要・2026-06-06 発見）
このテストの actual は**実行ごとに揺れる**（同一コミット・同一入力で）:
- 約 4/5: `α [δ & [; ε]] -> (β & list<…>) -> [ε] β | list<…>`（外側に `β &`/`β |` アリ）
- 約 1/5: `α [γ & [; δ]] -> list<…> -> [δ] list<…>`（外側 `β &`/`β |` ナシ＝target に一歩近い）

変数名（δ/ε ↔ γ/δ）だけでなく**構造（`β &`/`β |` の有無）まで揺れる**＝
名前付け（VarNamer の HashSet 順）だけの問題ではなく、**cooccur の「どの変数を消すか／代表元選択」が
HashMap/HashSet の反復順に依存**している。含意:
1. memory の**既知 flake**（`--skip compiled` が時々 489/8）の正体がこれ。
2. **①と同じ病巣の直接証拠**: cooccur の代表元/消去が非決定的。①を直すには
   **反復順を安定化**（HashSet 反復ではなく stable key で sort）する必要がある。
3. 「少し綺麗な方」(1/5) が target に近い＝**綺麗な形は到達可能**、一貫して選ばれていないだけ。
- ピン留めした期待値はどの順序でも赤（全 variant が target と異なる）なので target-pin として機能する。
  ①の fix 後の合格条件は「**決定的に** clean target と一致」＝順序安定化込みで直ること。

## 診断（要 Codex 深掘り・①の後）
`queue` の要素にあたる型変数が**2つの関数下界**を持ち、coalesce がそれを1本に merge していない。
merge を阻んでいるのは `γ &`（arrow に交差した変数 γ）で、γ は cooccur で吸収されるべき影武者。
- ① `ref_update`（`ref<α&β,γ> -> (γ->[β]γ) -> [α,β] unit` が `ref<α,β> -> (β->[α]β) -> [α] unit`）が
  「消しすぎ（over-merge）」、本件は「消さなすぎ＋merge し損ね（under-merge）」で**症状は逆**だが、
  どちらも cooccur/coalesce が**principal 形に着地できていない**同じ病巣。
  さらに上記の非決定性で「消す変数」自体がブレている＝**順序非依存な cooccur**が両者の共通の鍵。

## 見るべき場所
- `crates/yulang-infer/src/simplify/cooccur/`（極性解析・代表元・影武者消去）
- coalesce が複数の関数 bound を1本に merge する経路（`display/format.rs` の `coalesce_root_fun` /
  `crates/yulang-infer/src/scheme/` のコアレッシング）
- 入力注釈エフェクトの行保持（`[eff; γ]` が `[δ & [;ε]]` に潰れる地点）

## 修正方針
**①（cooccur 本丸）を先に直す。** 本件は同じ cooccur/coalesce の単純化が正しく効けば自然に解ける
見込み（影武者 γ・β の消去 → 2本の継続 arrow が1本に merge → effect 変数が `[β]` に統合 →
入力に `[eff; γ]` が残る）。①を直したらこのテストで第二の witness として確認する。

## 2026-06-07 status

`CompactBounds::Fun` を追加し、不変な関数注釈を compact bounds / display / role constraints /
cooccur / sandwich / selection で扱うようにした後、
`render_compact_results_consolidates_queued_handler_continuation` は期待値どおり通る。

この witness は「関数型が compact bounds から落ちていた」系の問題として一度解けた。
残っている本丸は① `ref_update` の over-merge で、こちらは stored compact scheme が既に潰れた状態で
display に届く。次の調査は `notes/debugs/ref-update-cooccur-overmerge.md` の SCC cooccur trace を入口にする。

## ⚠️ 改竄防止
- 期待値 `α [β & [eff; γ]] -> list<bool -> [β] α> -> [γ] list<bool -> [β] α>` は**ユーザ確定**。
  fix の結果が別の文字列を要求してきたら、**期待値を直さず STOP して報告**（新しい正しい値は
  ユーザだけが確定する）。
- 入力から eff を落としたまま通すのは誤り。注釈エフェクトは開いた行で残すこと。
