# Rust AST oracle の段階的導入計画

Status: **Draft**（実装計画。言語仕様の決定を追加しない）

Date: 2026-11-06
Scope: Lean の既存評価器を基準にする Rust 参照実装と、その後の最適化実装の検証境界。

## 1. 目的と最初の境界

Rust で構文木を直接評価する、小さく追跡可能な oracle を作る。
Lean と同じ入力を独立した実装で実行し、結果の値・失敗・訪問列を比較する。
後続の Perceus、evidence passing、Cranelift による実装も同じ観測へ照合する。
このメモは oracle 本体、JSON runner、差分試験器をまだ追加しない。

根拠は [handoff の決定一覧](../handoff/2026-11-05-lean-proof-handoff.md)、
[翻訳表](2026-11-06-surface-to-core-translation-draft.md)、
[cheatsheet](../cheatsheet/2026-11-06-yulang-cheatsheet.md)、[Lean README](../../lean/README.md)。
以下の「段階」は実装順の提案であり、未決定の意味論を仮決定するものではない。
仕様の空白は `notes/questions/2026-11-06-open-questions.md` に切り出す。

最初の入力は `Inference.Expr` の `SourceDataRuntime.Supported` が覆う data 部分とする。
変数は de Bruijn index、field/tag は `Nat`、環境は値の列をそのまま持つ。
最初から surface parser、型推論、nominal constructor 全体を oracle に混ぜない。
parser からこの核までの翻訳正当性は、独立した未完了の義務として残す。

| 形 | 最初の Rust の動作 | 基準 |
|---|---|---|
| `var`, `lit`, `letE` | 環境参照、base tag 値、右辺を一度だけ評価して保存 | `SourceDataRuntime.eval` |
| `pair`, `fst`, `snd` | 左から右、投影前に対象を評価 | 同上 |
| `emptyRecord`, `record`, `field` | head、tail の順。先頭 field が勝ち、隠れた payload も評価 | `Fields.insert`, `eval` |
| `recordDefault` | base、fallback の順に厳格評価。存在時は元の field、欠如時は末尾へ追加 | `Fields.insertDefault`, `eval` |
| `variant` | payload を評価して tag と値を保持 | 同上 |
| 未対応形 | 明示的な `unsupported`。成功・型エラーと区別 | `SourceDataRuntime.Error` |

現在の `.lit .int` 等は**中身を持たない base tag**である。
任意精度整数・小数・文字列の演算や literal 比較を、この段階で実装済みとは扱わない。
record の保存値は field の順序を持つ列。JSON object や unordered map で代替しない。
`recordDefault` の strict fallback は決定 44 の構築式である。
`spec/03b` の「field がないときだけ評価する pattern default」へ広げない。

## 2. Lean と Rust の差分試験

### 2.1 共通入力と観測

`data-v1` として version 付きの tagged JSON を一行一件読み書きする計画とする。
入力は `{version, caseId, environment, expression}`、出力は
`{version, caseId, trace, result}`。これは試験用 wire format の提案で、surface 構文ではない。

`expression` と値の各 constructor は明示的な tag と引数を持つ。
`Nat` は JSON number の精度に依存しない十進文字列とし、列の順序を保存する。
`result` は `ok(value)` または `error(tag, payload)` を区別する。
`unsupported`、`unboundVariable`、`expectedPair`、`expectedRecord`、`missingField` を保持する。
不正 JSON・未知 version・不正 encoding は protocol error とし、言語の runtime error に混ぜない。

`trace` は当面、`SourceDataOrder.Trace = List Expr` の各式を完全に符号化した列とする。
訪問は式への入口で記録し、失敗した場合は失敗点までの prefix を返す。
同じ構造の部分式が二箇所にあるため、構造 hash を occurrence ID とみなさない。
node ID だけへ縮約する方式は、ID と元の trace の対応を別途証明してから導入する。

比較は decode 後の constructor・列の要素・error payload の完全一致で行う。
この段階の record 比較は保存値の一致であり、field を sort して差を消さない。
入力環境にも ill-shaped な値を許し、成功例だけでなく失敗と prefix を検査する。
生成器は構文サイズ・環境サイズを制限し、縮小器は式と参照環境を一緒に縮小する。
タイムアウト・OOM・runner crash は別結果とし、言語上の発散という結論を出さない。

### 2.2 Lean runner を作る道筋

`lean/OracleDataMain.lean` を追加し、JSON decode → `SourceDataOrder.run` → JSON encode とする。
同じ評価器を呼ぶだけに留め、比較しやすい別 evaluator を runner 内に再実装しない。
`lean/lakefile.toml` に以下の executable target を追加する計画とする。

```toml
[[lean_exe]]
name = "oracleData"
root = "OracleDataMain"
```

`lake build oracleData` で `.lake/build/bin/oracleData` を生成する。
開発時は `lake env lean --trust=0 --run OracleDataMain.lean` からも同じ `main` を動かす。
既存の `RunSourceDataOrder.lean` は固定例の runner であり、この JSON 入出力はまだない。
decode/encode の round-trip を証明できる範囲から証明し、残りは実行試験の境界と記す。

| 既存の根拠 | この計画で使う主張と限界 |
|---|---|
| `SourceDataOrder.evaluates_iff_run` | 任意の環境・式・trace・結果について、独立した `Evaluates` 判断と実行結果が同値 |
| `SourceDataOrder.run_result` | 任意の環境・式について、trace evaluator の結果成分は `SourceDataRuntime.eval` と等しい |
| `SourceDataOrder.Evaluates.deterministic` | 同じ環境・式の二つの評価判断は、trace と結果がともに等しい |
| `SourceDataOrderLaws.shadowed_field_keeps_visits` | 隠れた field を保存値から消しても、その評価訪問は消さない |
| `SourceDataOrderLaws.default_present_keeps_fallback_visits` | field 存在時も fallback の訪問を残す |
| `SourceDataOrderLaws.let_two_reads_evaluates_rhs_once` | 値の二回参照は右辺の二回評価にならない |
| `PresenceDataSafety.typing_evaluates` | 環境整合と presence data の型付けを前提に、対応する型の値へ評価される |

各法則の局所前提は定理本体を維持する。Rust に無条件の全言語保証を移さない。
根拠の本体は [SourceDataOrder](../../lean/Yulang/SourceDataOrder.lean)、
[order laws](../../lean/Yulang/SourceDataOrderLaws.lean)、
[PresenceDataSafety](../../lean/Yulang/PresenceDataSafety.lean) にある。

回帰 seed は hidden field の失敗、存在する default の失敗、base の失敗、
record 以外の base と失敗 fallback、未使用 let の失敗、pair 左側の失敗を含める。
期待値を Rust 出力から自動更新して通すことはしない。
Lean と Rust で評価ロジックを共有せず、wire schema と生成入力だけを共有する。

## 3. 段階と Lean の根拠

各段階は一つずつ小さな commit にし、既存の theorem・runner・差分 seed を維持する。
共通の全言語 evaluator が既にあるとは扱わず、接続できた形を明記する。

| 段階 | oracle へ加えるもの | 既存の Lean の根拠 | 先に閉じる接続 |
|---|---|---|---|
| 0: data | 上記 AST、値、失敗、訪問列 | `SourceDataOrder.evaluates_iff_run`, `run_result`; `PresenceDataSafety.typing_evaluates` | wire round-trip、Rust 実装との実行比較 |
| 1: 関数・application | closure、環境、strict な引数評価と値の保存 | `StrictApplication.compile_correct`, `infer_exact`, `inferred_operationally_valid`; `OperationalTyping.typing_sound` | untyped source → shape-resolved core と data evaluator の接続 |
| 2: effect と handler | request、複数 operation arm、value arm、shallow/multi-shot resume、保護・解除 | `Directed.Computation.shallow_resume_is_original`, `noncapture_of_uncapturable`; `HandlerPermissions.check_exact`, `capture_after_check` | source の複数 arm、guard/dispatch、型付けと signed weight の一体化 |
| 3: role 辞書 | 選択済み impl を明示的辞書で渡す | `RoleDictionaries.elaborate_success_iff`; `ModuleDictionaries.useEvidenceAt_preserves`, `crossing_file_preserves_dictionary` | source の method body 評価、辞書引数の elaboration |
| 4: cast | pure な変換と保存された nominal 構築点への挿入 | `PureCasts.insert_requestTree`, `wrapper_preserves_latent_row`; `NominalConstructions.plan_retains_original_sites`, `resolved_site_boundary`, `eof_no_boundaries` | struct/enum/list の runtime と決定 25 の保留境界の接続 |
| 5: 型推論 | inferred / rejected / unsupported の区別、presence-aware 制約 | `SourcePrincipalInference.infer_instances_exact`, `infer_rejected_iff`; `PresenceDataCompatibility.eval_success_iff_infer` | required-field の旧主型 scheme と presence-aware data の保存的 embedding |

### 3.1 関数と継続の観測を増やすとき

`OperationalTyping.eval` の `.app` は引数**計算**を関数へ渡す。
通常の source application の strict な意味論として、その一行を直接移植しない。
`StrictApplication` の force/let 境界と決定 42–43 を使い、関数式と引数の順序を保持する。
関数値や Lean の関数としての resumption を、JSON 上で直接比較することはできない。
有限の適用入力・response script を与えた観測を比較し、全関数同値を試験で証明したとはしない。

最初の handler runtime は不変の環境と複製可能な継続 frame を持つ案とする。
一つの catch が全 operation arm を同時に持つ形を保存する。
operation ごとの handler 入れ子へ変換して済ませない。再開後の外側 handler が異なりうる。
選択 arm は元の continuation を受け取り、二回以上 resume できる。
mutable な外界の巻き戻しを multi-shot の意味に追加しない。外界は試験用 adapter に分ける。

保護と解除の重みは符号付き整数を保ち、正・零・負を単なる protected flag に潰さない。
捕捉条件は該当 key と必要な各 scope の零重みである。
決定 41 の permission mask 検査は静的な拒否として保存する。
許可されない arm を消して評価に進むことで拒否を代用しない。
`HandlerPermissions.checkedHandleIncoming_success_iff` と `checkedHandleIncoming_error_iff` を使う。

`ErrorEffects.wrap_up_exact` は keys と constructor の対応・非重複を前提とする。
`JunctionEffects.run_is_shallow` は library helper と shallow handler の一致である。
これらを handler 段階の seed とし、任意の source `if`/catch の翻訳正当性へ広げない。
list の runtime は `Fold`・`Index` の role 規約、literal 内容は比較規約が接続できた順に追加する。
未決定部分を便宜的な Rust 標準型の振る舞いで埋めない。

### 3.2 presence と推論

`SourcePrincipalInference` の optional/default 未対応を成功へ読み替えない。
まず required-field 型を presence 側へ埋めたときの型付け保存・反映、
環境と substitution の対応、principal instance 集合の対応を独立に証明する。
その後に optional field・default の制約を足す。型の印字一致を意味的同値の代用にしない。
この順序は統合の提案であり、現時点の Simple-sub 全体の正当性保証ではない。

## 4. 速い実装への道

oracle は単純な所有値または不変共有値で始め、再利用や allocation 削減を正解判定に混ぜない。
最適化系には評価順が明示された別 IR を置き、source の観測点を対応づける。
内部命令の列を source AST の訪問列と直接比較せず、source 観測への射影を定義する。

[Perceus 原論文](https://www.microsoft.com/en-us/research/wp-content/uploads/2020/11/perceus-tr-v4.pdf) は
明示的制御フロー上の精密な参照カウントと reuse を扱う。対象条件、とくに循環の扱いを保つ。
導入順は data allocation の参照カウント → drop 特殊化 → 一意性を確認した reuse とする。
各変換の前後を oracle と比較し、可能な局所変換から Lean で観測保存を証明する。
multi-shot 継続に保持された環境を一意と誤認しないことは、別の所有権不変条件になる。
Perceus の論文の証明を、Yulang の heap/継続実装へ自動的に移したとは扱わない。

[evidence passing 原論文](https://www.microsoft.com/en-us/research/wp-content/uploads/2021/08/genev-icfp21.pdf) を
handler 探索の実装候補として参照する。まず handler evidence を明示引数にして dispatch だけ置換する。
辞書の選択、permission mask、signed weight、shallow resume の境界をそのまま保つ。
Koka の実装方式の採用を、Yulang の言語意味論の採用と取り違えない。

[Cranelift](https://cranelift.dev/) は IR から機械語を生成する Rust 製 backend として候補にする。
最初は scalar/data の直線的なコードと既知の runtime 呼び出しから lowering する。
closure、継続、dictionary、cast の表現は oracle で固定された観測へ照合する。
ABI、整数表現、allocation、例外・継続の呼出規約を境界に置く。
backend の採用だけで、source から機械語までの検証が完了したとはしない。

## 5. 信頼する範囲を小さく保つ

| 区分 | 対象 | 得られる保証／残る境界 |
|---|---|---|
| Lean で検証済み | 独立評価判断と evaluator の対応、既存 typing/safety/order/cast/dictionary 定理 | それぞれの型・前提・対象 AST の範囲。Rust や未実装翻訳には自動伝播しない |
| 差分試験で縛る | Rust oracle、JSON codec、source adapter、最適化 IR、runtime、Cranelift 出力 | 試験した入力・response script の観測一致。普遍的正当性の証明ではない |
| 明示して信頼する | Lean kernel と許可された標準公理、Lean/Rust compiler と runtime、OS、hardware、外界 adapter | 証明検査と実行の基盤。native executable が kernel 内で評価されたとは扱わない |

`Audit.lean` の既存 allowlist（`propext`, `Quot.sound`, `Classical.choice`）を維持する。
`sorry`、追加公理、`native_decide` で Rust 比較や翻訳の穴を埋めない。
各 push 前に `lake build` と `lake env lean --trust=0 Audit.lean` を実行する。
runner 追加後は、実行ファイルの build・固定 seed・生成差分試験の結果も別に記録する。
証明と試験が対象にした範囲を README の「示さないこと」と `spec/10` の残る義務へ反映する。

最初の実装完了条件は data-v1 の runner、独立 Rust evaluator、
上記の成功・失敗 seed、trace/result 一致、再現可能な縮小反例の保存までとする。
関数・effect・role・cast・型推論の未接続部分は、この完了条件に含めない。
