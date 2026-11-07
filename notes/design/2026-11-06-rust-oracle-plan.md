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

## 6. 推論の性能設計

この節は型推論器を Rust へ接続する際の実装・証明・計測の計画である。
Rust 推論器、cache、worklist の実装や新しい benchmark 結果を追加したものではない。
以下の Yulang2 の数値はすべて過去の記録であり、Yulang3 の性能予測ではない。
歴史的資料と fixture の参照先は、読んだ `main` の
`d4c8bc8fc8a49173180932cd25921a2c41057354` に固定する。

### 6.1 標準ライブラリの再推論と module scheme cache

**仮説 1 は、標準ライブラリを source から処理する計測では支持される。
cache hit 後の遅さまで標準ライブラリの再推論で説明することはできない。**

| 過去の条件 | 記録 | 読み取れる範囲 |
|---|---|---|
| 6/23、local WSL2/debug、36 files の `check-poly-std examples/showcase.yu` | infer 2.854 s、total 3.215 s | この条件では推論が大半を占める。release の絶対時間とは比較しない |
| 6/26、native、実際の `lib` と二つの entry file、std prefix cache なし | `build_poly` 2.914 s、total 2.956 s | source からの静的解析が大きい |
| 同じ cache 検証の std prefix hit | `build_poly` 215.2 ms、total 256.0 ms | 変わらない prefix の再利用が大きく効く |
| 同じ検証の初回 cache build | `build_poly` 3.216 s、total 3.258 s | artifact の生成・保存があり、初回が速くなる保証はない |

出典は [6/23 baseline][perf-main-baseline] と [6/26 compiled-unit cache][perf-main-cache]。
後者は source unit の dependency closure と std prefix の再利用であり、
単一の「型推論時間」だけを切り取った比較ではない。
同資料には clean な infer 484.8 ms、constraint drain 202.9 ms、
replay accepted 62,792 / duplicate 584,369 も残る。
したがって cache は「同じ処理をしない」対策、solver 改善は「必要な処理を安くする」対策として両方必要になる。
[static-analysis speed plan][perf-main-static] も cache 後の principal unification、
root/body rewrite、名前解決の重複を別に計測し、request を intern して work queue へ送る案を挙げる。
この案を Yulang3 で実装済みとは扱わない。

Lean の根拠を使える場所は次のように限定する。

- [`Inference.Scheme`](../../lean/Yulang/Inference.lean) は `Formula (Option α)` であり、
  `Scheme.instantiate` は保存済み formula の substitution である。
  `Scheme.holds_instantiate` は、任意の model、assignment、scheme、結果の項に対し、
  具体化した formula の充足と、結果 slot をその項の評価値で埋めた元の scheme の充足が同値であることを示す。
  以前の RHS の AST を再び推論しない構成の根拠になるが、制約の複製・freshening・解決が定数時間になる定理ではない。
- [`EOFNoDefaulting.accepted_export_independent`](../../lean/Yulang/EOFNoDefaulting.lean) は、
  **同じ model、型から role term への decode、assignment、interface** と、
  well-formed な二つの impl database を取り、**両方の `finish` が成功したなら**返す closed interface が等しい。
  任意の import/impl 変更後にも module が受理されるとは述べない。
  `accepted_with_more_impls` でも、可視 impl を包含関係に沿って増やすと、
  同じ export で成功する場合と concrete goal が ambiguous になる場合が残る。
- [決定 33](../handoff/2026-11-05-lean-proof-handoff.md) の
  「impl 候補から未確定の型を補わない」を保ち、型 scheme の保存と、
  定義側・呼出側それぞれの scope で必要な role 検査・辞書選択を区別する。
  export が同じであることを理由に、変更された可視 impl での受理検査や辞書の選択を省略しない。
- [`AnnotationFinalization.later_instantiation`](../../lean/Yulang/AnnotationFinalization.lean) は、
  key と slot に decidable equality があり、ある facts/problem/pending が
  `finalize = some history` を満たす場合、任意の formula、substitution、
  model、assignment に対し、保存した history を付けた formula の具体化と、元 formula の代入後の充足が同値である。
  cache に一般化時の検査済み snapshot を保存し、将来の具体化で正の注釈を再検査しない設計の根拠になる。
  本体/SCC の制約が揃う前に snapshot を採ることは許さない。

最初の cache artifact は、exported scheme と qualifier、束縛 slot と捕捉 slot の区別、
nominal/effect の参照先、検査済み annotation snapshot、辞書に関する依存情報を持つ不変の template とする案である。
具体化ごとに量化 slot を fresh にし、捕捉した単相 slot は元の環境との共有を保つ。
module の既存 nominal 宣言の identity は import ごとに別物にせず、
新しいローカル effect family を生成する構築点では、その都度別 identity を割り当てる。
この対応を relocation/freshening 表で明示し、保存した solver の可変ポインタをそのまま復活させない。
この serializer と新旧 module 実行の同値は、上記定理とは別の未完了の義務である。

最初は以下を cache key または検証対象に含め、依存 closure を保守的に無効化する。
依存変更後も再利用できるという細粒度化は、別に十分条件を証明してから行う。

| 変化 | 無効化・再検査するもの |
|---|---|
| module source、構文を変える設定、名前解決・module path、std source | 対応する resolved AST、推論結果と依存 module |
| compiler/IR/scheme encoding の version、型・行・一般化規則、正規化規則 | 解釈が変わる artifact。version 不一致は cache miss とする |
| import の export interface、捕捉環境、SCC 境界・注釈、宣言の identity | 依存 scheme、snapshot、nominal/effect relocation の検証 |
| 定義側または呼出側の可視 impl、impl pattern/制約・辞書本体 | その scope の受理検査と選択済み辞書。型 scheme だけを残せるかは別に判定する |
| generative な構築点の対応、fresh slot 名前空間 | template の freshening 対応。異なる変数・effect family を同一視しない |
| dependency hash、長さ、参照先など artifact 検証の不一致 | cache を使わず source/有効な依存から再構築する |

### 6.2 let の選言を一本へ減らせるか

**仮説 2 の「純粋なら多相」は、そのままでは仕様と一致しない。
構文値の条件を加えても、現在の全 instance 同値の証明から直ちに mono 枝を削除することはできない。**

[spec 4.7](../../spec/04-types.md) は構文上の値だけを一般化する。
`my id = \x -> x` と、純粋でも application である
`my id2 = (\f -> f) (\x -> x)` を区別し、後者は単相のままである。
SCC 内の単相性、全部注釈した binding の例外、再帰中に共有する effect 行も保持する。

[`Inference.generate` と `Typing.letValue_iff`](../../lean/Yulang/Inference.lean) は、
任意の model `m`、環境 `Γ`、RHS `v`、本体 `body`、結果の計算型 `c` に対し、
`v.isValue = true` なら let の型付けが次の**選言**と同値になることを示す。

- `v` に純粋な型が少なくとも一つ存在し、`v` とその捕捉環境を持つ多相 binding で `body` が `c` を持つ。
- ある計算型 `a, b` が存在し、`v` が `a`、その値型を共有する単相 binding の下で `body` が `b` を持ち、
  `b` の値型と `a`・`b` の行の join が `c` 以下になる。

`v.isValue = false` の場合は `Typing.letComputed_iff` により後者だけになる。
参照 generator は選言を formula として保存する。これを DNF へ展開するコストを避けることと、
意味を持つ選言の片方を消すことは別の変更である。
一つ選んだ RHS の型や行だけを見て「pure」と判定しても、RHS の全 instance や捕捉 slot の関係を代表するとは限らない。

最初の Rust 案では RHS の生成結果を不変 DAG/template として共有し、
`isValue` gate を先に適用する。選言は遅延して保持し、分配による eager な DNF の複製を避ける。
template の使用時には fresh slot と捕捉 slot の対応を維持する。
一本化は、対象の具体 model と環境の前提の下で
「mono 枝のすべての instance が poly 枝に含まれる」という subsumption と、
RHS を先に解く手順の principal instance 保存を証明した後の最適化候補に残す。
必要な結論は、任意の対象環境・式・結果型に対する最適化前後の instance 集合の同値であり、
選んだ一つの ground type の一致や数個の利用例の成功では代用しない。
現在この枝削除の証明と Rust 実装は存在しない。

### 6.3 型 node 対の飽和を疎な worklist にする

**仮説 3 は実装方針として妥当だが、hash による同じ仕事の排除と、
union-find による異なる型変数の同一視を分ける。**

[`FiniteHorn.saturate_exact`](../../lean/Yulang/FiniteHorn.lean) は、任意の decidable equality を持つ fact 型、
rule 列、**すべての fact を含む有限の列**、fact に対し、飽和結果への所属と rule からの導出を同値にする。
Rust の sparse worklist は、型 node 対などの同じ有限 universe・同じ規則に対して
`edge ∈ sparseResult ↔ Derives rules edge` を満たすことを目標にする。
node 対の全表や全 rule を実行時に前もって作る必要はないが、未生成の必要な規則を落としてよいという意味ではない。

[`RegularNestedModels.saturate_models_iff`](../../lean/Yulang/RegularNestedModels.lean) は、
反射的・推移的な行関係、任意の有限入力 graph と制約、任意の再帰 model graph と valuation に対し、
飽和後の制約を満たすことと元の制約を満たすことを同値にする。
model graph の観測深さを制限しない。この模型集合の保存を、疎な実装への置換後も要求する。
row checker の exactness や全推論器の principal theorem は、これとは別の接続条件として保持する。

実装は入力 edge を queue へ入れ、既知の ordered node pair を hash set で管理する案とする。
新しい下界・上界が入った pivot の隣接関係、constructor の子、反変位置など、
影響を受ける規則だけを逆引きする。同じ pair の登録は一度でも、後で新しい隣接 edge が来たときの
新しい組合せは処理する。終了時に全規則について閉じていることが completeness の要点になる。
hash collision は実際の key 比較で解決し、可変 graph/row に対する memo は revision/epoch を管理する。
queue の順序を変えても導出集合が変わらないことを先に縛り、replay 回数に上限を設けて受理へ進む変更は行わない。
疎な実装も、必要な node 対自体が密になる入力では二乗個の pair を持ちうる。
worklist を使ったことだけから入力サイズに対する線形時間を主張しない。

union-find は、対象 model で同一視してよい等号と substitution 保存が得られた slot に限る。
単なる subtype edge、同じ bounds の見た目、有限深さで似た graph、局所的な α-renaming を等号扱いしない。
例えば一つの共有変数を二度使う `(a, a)` と、独立した `(b, c)` は同じ template shape でも同じ制約ではない。
不変 constructor node の hash-consing でも、子の identity・捕捉関係・nominal/effect identity を key に含める。

[8/4 調査の最終節 7][perf-main-mutable] は、この区別を直接裏付ける。
warm compiled std/release の mutable reference で、初めは `var` の合成 act を繰り返し推論する費用もあったが、
最終節では template の具体化へ変更済みであり、`var` 27.139 ms → 0.237 ms、
`label_sub` 2.857 ms → 0.359 ms へ改善している。この問題を未修正のままと記述しない。
一方、残る pair 調査では 10,744 候補のうち exact duplicate/trivial が 9,818、
locally-isomorphic-but-globally-distinct が 898、global-alpha-equivalent が 0、novel が 28 だった。
受理された 926 は 898 + 28 であり、「形が似た 898 をまとめる」ことは既存の sharing を失う。
同節で残る replay graph の解決設計は未完了である。
この結果は重複仕事の削減を否定するものではなく、形だけの union-find 統合を正当化しない根拠になる。

### 6.4 無限行の判定に有限行・ray の速い道を置く

**仮説 4 は既存の Lean に一部実現している。追加の速い道も重い判定と同じ意味で縛る。**

[`SemilinearDecisions.checkSpan`](../../lean/Yulang/SemilinearDecisions.lean) は正規化後の空 generator と
単一 generator を先に処理し、一般の場合を carry solver に送る。
`checkSpan_preserves_result` は任意の generator 列と整数重み vector に対して raw 判定との Bool の一致を示す。
[`SemilinearFastInclusion.check`](../../lean/Yulang/SemilinearFastInclusion.lean) は安い十分条件を試し、
[`SemilinearAutomata.checkSubset`](../../lean/Yulang/SemilinearAutomata.lean) はその**成功時だけ**採用する。
十分条件に失敗した場合は NFA の完全な包含判定へ進む。
`checkSubset_preserves_result` は任意の二つの semilinear 集合について fallback と同じ Bool を返すことを示す。
これらは有限個の sample weight だけの一致ではない。

追加する有限集合・単純な ray の checker は `fast : Row → Row → Option Bool` とし、
任意の `left, right, b` について `fast left right = some b` なら
`b = true ↔ Included left right` を要求する。
これにより `some false` も本当の非包含でなければ返せない。対象外は `none` として exact な fallback へ送る。
`SemilinearRowAlgebra.checkSubset_exact` の `Included` は**すべての operation key と整数重み vector**を量化する。
fallback の exactness と合わせて、合成 checker の結果が元の checker と等しいことを証明する。
正の答えだけを証明できる高速検査は、`some true` / `none` だけを返す形で使える。

有限集合は正規化した key/weight の集合照合、単一 ray は base・period の算術で扱う候補とする。
signed weight、零 period、逆向きの ray、多次元、同一 key の成分の union を保存する。
例えば自然数 ray は偶数 ray と奇数 ray の union に含まれるので、
source ray が target のどの一成分にも丸ごと入らないことを理由に false を返してはいけない。
この例は [`SemilinearAutomataExamples.infinite_union_comparison_accepts`](../../lean/Yulang/SemilinearAutomataExamples.lean) にある。
有限な列への切り詰めや、探索 budget 超過を false にする方法は exact checker の代用にならない。
計測では fast hit/未対応、fallback 数、NFA state 数、到達した冪集合 state 数・peak memory を分け、
資源不足は試験の失敗として報告する。言語上の拒否へ読み替えない。
NFA の state 数を `q` とすると、部分集合構成の候補は最大 `2^q` 個になる。
速い道はその構成を避ける対象を増やすためのもので、一般の fallback の最悪計算量を改善する証明ではない。

### 6.5 scheme の簡約と具体化のコピー費用

**仮説 5 は削減の可能性を述べるものとして支持できるが、削減率はまだ分からない。
mutable reference の遅さを scheme clone だけで説明する仮説は、過去の記録と合わない。**

[`TypeSimplification.simplify_instances_exact`](../../lean/Yulang/TypeSimplification.lean) は、
任意の empty/join、反射的・推移的な行関係、固定された行 assignment、
`supported term = true` を満たす型項、期待型に対し、簡約前後の**全 upward instance 集合**が同じことを示す。
値 parameter に独立な行を固定し、record tail は既存の固定 spine の範囲に限る。
正の位置だけにある自由な値 parameter は `never`、負の位置だけなら `any` に置き換え、
両方に現れる parameter の共有は保つ。行 variable を削除する定理や、任意の scheme 制約・presence 型全体の簡約定理ではない。

この簡約で不要になる parameter 出現は、具体化で訪問する参照や生成する slot/制約を減らせる候補になる。
ただし型項を簡約しても `Fin n` の領域そのものが縮むとは限らない。
到達しない slot の除去や再番号付けを行うなら、capture と substitution を保つ対応を別に証明する。
一般化時に一度簡約し、不変 DAG を保存し、具体化では fresh parameter 表と必要な差分だけを作る案を採る。
同じ具体化の中の共有を保ち、別々の具体化の量化 slot は区別する。
捕捉 slot は元の環境との共有を保ち、mutable solver state を別の具体化と共有しない。

コピー費用だけの単純なモデルでは、各具体化が到達 node `m` 個を訪れ、具体化回数が `k` なら
訪問数は `k × m` になる。簡約後に到達 node が `m'` 個なら、同じコピー方式では `k × m'` まで減る。
これは測定した削減率ではなく、共有もsolver処理も含めない費用モデルである。
不変DAG共有はこの全コピーを避ける別の施策であり、残るfresh slot・edge生成と解決の費用を別に測る。
簡約後の具体化を定数時間と呼ぶ根拠にはしない。

[8/4 調査][perf-main-mutable] の get scheme clone は 0.015–0.024 ms、
late stale probe は 0–0.002 ms だった。intrusive tracing 下の後続 get の subtype 処理は
60.658 ms、210.379 ms に達していた。
同じ lower-bound graph と新しい不変位置の変数の接続で replay が増えており、
clone cache の追加だけでこの差を消せる根拠はない。
slot 数、到達 node 数、具体化した edge 数、clone allocation bytes、substitution 時間、
その後の saturation/replay を別々に計測し、簡約前後で何を減らしたかを確認する。
無限行や role obligation を含む保存形式全体への拡張は、それぞれの instance 保存を示した範囲だけ適用する。

2026-11-07 追記: 参照簡約器の全四段階にも計数付きの実装を接続した。
[`TypeSimplificationCheckCost.symbolicCount_value`](../../lean/Yulang/TypeSimplificationCheckCost.lean) は、
任意の二つの `TyTerm (Fin n)` に対し、型・行の等号と record spine を内部で走査する計数付き checker が
既存の `symbolicCheck` と同じ Bool を返すことを示す。全枝を先に評価するため、短絡評価より保守的な参照費用である。
full node 数の合計を `S` とすると、`symbolicCount_size_bound` の上界は `E(S) = (S + 1) × 128^S`。
これは指数時間の素朴な checker に対する安全な上界であり、最適な上界や速さの実測ではない。
各 constructor と有界個の局所検査を一単位とし、明示した Boolean 合成を別に数える。
型全体の等号を定数時間とみなす費用モデルではない。

[`TypeSimplificationCost.simplifyAllCount_value` / `simplifyAllCount_bound`](../../lean/Yulang/TypeSimplificationCost.lean) は、
任意の入力型について、計数付き処理が既存 `simplifyAll` と同じ型を返し、
`totalBudget n M` 以下であることを示す。`n` は有限 parameter 領域の大きさ、`M` は arrow の行を含む入力 node 数。
要求する成功・`supported`・外部 fuel の前提はない。内訳は二回の variance pass、`4n` 個の scalar sandwich、
`n²` 個の merge と候補列の実際の生成・連結である。
[`TypeSimplificationSize`](../../lean/Yulang/TypeSimplificationSize.lean) のサイズ非増大を使い、
各検査を元の `M` で評価できる。merge 用の一時的な joint substitution だけは最大 `3M` となり、
元の型との比較には `E(4M)` を使う。固定 parameter inventory の library 内部の materialization、
識別子の bit cost、allocator の実装費用はこの計数に含めない。
`simplifyAllCount_instances_exact` は既存 `StructuralBase` の instance 保存へも接続するが、
これを presence・mask・regular graph・任意の scheme 制約の canonicalization まで広げるものではない。

### 6.6 最初の benchmark と計測条件

**仮説 6 の通り、実装前に入力と観測を固定する。最初は小さな let/scheme とその scaling を選ぶ。**
以下の個数は固定 SHA の fixture を実読した結果であり、実行時間の新規計測ではない。

| 導入順 | 固定する過去の入力 | 推論で見るもの／接続条件 |
|---|---|---|
| 1 | [`infer_simple.yu`][perf-main-infer-simple]：301 個の identity 関数と 301 個の integer alias、計 602 binding | 関数値の一般化、単相/捕捉 slot、scheme 保存・具体化。未使用 binding も通常の検査対象として残す |
| 2 | [`chain_1000.yu`][perf-main-chain-1000]：2,000 binding → [`chain_2000.yu`][perf-main-chain-2000]：4,000 binding | 定義数を倍にしたときの時間・memory・生成 node/edge/replay の増え方。前半は独立した identity、後半は alias chain |
| 3 | [`loop_recursive_sum_20_discard.yu`][perf-main-recursive-sum] と [`loop_for_no_ref_20_discard.yu`][perf-main-for-no-ref] | SCC、算術/比較 role、range/for の接続後。再帰と for の制御に必要な推論を測り、mutable reference を先に混ぜない |
| 4 | [`loop_for_sum_ref_20_discard.yu`][perf-main-for-sum-ref] と順 3 の二例 | 同じ規模の加算で reference の生成・get/set・effect family と invariant 制約の増分を分ける |
| 5 | [`loop_recursive_20_discard.yu`][perf-main-recursive-list]、[`loop_for_20_discard.yu`][perf-main-for-list] | list/append と mutable list を追加。nominal list、literal、対応する role/constructor の接続後に測る |

loop の `20` は実行時の反復回数であり、推論で body を 400 回展開する規約を追加しない。
最初の二組は inference-only の試験とし、後続 loop でも型推論時間と実行時間を分離する。
Yulang2 の source をそのまま Yulang3 の受理対象だと仮定せず、必要な adapter と対象構文を明記する。
未接続の機能は `unsupported` とし、型エラーや benchmark の成功へ読み替えない。
元の fixture と期待値は保存し、互換入力や追加の反例が必要なら別 fixture として由来と対応を記録する。

計測 harness は次を別々のケースとして持つ案とする。

- cold：std/module cache miss、warm std：std だけ hit、warm module：利用 module も hit、
  invalidation：依存 module 一つまたは可視 impl を変更した後の再検査。
  hit 数、再推論した module/式数、辞書の再選択数を併記する。
- build 済み release binary、compiler/std/fixture の固定 SHA、同じ実行環境を使う。
  compiler 自体の build 時間を推論時間に混ぜず、warm-up と反復数を記録し、中央値・分布を残す。
- parse/name resolution、constraint generation、value saturation、row comparison、role resolution、
  SCC finalization/generalization、simplification、serialize/deserialize を計測する。
  包含関係にある phase の時間は足し合わせない。
- 入力 binding 数、fresh slot/node/edge 数、queue の追加・重複・最大長、bound/replay 数、
  row fast/fallback 数、scheme の共有率と allocation bytes、peak memory を保存する。
  1,000 → 2,000 の名前だけから線形性を仮定せず、実際の binding 数と counter の比を比較する。
- 受理/拒否/unsupported、exported scheme の instance に関する検査、role の選択と曖昧性、
  annotation snapshot、fresh identity の回帰を性能とは別の gate にする。
  ground な例の一致を全 instance 同値の証明と呼ばない。

過去の [`infer_bench.sh`][perf-main-infer-harness] は finalize/commit/compact/instantiate を、
[`static_analysis_bench.sh`][perf-main-static-harness] は `--infer-only` と多数の work/replay counter を分けている。
これらを観測項目の出発点にし、Yulang3 の未実装 CLI を既に動かしたとは記録しない。
[6/23 baseline][perf-main-baseline] では typeclass method の時間に後続 SCC routing が重複計上され、
修正後の method apply は 17.6 ms だった。また drain 呼出を 17,623 → 17,432 に減らしても
work 91,664 は変わらず、時間には揺らぎがあった。
名前の似た counter や単発の wall time だけで原因・改善率を判断しない。

この節で新しい言語仕様の決定は置かない。未完了の中心は module cache の保存/復元の同値、
let の枝削除に必要な全 instance の subsumption、疎な solver と追加 fast path の exactness、
scheme 全体の共有・freshening の保存、そして Rust 推論器の実測である。

## 7. 名前解決・lowering と SCC ごとの selection 確定

追記日: 2026-11-07。Rust 前段の内部設計案であり、surface の意味を追加しない。
根拠は [Yulang2 の lowering 調査](2026-11-07-yulang2-lowering-hotspots.md)、
[決定 29](../handoff/2026-11-05-lean-proof-handoff.md)、上の 6.1・6.6 とする。
Yulang2 の `lower.resolve` は selection の固定点処理であり、名前・path・演算子の解決とは別の段階である。
調査メモの時間は過去の記録であり、以下の設計を実装・測定した結果ではない。

### 7.1 先に宣言と依存を揃え、本体は必要な単位で lowering する

SCC は相互に依存する binding のまとまりである。量化前にこのまとまりを確定する必要があるが、
それは「標準ライブラリ全体の本体制約を先に生成する」ことを要求しない。
次の二段階を分ける。

| 段階 | 保存するもの | 次へ進める条件 |
|---|---|---|
| 宣言・依存の収集 | module/header、宣言 ID、import、可視名、演算子規則、body 内の参照先と依存辺 | 前方参照も含め、その単位から外へ出る依存が列挙されている |
| module/SCC の本体 lowering | resolved body、制約、未確定 selection、注釈の検査対象 | 依存 module の有効な interface があり、依存 binding と同時に解く範囲が確定している |
| SCC の求解と確定 | receiver の最終情報、可視 role index、typed fallback、選択した宣言 ID | 本体・依存・注釈の制約が揃い、確定を後から無効にする依存追加が残っていない |
| 一般化・export | 不変 scheme、捕捉 slot、snapshot、辞書依存、canonical interface の保存候補 | 仕様の値制限・SCC 内の単相性・注釈の条件を満たす |

依存収集では body の**参照**も調べる。header の宣言名だけを登録し、body の forward ref を
未発見のまま量化してよいとはしない。構文 arena 上の軽い参照走査を body lowering と分け、
その結果を後段へ渡す。本体を後で再走査して同じ名前解決をやり直すことを避ける。
module 内の後方宣言は先に割り当てた ID へ結ぶ。相互 import が許される場合は module の循環群を
一つの処理単位とし、循環内の module を個別に先行量化しない。

selection や未確定 path が依存先を持ちうるなら、その依存を未解決のまま SCC を閉じない。
宣言情報で確定できる依存は先に登録し、残る依存を解消するまで該当する確定点を保留する。
既に量化した SCC へ後から辺を足して repair する全体ループは初期設計に置かない。
一方、候補を無条件に全て相互依存辺へ変換すると、不要な SCC 統合で一般化範囲を変えるおそれがある。
依存抽出と SCC 境界の正しさは別に示す必要があり、以下の局所性定理だけからは得られない。

ここまでの依存準備ができた module から本体を処理する。std 全体の body lowering 完了を待たず、
依存 module の確定済み interface を使って量化へ進める設計である。
「header だけなら常に量化できる」という短縮は採らない。

### 7.2 arena・path の intern・持続的な module map

構文、resolved body、型/制約の不変 node をそれぞれ arena に保存し、参照は用途別の ID とする。
source span と元の occurrence ID を node に残し、同じ形の別の式を同じ評価位置とみなさない。
solver が更新する slot/edge は別領域とし、保存済み scheme の node を破壊的に書き換えない。
revision をまたぐ cache は arena の生ポインタでなく、6.1 の relocation/freshening 対応を使う。

識別子の文字列と path の各 segment を intern し、path 全体も segment ID の列として共有する。
同じ綴りの名前でも scope が違えば解決結果は違うため、解決 memo の key には module/scope の
version と必要な import・演算子環境を含める。nominal/effect/role の宣言 ID を文字列だけで同一視しない。
演算子は綴りの intern と fixity/結合順位の解決を分け、構文を変える演算子環境を依存に記録する。
局所変数は resolved binding ID まで落とし、後段で path の文字列探索を繰り返さない。

module と lexical scope の map は、不変 snapshot 間で node を共有する持続的な構造を初期案とする。
binding を追加するたびに module 全体の map を clone する構成を避ける。
更新用の builder は使ってもよいが、公開した snapshot を後から変更しない。
代案は mutable map と rollback log である。単一走査では安い可能性がある一方、並行 module、
注釈の snapshot、cache 再利用との lifetime を別に管理する必要があるため、最初は共有可能な不変境界を優先する。
arena 解放は module/revision 単位に行い、古い snapshot の到達可能性と peak memory を計測する。

hash table の検索を無条件に最悪 `O(1)` とは呼ばない。collision 時も実際の key を比較する。
Lean の抽象コストは table query/update の回数を数えるだけである。
Rust では hash 品質・再配置・key の長さを含めて測る。決定的な最悪上界が必要なら、
balanced tree による `O(log D)` の map 操作などを選び、抽象操作数にその実装費用を掛ける。

### 7.3 method 名の index と、一度だけの selection 解決

可視 scope の snapshot ごとに method 名から候補を引く index を作り、同じ scope の SCC 間でも共有する。
候補は `(role ID, declaration ID)` であり、同じ role の同じ宣言を複数回 import しても一候補である。
解決用の summary は「候補なし・一候補・二つ以上」の三状態を持つ。
診断に必要な宣言位置は別に保持し、複数候補を一覧順の先頭で決めない。
新しい scope snapshot は親 index を持続的に拡張する案とし、各 selection で index を再構築しない。

未知 receiver では index を一度引き、候補なしなら field、一候補ならその role method、二つ以上なら曖昧エラーとする。
既知 receiver では先に field を調べ、存在しない場合だけ既知型用の fallback を使う。
未確定の solver state を途中で覗いた結果を「最終的に未知」と判定しない。
SCC の確定点では、その SCC が所有する selection ID の列を一度走査し、選択した参照を保存する。
後続の scheme 具体化はその参照を使い、receiver が後から具体化したことを理由に選び直さない。

今回加えた Lean の根拠と、その入力境界は次の通り。

| 根拠 | 量化した主張と前提 | この定理が入力として受け取るもの |
|---|---|---|
| [`MethodResolutionLocality.resolve_local`](../../lean/Yulang/MethodResolutionLocality.lean) | 任意の二つの site が `SameFacts` を満たせば、実際の `resolve` の三状態の答えが等しい。未知 receiver は対象名の可視候補が同じ、既知 receiver は対象 field の有無が同じで、欠如時に fallback が同じことが条件 | name、receiver 情報、可視候補、fallback |
| `MethodResolutionLocality.scc_order_independent` | 任意の固定された site 表、SCC ごとの所有 site 列、初期回答表、同じ SCC を含む二つの順序について、実際の `resolve` を呼ぶ `runSCCs` の回答表が等しい | 各 SCC の最終 snapshot。SCC の求解・構築そのものは行わない |
| [`ModuleScheduling.run_legal` / `run_build_exact`](../../lean/Yulang/ModuleScheduling.lean) | 任意の pure compile、source/key、有限 DAG の依存表に対し、依存を先に処理し各 node を一度だけ処理する合法 schedule は実際に完走し、既存の昇順 `ModuleIncremental.build` と同じ artifact を返す。呼出 trace は schedule 自体に等しく、重複しない | node は既に module/SCC にまとめられ、依存先の番号が小さい。compile の入力は source/key と完成済み依存 artifact の順序付き列に限る |
| [`MethodResolutionScheduling.schedule_independent`](../../lean/Yulang/MethodResolutionScheduling.lean) | 任意の pure な snapshot 構築関数 `prepare`、source/key、依存表、同じ node 集合の二つの合法 schedule に対し、実行中に構築した snapshot と全三状態の selection が等しい。compile は `prepare` の返す各 site に既存 `MethodResolution.resolve` を適用する | 最終 snapshot 自体は前提にしない。`prepare` が source/key と完成済み依存 artifact だけから snapshot を作る契約が入力になる |
| [`MethodResolutionCost.resolveCount_value` / `resolveCount_bound`](../../lean/Yulang/MethodResolutionCost.lean) | 任意の site で計数付き resolver の値が既存 `resolve` と等しい。未知 receiver は可視 role 数 `R` に対し `1 + 2R` 以下、既知 receiver は型の構文 node 数 `V` に対し `1 + V` 以下 | table query、候補比較、record spine の訪問、dispatcher を抽象単位とする |
| [`MethodResolutionIndex.indexedResolve_exact`](../../lean/Yulang/MethodResolutionIndex.lean) | 任意の有限 declaration catalog、可視 role 列、名前、receiver、fallback について、同じ `(role, name)` の宣言が一致するなら、index による解決とその catalog を読む既存 `resolve` が等しい | catalog の関数性。重複 import と任意の列順を許す |
| `MethodResolutionIndex.resolveNamesCount_exact` / `resolveNamesCount_bound` | 任意の名前列に対する一回の index 構築と全 query の値が元の `unknown` の結果列に一致する。可視宣言数 `D`、名前数 `N` に対し `3D + 2N` 抽象操作以下。上界自体は catalog の関数性や解決成功を仮定しない | 可視宣言に絞った入力。visibility filtering と map の内部実装費用は別 |

`buildIndex_ext` / `buildIndex_perm` は、catalog の順序と同じ entry の重複が答えを変えないことも示す。
`runCount_bound` は schedule の各 site の上界の和を取り、同じ site を二度処理すれば二度分を数える。
実際に一回だけにするには、Rust の site 所有表・queue が重複を入れないことを別に検査・証明する。

したがって、**凍結済みの snapshot の selection を解くための全体固定点ループは不要**である。
さらに `ModuleScheduling` / `MethodResolutionScheduling` によって、有限 DAG の抽象モデルでは
依存 artifact の計算、そこからの snapshot 構築、実際の selection 解決まで処理順序に依らないことが得られた。
各 step は依存 artifact の存在と自身の未処理を実検査してから compile を呼ぶ。
合法性は ID と依存辺から定義し、推論成功や共通の最終 snapshot を仮定しない。

source 全体へ適用するには、なお二つの接続が要る。第一に、source の参照先を列挙し SCC をまとめる処理が、
後から確定済み SCC へ必要な依存辺を追加しない完全な依存表を返すこと。
第二に、任意の source SCC と、その完全な依存 artifact を持つ solver state に対して、
実際の SCC 確定処理の結果が、同じ source/key と順序付き依存 artifact を引数にした
`prepare` の結果で表せること。他の SCC の処理履歴を入力として参照しない形へ移す必要がある。
選択に伴う制約追加が既に固定した receiver・可視候補・fallback を変えないことも、この確定契約に含める。
この具体実装との対応を示さずに、未確定 receiver を一回見ただけで selection を固定する最適化は適用しない。

### 7.4 module の量化・interface cache の境界

量化済み module は scheme と qualifier、捕捉 slot、注釈 snapshot、宣言 identity、辞書依存を保存する。
6.1 の cache key・無効化表をすべて維持し、依存 interface の hash だけへ縮小しない。
依存の変更で影響を受ける module の判定には、import 先を指す辺と、その逆向きに保持した利用者の辺を区別する。
変更 module から利用者側へ到達する範囲を再検査候補にし、同じ interface が得られた場合の伝播停止は
source、scope、impl/辞書、設定など別の依存も不変である場合にだけ認める。

公開型の等しさは [4.7b](../../spec/04-types.md) の要求による等価と
[7.4b](../../spec/07-display.md) の標準形を基準にする。
同じ構成子の union を成分ごとにまとめるだけでは、型変数・mask・regular graph・scheme 制約全体の
等価を決める canonical interface が完成したことにはならない。
全 interface に対する「要求で等価であることと canonical encoding が一致することの同値」は、
serializer の保存性とともに別の未完了の接続として残す。
hash は canonical encoding の参照を探す手段であり、collision を型の等価とみなさない。

`accepted_export_independent` の適用条件は 6.1 のままとする。
同じ model・decode・assignment・interface に対し、well-formed な二つの impl database の
**両方で `finish` が accepted** なら closed interface が等しい。
可視 impl の追加が新たな曖昧性を作る可能性は残るので、この定理だけで受理検査や辞書再選択を省かない。
module 単位の量化をこの定理だけで導くこともせず、7.1 の依存/SCC の条件を別途満たす。

### 7.5 前段を導入するときの最初の benchmark

6.6 の let/scheme fixture を維持し、その次に lowering 調査の 4 節に対応する次の三群を加える。
これらは入力生成と観測の設計であり、Rust runner や新しい測定値を追加したものではない。

| benchmark 群 | 最初に変える入力軸 | counter と判定したいこと |
|---|---|---|
| `selection-scaling` | selection 数 `N = 128, 256, 512, 1024`。可視 role/宣言数はまず固定し、必要なら次に `R` / `D` を変える | 解決した site 数、候補走査・比較数、index 構築数、query 数、全 selection 再走査数、時間・allocation。`N` を倍にしたとき、処理回数が二倍か四倍かを識別する |
| `lowering-components` | 同じ binding/body 数で、繰り返す path と異なる path、path 長、import alias 数を変える | parse、名前/path/演算子解決、制約生成の時間を別々に記録。intern の hit/miss、共有 map の追加 node、解決済み参照の再利用、生成 node/edge 数も取る |
| `module-invalidation` | chain・fan-out・独立 sibling を持つ module 群の一 module だけを変更する | body を再処理した module 数、interface を再検査した module 数、辞書再選択数、cache hit/miss。全再計算と増分再計算の受理結果・interface を照合する |

selection 群は、未知 receiver の候補 0 / 1 / 複数、重複 import、既知 receiver の field 優先と
欠如時 fallback を含める。既知 receiver の field spine 長は別の入力軸にする。
SCC 列を入れ替えたときも答えを保存し、重複のない所有表で「処理 site 数 = 入力 site 数」を検査する。
`3D + 2N` は index 構築と未知 receiver query の抽象計数に対する定理であり、
parser、dependency collection、可視性の絞り込み、nominal/inherent lookup、solver 全体の時間上界ではない。

増分群は、(a) export を変えない body 編集、(b) export を変える編集、(c) 可視 impl/辞書だけの変更を分ける。
独立 sibling の本体再処理が増えていないか、変更を必要な利用者へ伝えたかを別々に数える。
canonical interface が未接続の段階は、接続済み断片の構造一致と結果の検査だけを行い、
全言語の interface 同値を実証したとは扱わない。

計時は 6.6 と `rules/performance.md` に従い、最初は一つの比較 harness で baseline/candidate を組にする。
通常は warm-up 一回と測定三組、中央値と範囲を残す。最初から全入力軸の直積を測らない。
上の四つの `N` は二次走査との区別が必要な場合の scaling 用であり、counter で解ける問題は計時を増やさない。
包含する phase の時間を足さず、Rust の高速化を Lean の抽象操作数だけから実測済みと結論しない。

[perf-main-baseline]: https://github.com/momota1029/yulang/blob/d4c8bc8fc8a49173180932cd25921a2c41057354/notes/benchmarks/2026-06-23-hardening-baseline.md
[perf-main-cache]: https://github.com/momota1029/yulang/blob/d4c8bc8fc8a49173180932cd25921a2c41057354/notes/benchmarks/2026-06-26-compiled-unit-cache-speedup.md
[perf-main-static]: https://github.com/momota1029/yulang/blob/d4c8bc8fc8a49173180932cd25921a2c41057354/notes/design/static-analysis-speed-plan.md
[perf-main-mutable]: https://github.com/momota1029/yulang/blob/d4c8bc8fc8a49173180932cd25921a2c41057354/notes/design/2026-08-04-mutable-reference-performance-investigation.md
[perf-main-infer-simple]: https://github.com/momota1029/yulang/blob/d4c8bc8fc8a49173180932cd25921a2c41057354/bench/infer_simple.yu
[perf-main-chain-1000]: https://github.com/momota1029/yulang/blob/d4c8bc8fc8a49173180932cd25921a2c41057354/bench/chain_1000.yu
[perf-main-chain-2000]: https://github.com/momota1029/yulang/blob/d4c8bc8fc8a49173180932cd25921a2c41057354/bench/chain_2000.yu
[perf-main-recursive-sum]: https://github.com/momota1029/yulang/blob/d4c8bc8fc8a49173180932cd25921a2c41057354/bench/loop_recursive_sum_20_discard.yu
[perf-main-for-no-ref]: https://github.com/momota1029/yulang/blob/d4c8bc8fc8a49173180932cd25921a2c41057354/bench/loop_for_no_ref_20_discard.yu
[perf-main-for-sum-ref]: https://github.com/momota1029/yulang/blob/d4c8bc8fc8a49173180932cd25921a2c41057354/bench/loop_for_sum_ref_20_discard.yu
[perf-main-recursive-list]: https://github.com/momota1029/yulang/blob/d4c8bc8fc8a49173180932cd25921a2c41057354/bench/loop_recursive_20_discard.yu
[perf-main-for-list]: https://github.com/momota1029/yulang/blob/d4c8bc8fc8a49173180932cd25921a2c41057354/bench/loop_for_20_discard.yu
[perf-main-infer-harness]: https://github.com/momota1029/yulang/blob/d4c8bc8fc8a49173180932cd25921a2c41057354/bench/infer_bench.sh
[perf-main-static-harness]: https://github.com/momota1029/yulang/blob/d4c8bc8fc8a49173180932cd25921a2c41057354/bench/static_analysis_bench.sh
