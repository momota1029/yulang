# ChatGPT Pro への依頼(復旧): 落ちたセッションの続きを、リポジトリの状態から再開する (2026-11-08)

前のセッションは、約 1 時間走ったあと、**完全に再起動できなくなった**。セッション内の記憶と、未 push の作業は失われた。残っているのは `integration/m1-final` に push 済みの状態だけ。
ここから**新しいセッションとして**続きを進める。前のセッションの会話は引き継がれない。この文書とリポジトリの文書だけが頼りになる。
再発を避けるため、**小さな単位(補題一つ、定理一つ)ごとに commit と push**を必ず行う。30 分以上 push しない状態を作らない。

```text
yulang の integration/m1-final ブランチ(https://github.com/momota1029/yulang)を pull して、続きを進めてください。
前のセッションが落ちたので、新しいセッションとして再開します。最初に notes/handoff/2026-11-08-chatgpt-prompt-m1-recovery.md を読み、そこに書いてあるとおりに進めてください。
途中で私に確認を取らずに、できるところまで自走し、小さな単位(補題一つ・定理一つ)ごとに commit と push を繰り返してください。30 分以上 push しない状態を作らないでください。
新しいブランチは切らず、integration/m1-final をそのまま続けてください。yulang3 と integration/types には push しないでください。
最初に、cd lean && lake build --wfail && lake env lean --trust=0 Audit.lean が通ることを確かめてください。
```

## 状態

- ブランチ: `integration/m1-final`。前のセッションの最後の作業 commit は `3366d509b`(08:53、「Validate closed record field-spine agreement with a finite check」)。その後の commit は、ユーザー側の決定の記録(文書だけ)。
- 前のセッションは約 54 commit を積んだ。Lean は 28 個ほどの新モジュール。検証済み: 8:45 時点の先頭は `lake build --wfail` が 1034 jobs で exit 0、`Audit.lean` も exit 0(許可リスト 75,427 宣言)。それ以後の 7 commit は、新しいセッションの最初のビルドで確かめる。
- 検証が通らない場合は、まず通す(直すか、壊した最後のモジュールを退ける)。それが最優先。

## 最初に読むもの(この順)

1. `notes/handoff/2026-11-08-chatgpt-prompt-m1-interval-continuation.md`(元の依頼。区間モデルが正本であること、作業 0・B4・B5/B1・B2・B3 の意味、進め方)
2. `notes/reference/2026-06-02-role-system-yulang2.md`、`2026-06-06-invariant-type-sandwich-yulang2.md`(旧世代の正しい区間規則)
3. `notes/handoff/2026-11-08-m1-model-fidelity-audit.md`(作業 0 の結果。前のセッションが書いた)
4. 前のセッションの継続結果: `2026-11-08-m1-b2-continuation.md`、`…-b3-continuation.md`、`…-b5-continuation.md`、`notes/design/2026-11-08-b4r8-interval-model.md`、`…-b5-interval-invariance.md`。**各ファイル末尾の「正確な残り」が、続きの起点**
5. `spec/06-roles.md` 6.3〜6.5 と、`spec/04-types.md` 4.3・4.6(ユーザーの決定。下に一覧)
6. `notes/handoff/2026-11-07-m1-completion-contract.md`(E1/E2、ワーカーの契約)の**最後の二つの節**(「E2 は終わりではない」、モデルの忠実性の監査)
7. `notes/questions/2026-11-08-m1-interval-statement-alignment.md`(承認済み。全体 statement の更新)

## 前のセッションの後に決まったこと(ユーザーの決定。文書に書いてある)

- **E7: `x | catch:` の左辺は計算のまま渡り、handler に届く**(`x | catch: ...` は `catch x: ...` と同じ)。(`spec/03-expressions.md` 3.7・3.9)

- **K1(receiver の無い role member の整合条件)は、宣言で何も拒否しない**: 型引数を決める手がかりは呼び出しの引数と戻り値であり、型が分かるまで遅らせる。未解決の制約は、既存の規則（6.3）どおり、ファイルの終わりまで待ち、決まらなければそこでエラー。(`spec/06-roles.md` の K1)

- **case の静的 effect 行は、全 arm の guard と body の行を合流する(保守的)**: 先行する arm が必ず合って到達しない arm の effect も、行に含める。(`spec/03-expressions.md` 3.7、`notes/questions/2026-11-07-b2-unreachable-case-effect-row.md`)

- **optional field の照合は合法**: 入力の型で field が optional でも、default なしの `{port: p}` で照合してよい。field が無ければ miss して次の arm へ進む。(`spec/03b-patterns.md` 3b.3、`notes/questions/2026-11-07-b2-optional-field-case-pattern.md`)

- **保留された境界は、不変な型引数にだけ付く**: 共変の `box { value: id_value }` は保留せず `box user_id` になり、後から共変で cast される。`list` のような不変な引数は、`'_a` を保留して構築位置へ遡って cast する。(`spec/06-roles.md` 6.5)

- **全体 statement の更新(承認)**: 旧定理(点モデル)は保存し、区間・遅延・宣言別 variance を明示した別の全体 statement を、B4 と B5/B1 の E1 の対象にする。その E1 は、元の B4・B5/B1 の完了として数える。(`…-interval-statement-alignment.md`)
- **「無限に入れ子」の判定規則(候補 1)**: 宣言群から引数ごとに、使われなければ `unused`。使われる引数は、cast が値を今その場で辿る道(field・variant payload・tuple)の上に反復できる nominal 展開の cycle があれば不変。関数を包む位置で即時に辿る道を切る。結果: `box`・`box2`・`reset`・`stream` は共変、`chain`・`left`/`right` は不変、`phantom` は `unused`。理由は型変換のコスト。(`spec/06-roles.md` 6.5、`…-b5-declaration-recursive-variance.md`)
  - 証明義務: (1) 宣言から表を求める `deriveVariance` が、独立した使用・極性・再帰の判断と iff。手渡しの表を正しいと仮定する形は不可。(2) その表に従う構造 cast の費用上界(wrapper の作成と一回の呼び出しを区別する)。
- **合流した payload の分割の問いは起きない**: 共変の引数(`box`)は合流して一つの型になる(`box int | box bool` は `box (int | bool)`)。不変の引数(`list`)で別々の型を合流させると、構築の時点で型エラー(区間が矛盾する)。head の変数は、合流後の payload を丸ごと捕捉する。したがって、有限 cover などの案は不要。(`spec/06-roles.md` 6.3、`…-b4r7-nominal-alternative-capture.md`)
- **拒否と曖昧性の優先順位**: 拒否が先。一つでも再帰型の中身を見る候補があれば、他の安全な候補がいくつあっても、「再帰型のため解決できない」と拒否する。(`spec/06-roles.md` 6.3 の K2、`…-b4r2-rejection-priority.md`)
- **E2(反例)は終わりではない**: 反例が出たら、反例を排除して実際の solver の規則に合う定義を設計し、その定義の上で証明する。終わりに数えるのは、元の statement の E1、または設計し直した statement の E1(修正の根拠つき)。設計が決まっていない選択を含むときは、候補を 2〜3 個、Yulang の例つきで `notes/questions/` に出し、決めずに進められる部分を証明し続ける。
- **区間の端点が不変な引数を持つときは、内側でも同じ規則を再帰的に適用する**(2026-11-08, 復旧後に確定): 併合で生まれる交差条件は通常の部分型制約として解き、端点の `list (list int)` と `list (list float)` のような入れ子では、内側の `list` の区間がまた併合される。深さの上限はない。B4 の区間生成が入れ子を再帰で扱うかを確かめる。(`spec/06-roles.md` 6.5)
- **不変な引数の中にある共変・反変の位置は、不変として扱ってよい**(2026-11-08): `list` の不変な引数の内側の `box` の共変な引数は、そこでは共変 cast せず不変な区間として持つ。外側が不変なら、内側の宣言上の向きは区間の扱いを変えない。(`spec/06-roles.md` 6.5)。B5 の variance 表と cast 費用の接続で、入れ子の中の向きがこの規則と合うか確かめる。
- **不変な引数は、区間か、区間の両端が同じ constructor で確定した形のどちらか**(2026-11-08, 型の単純化): 不変な引数の区間の上界・下界がどちらも `box` なら `box` が確定し、中身はまた不変な区間になる。`list` の区間 `(box A, box B)` は `list (box (A, B))`、例 `list (box (int | 'a & float))`。不変は入れ子になる。(`spec/06-roles.md` 6.5)。B4 の区間生成・併合が、両端の head が一致したときにこの単純化を行い、中身へ再帰するか確かめる。
- **record の尾**: `..'a` は、具体的な record が来て、先頭の field が引かれたときに決まる引き算の結果。未解決のうちは解かず保留する。
- **rank 2 の struct field**: struct の型引数に無い型変数が field の型に出ると、その field の中で全称量化される。`ref` の field は `run` だけで、`get` は `sub: r.run \a -> { return a; ... }` で作る。(`spec/04-types.md` 4.6)

## ユーザーに残っている問い(決めずに、局所の補題や場合分けで進める)

- A2 の契約の修正案(`2026-11-07-a2-canonical-computability.md`)。
- 区間 resolver の停止の尺度: 遅延だけでは、子の下界の head が毎回分かっている増大鎖は止まらない。Paterson 的な下降が区間モデルで要るかを示す(前のセッションの監査に書いてある)。これは問いではなく、証明の課題。

## 続きの作業(前のセッションの「正確な残り」から)

優先は、全体 statement の更新の下で、B4 と B5/B1 を E1 まで閉じること。
- **B5/B1**: `deriveVariance`(宣言から表を求める iff)と、構造 cast の費用上界。続いて、同じ表を full nominal carrier の subtype・construction・cast judgment と元 source generator に接続する。旧 all-invariant iff を一般 nominal theorem として流用しない。
- **B4**: 区間 resolver の実際の下降の尺度(上のとおり)。全体 statement の定義(pending/selected/ambiguous/rejected、生成した全 where 子と ordinary 制約、有限辞書)を Lean で書き、局所の補題(区間生成、閉じた record の残り、準備完了の鎖)をその部品として接続する。
- **B2**: 一般の source 式から実行 prefix を作る producer と adequacy(B3/B5 との橋)、presence の合法性。
- **B3**: 検証済み source 宣言全体の iff(旧 value-local 表だけでなく、mixed な型・行 local 表全体の再帰、family 引数の区間照合、visible effect・permission・hygiene の lowering)、返却 scheme の回収、arrow の cover(depth ごとの cover は固定 branch にできない既存の反例がある)。
- B6(公開入口 `Core.infer` への統合)は、作業 0 の不一致が片付き、上の目標が閉じるまで始めない。

## 進め方

- **spec の例を Lean の具体例にする**(2026-11-08, ユーザー承認): `notes/handoff/2026-11-08-m1-spec-examples-conformance.md` の X1〜X24 を、`lean/SpecExamples.lean` に具体的な theorem として置き、Audit に登録する。一般論の証明より先に通す。通らない例は、定義のずれか spec の書き漏れかを示して `notes/questions/` に積む。

- sorry、追加の公理、`native_decide` を使わない。既存の定理の主張を弱めない。`lake build --wfail` と `Audit.lean` を通す。新しい主要 theorem は Audit に登録する。README の「示さないこと」の列を、証明した範囲と一致させる。
- 既存の Lean ファイルを変更しない(`Yulang.lean`・`Audit.lean`・`README.md` への追記だけ可)。公開入口は触らない。
- 「∃ 代入」や「任意の代入」を含む statement を置くときは、実際の solver がその代入をどう決めるかが spec に書かれているかを先に確かめ、書かれていなければ、E2 を出す前に `notes/questions/` に 1 問(Yulang の例つき、選択肢つき、推奨を先頭)を積む。
- 回数制なので、**この 1 回で終わらせようとして、証明の質を落とさない**。閉じていないものは、閉じていないと書く。落ちる前に、こまめに push する。

## 返信に含めてほしいこと

1. 最初のビルドと Audit の結果(通らなかった場合は、何をしたか)
2. 追加した定理の名前と、日本語で読める主張(量化子と前提を省略しない)
3. 各目標(B2・B3・B4・B5/B1)の到達状況(完了 / 部分 / 未着手)と、E1 までの残りの補題
4. ビルドと Audit の結果の末尾
5. `notes/questions/` に積んだ新しい問いの一覧
