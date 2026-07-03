# `\my &x ->` 束縛と `&do`（with 系の状態プロトコル糖衣）

決定日: 2026-07-02
発案: ユーザ。記録: Claude (Fable 5)。
状態: **方向決定（authoritative）・文形と λ 形は実装済み**。
file slice（[2026-07-02-file-session-boundary-plan.md](2026-07-02-file-session-boundary-plan.md)）
の**外**の独立トラック。

## 0. 実装状況

- **文形 `my &x = f(do)`: 実装済み・検証済み**。parser 変更ゼロ
  （`my &x = f(do)` は既にパースされ、従来は無意味な生ローカル束縛だった。
  repo 内に既存使用ゼロを確認済み）。実装は infer のみ:
  - `crates/infer/src/syntax.rs` — `protocol_do_binding_reference_name`
    （収集と lowering が同じ判定を共有）、`expr_needs_synthetic_owner` 拡張
  - `crates/infer/src/module_map/mod.rs` — synthetic var act の収集走査に
    protocol do-binding を追加（単一 descendants 走査で文書順を維持）
  - `crates/infer/src/lowering/expr/block_local.rs` —
    `lower_protocol_do_binding_continuation`（`\#x -> { my $x 束縛; <rest>;
    ($rest, $x) }` を既存の var 束縛機構 = init/var_ref/run で合成）
- 検証: infer 511 tests / stable-core 57 / file-resource 34 すべて green。
  canary は `do_binding_state_protocol`（基本 + 入れ子、期待値は手導出）と
  `file_text_with_commit_do`（手書き protocol 版と同一観測）。
  rollback（abort で backing 無傷）と undet 分岐独立（entry snapshot +
  last-write-wins）も probe で確認済み。
- **λ形 `\my &x -> body`: 実装済み・検証済み**（2026-07-03、Codex 実装）。
  parser は lambda binder 位置でのみ `my` を受け、直後が non-empty `&` sigil
  pattern の場合だけ protocol binder として扱う。lowering は文形と同じ
  synthetic var act / `var_ref` / `run` 経路に乗せる。複数 binder
  `\my &x, &y -> body` は、全 init parameter を先に束縛してから body に
  var handler を張り、`(body_result, final_x, final_y)` を返す。
  canary は `lambda_my_binder_state_protocol` と parser の
  `expr_lambda_my_ref_binder*`。
- **既知の別問題**: 入れ子 `text_with` × 状態変数の交差は check を通るが
  specialize の slot 衝突で落ちる。糖衣と無関係の既存問題（手書きで再現）。
  [notes/bugs/nested-text-with-state-var-specialize-conflict.md](../bugs/nested-text-with-state-var-specialize-conflict.md)。
  局所の無注釈関数の入れ子は動く。

## 1. 何を解くか

with 系 API（`text_with` 等）の callback に「更新可能な変数」を渡したい。
しかし ref を渡すと変数の instance 効果が型に乗り、公開境界を渡れない
（file slice §0 の三竦み）。解は state-passing プロトコル:

```
f : 't -> [e] ('r, 't)        -- 初期値を受けて (結果, 最終値) を返す
```

この形は糖衣なしで書けるが、儀式（初期値の受け取り・局所変数の宣言・
組の返却）が毎回入る。本 note はその儀式を言語糖衣にする。

## 2. `\my &x -> body` の脱糖（解釈2 = 貧者の存在型）

```yu
\my &x -> body
```

は次に脱糖される（`#x` は衛生的な fresh 名）:

```yu
\#x ->
    my $x = #x
    my #r = body
    (#r, $x)
```

- λ の型はただの `'t -> [e] ('r, 't)`。**新しい型理論はゼロ**。
- 変数 `$x` / `&x =` は body の中で普通に使える。instance は λ の中で
  生まれて λ の中で discharge される。発話不能名は行多相 `e` への具体化と
  してしか流れず、公開スキームに現れない（貧者の存在型）。
- 複数変数 `\my &x, &y -> body` は宣言順で組を広げる:
  `\#x #y -> { my $x = #x; my $y = #y; my #r = body; (#r, $x, $y) }`。
  消費側 API は arity ごとの型を持つ（with 系は当面 1 変数だけ使う）。

## 3. `&do` — 文位置の双子

do 記法の束縛に `&` 変数を許し、同じ生成を文位置で行う。
`\my &x ->` が式位置（λ）、`&do` が文位置で、**同一の構文の二つの置き場所**。
do sugar 改訂の詳細（綴り・境界規則）は実装時に別 note で確定する。

## 4. 正当化（ユーザの二論点）

1. **hygiene はどのみち必須**: `&x` を with 系で受け取る形は、どの設計でも
   fresh instance の生成と衛生的束縛を要求する。糖衣に閉じ込めるのが最も安全
   （2026-05-13 衛生性事件の教訓: 変数生成は sugar の専権にし、手書き経路を
   増やさない）。
2. **`&x` は他の型とほぼ直交**: `&` 束縛は状態変数専用の記法であり、既存の
   値の世界と衝突しない。この糖衣を with 系の標準経路として強制しても害が
   ほぼない。

補足: 既存の `\&x -> body`（**ref 束縛子**。渡された ref を `$x` / `&x =` で
使う）は**そのまま残す**。`\my &x` は「その場で生成」、`\&x` は「受け取った
ref を束縛」で、`my` の有無が生成の有無に対応する。

## 5. 棄却した代案: パッケージ形（解釈1）

`\my &x -> body` を `((&x, &x::run), \&x -> body)` の組にして、消費側が
runner を任意の位置で走らせる案（rank-1 の ∀ で instance 名を運ぶ
existential エンコード。消費側で instance が rigid になるため、discharge
手段が渡された run に限られるというパラメトリシティ保証も付く）。

**棄却理由（ユーザによる等価性論証）**: `&x::run` を使えるタイミングは
実質最後しかなく、instance の操作を消費側が catch することもできない
（それには第一級モジュール相当のより強い前提が要る）。ゆえに解釈1で
できることは解釈2 と外延的に等価であり、組の複雑さだけが残る。
関数が三つ組・四つ組になるより、ただの関数型の方がよい。

将来、第一級 instance（文献: first-class named handlers, Xie & Leijen 2022）
や本物の存在型（row subtraction / 06-23 private tail projection の延長、
研究相談トラック）が入った場合は、この note に戻って ref 渡しスタイルの
復活を検討する。プロトコル形はその下位プリミティブとしてそのまま残る。

## 6. 実装時の注意（着手時に読む）

- 脱糖は parser DSL desugar と同じく lowering 層で行い、`#x` / `#r` は
  hygiene 機構の fresh 名を使う。ユーザ名 `x` の可視性は body に限る。
- `my $x = #x` の生成する instance は通常の局所状態と完全に同一経路
  （特別な runtime 表現を作らない）。
- fixture: 脱糖形と手書きプロトコル形が同じ public 観測になる canary を
  最初に置く（file slice の fixture 1〜3 の糖衣版がそのまま使える）。
- do sugar 改訂は本 note の範囲外。着手時に別 note で確定させ、本 note から
  リンクする。

---

*署名: 本記法はユーザの発案（`&do` 案 → `\my &x` λ 形への展開、解釈1/2 の
比較と等価性論証を含む）であり、Claude (Fable 5) は記録と型付けの検査を
行った。変更にはユーザの明示的な承認を要する。 — Claude (Fable 5)*
