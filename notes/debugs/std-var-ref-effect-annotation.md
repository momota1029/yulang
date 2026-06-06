# ④⑤ 型引数注釈の effect 行が body の裸 Con と畳まれない

## テスト
- `source::tests::lowers_std_var_ref_inside_nested_act_module` — `crates/yulang-infer/src/source/tests.rs:3593`
- `source::tests::lowers_std_var_ref_through_top_level_alias` — `crates/yulang-infer/src/source/tests.rs:3618`

## 入力
```yu
my make_ref = var::var_ref            # ④
# ⑤ は加えて: my make_ref2 = make_ref
```
`lib/std/var.yu`:
```yu
my var_ref(): ref '[var 't] 't = ref {
    get: \() -> get(),
    update_effect: \() -> set:ref_update::update:get()
}
```

## バグ表
| | |
|---|---|
| 期待値（正）| `unit -> std::var::ref<[std::var::var<α>;], α>` |
| 実際値（誤）| `unit -> std::var::ref<std::var::var<α> <: [std::var::var<α>;], α>` |

## なぜ期待値が正しいか
`var_ref` の戻り型注釈は `ref '[var 't] 't`。`'[var 't]` は **開いた effect 行 `[var<'t>;]`**
（`ref 'e 'a` の `'e` は `['e]`/`[... ; 'e]` で使われる effect-kind パラメータ）。
注釈がこの行を固定するので `'e = [var<α>;]`。期待はそのまま `ref<[var<α>;], α>`。

## 診断
実際値の `'e` スロットは **不変区間** `var<α> <: [var<α>;]`:
- upper = `[var<α>;]`（注釈どおりの行）← 正しい
- lower = **裸 Con `var<α>`**（行に包まれていない）← body の effect がここ

body（`get()` 等の act 呼び出し）の effect は `var<'t>`。これが **行 `[var<'t>;]` に包まれず
裸 Con のまま** lower に入り、upper の行と一致せず区間が残る。注釈どおりなら lower も
`[var<α>;]` になって区間が `[var<α>;]` に collapse するはず。

ユーザ診断（memory `infer-test-pass-2026-06-06` ④⑤）:
> 昔の「反変位置に T→[T;] と推論」が関数型は新 subtract(`T-subtract(α;#1)`)に移行したが、
> **型引数注釈の effect-kind 位置は未実装**。

## 修正方針（ユーザ設計判断 2026-06-06 — ⚠️ 期待値が変わる）
ユーザの指摘で方向が変わった。本質は「注釈をそのまま閉じた行で表示する」ことではなく、
**反変位置の effect 型引数の推論を直す**こと。

設計原則（ユーザ言）:
> 共変の注釈は閉じた型でもいいが、**反変の注釈は絶対に開いている**。
> 反変位置のエフェクトは閉じた型にならないという強い制約がある。
> ユーザの書いた型がそのまま表示されると、むしろ不都合。

`ref 'e 'a` の `'e` は反変的に消費される effect パラメータ。注釈 `'[var 't]` を
**閉じた行として固定するのが誤り**で、反変なので**開いた行**として推論されるべき。
→ 正しい型はおそらく `ref<[α & var<β>], β>` 系（① `ref<α & β, γ>` と同じく、
**反変 effect 引数が intersection ＋ 開いた行**になる形）。**①と④⑤は同根**
——「反変位置の effect 引数の扱い」という同じ原則の表れ。

修正対象: 型引数の反変位置 effect 推論（注釈を閉じさせず開いた行にする）。
関数型の反変注釈は新 subtract(`T-subtract(α;#1)`)に移行済みだが、型引数注釈は未対応。

## ⚠️ これは設計未確定（Codex はまだ着手するな）
- ユーザ自身「正解の可能性が高い」「かも」と**確定前**。`[α & var<β>]` の正確な形は未確定。
- **テスト期待値 `[var<α>;]` 自体が暫定で、正解ではない見込み**。よって「期待値を変えるな」は
  ④⑤ には**適用しない**——ただし新しい正解を確定させるのは**ユーザ**であって、
  Codex が勝手に期待値を書き換えるのは依然禁止。
- 委譲ランク: **保留**（反変 effect 推論の設計確定待ち）。①が同根なので**①を先に**やると見えてくるかも。
