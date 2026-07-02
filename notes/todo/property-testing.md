# property testing TODO（undet を土台に）

出典: notes/design/2026-07-02-parting-assessment.md §5（Claude Fable 5、ユーザ承認済み）。

## 目的

生成器 + 性質 + 縮小からなる property testing を std に置く。
外部の乱数生成器や探索器を輸入しない——**undet がまさに探索器**であり、
`less` / `more` は縮小順序、junction の all は一括検査として既に存在する。

mock handler（構文を変えないテスト）と合わせ、「effect 言語はテストが
書きやすい」を公開時の実証つき主張にする。

## 設計素描

生成器はただの undet 計算:

```yu
-- gen::int, gen::list f, gen::str などは undet で候補を枚挙する普通の関数
my xs = gen::list gen::int
assert (xs.sort.len == xs.len)
```

- **探索の駆動**: undet の全枚挙は無限になるので、テストランナーが
  「予算つき探索」の handler で undet を受ける（枚挙数上限・サイズ上限）。
  乱択が欲しい場合は random act（host）を種にした選択 handler に差し替える。
  同じ生成器コードが全枚挙・乱択の両方で走る——handler 差し替えの見本になる。
- **縮小（shrinking）**: 反例発見後、`less` 側の候補から再探索して最小反例へ
  降りる。縮小器を別に書かせない（生成器の構造が縮小順序を含んでいる）。
- **assert**: 失敗は error effect。ランナーが catch して反例値
  （derive show / debug、notes/todo/deriving.md に依存）と一緒に報告する。
- **再現**: 乱択の種、または record/replay（notes/todo/record-replay.md）の
  記録を失敗報告に添付し、`--replay` で決定的に再現する。三つの TODO が
  ここで合流する。

## テストの表面（綴りは仮）

```yu
test "sort keeps length":
    my xs = gen::list gen::int
    assert (xs.sort.len == xs.len)
```

- `test "名前":` ブロックの正確な形は error 仕様と `?` 記法の確定後に決める。
  それまでは通常の関数 + ランナー規約で始めてよい。
- ランナーは CLI（`yulang test`）とし、cases.toml の executable contract とは
  別レイヤ（ユーザ向け機能であって、コンパイラの regression 基盤ではない）。

## First slice

1. `gen::int` / `gen::bool` / `gen::list` を undet で実装（std のみ、runtime 変更なし）。
2. 予算つき枚挙 handler + assert + 最初の反例報告（縮小なし）。
3. 縮小: 反例発見後の less 側再探索。
4. `yulang test` ランナー（ファイル内の test 関数を列挙して実行）。
5. 乱択 handler（random act 依存。host act 実装後）。

1〜3 は**言語機能を一切足さずに std だけで書けるはず**。書けない場合は
undet / Fold の表現力の穴が見つかったということなので、それ自体を報告する
（dogfooding としての価値）。

## 完了条件

- `xs.sort.len == xs.len` 型の性質テストが動き、故意に壊した sort で
  最小反例（またはそれに近い小ささ）が報告される。
- 同じ生成器が全枚挙 / 乱択の両 handler で動く。
- 反例の表示が derive debug 経由で読める。

## やってはいけないこと

- 専用の乱数プリミティブや shrink プリミティブを runtime に足すこと
  （undet / less / more / random act で書けない場合のみ相談）。
- テストランナーのために推論・lowering に test 専用分岐を入れること。
