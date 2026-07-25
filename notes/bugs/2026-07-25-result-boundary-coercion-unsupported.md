# 結果境界で implicit cast が実行時に適用されない

発見日: 2026-07-25
状態: **解決済み（2026-07-25、同日）**。`fbb9c62c`。下記「解決」を参照。
発見経緯: 型健全性スライス（`dd29c93e` companion method、`3219363f` plain function）の
レビュー中に、Claude が実機確認して発見

## 症状

関数・メソッドの結果型注釈が正当な implicit cast を要求する場合、コンパイルは通るが
実行時に落ちる。

```yu
my g(): float = 1
g()
```

`lib/std/core/convert.yu` に `int -> float` の cast が宣言されており、候補は一意である。
コンパイル時にはその cast が正しく解決される。しかし実行すると次で失敗する。

```console
$ yulang --std-root lib --no-cache run --print-roots repro.yu
runtime error [yulang.unsupported-runtime-feature]: unsupported expression in runtime: runtime boundary

$ yulang --std-root lib --no-cache run --interpreter --print-roots repro.yu
runtime error [yulang.unsupported-runtime-feature]: unsupported runtime feature: coerce int => float
```

interpreter 経路の方が原因を明示している。`coerce int => float` が実装されていない。

companion method でも同じである。

```yu
struct s { v: int } with:
    our x.m: float = 1

(s { v: 1 }).m
```

## 対照: 他の境界では動作する

同じ cast が、他の位置では実行時にも正しく適用される。

```yu
my h: float = 1     -- 値束縛
h
```
```console
run roots [1]
```

```yu
my k(x: float): float = x    -- 引数位置
k(1)
```
```console
run roots [1]
```

したがって、implicit cast の実行時適用そのものは実装されている。
欠けているのは**結果境界での適用**だけである。

## 経緯

この経路は、これまで一度も踏まれていなかった。

結果型注釈に subtype 義務が課されていなかったため（それがまさに 2026-07-12 に記録された
型健全性の穴である）、cast が要求されることが無く、したがって実行時に cast を適用する
必要も生じなかった。

`dd29c93e` と `3219363f` で義務を課したことにより、この経路が初めて到達可能になった。
新しく作り込んだ欠陥ではなく、既存の未実装箇所が露出したものである。

## 影響

結果型注釈が正当な implicit cast を要求するプログラムが、実行時に失敗する。

- コンパイル時には診断が出ない（型としては正しいため）
- 実行時に `yulang.unsupported-runtime-feature` で停止する
- 誤った値を返すことはない

現行コーパス（`lib/std`、`examples` 34 件、`tests/yulang` 全 fixture、contract 229 件）に
この形を含むプログラムは存在せず、全ゲートが通過している。したがって現時点で観測される
実害は無いが、ユーザーが書きうる正当なコードである。

## 修正前後の比較

| | 修正前 | 修正後 |
|---|---|---|
| `my g(): bool = 42`（cast 無し） | 通る（**不健全**） | 拒否される |
| `my g(): float = 1`（cast 一意） | 通り、`int` を返す（**不健全**） | 実行時に停止 |

いずれも修正前は不健全であった。後者は、静かに誤るのではなく明示的に停止する状態へ
変わっている。

## 修正の方向

他の境界（値束縛、引数位置）で既に動作している cast 適用機構を、結果境界にも通す。
新しい機構の設計ではなく、既存機構の適用範囲の問題と見られる。

着手前に確認すること。

- 結果境界の cast がどの段階で落ちているか（specialize か、control IR lowering か、VM か）。
  evidence VM と interpreter で異なるメッセージが出ることから、少なくとも 2 箇所で
  扱いが分かれている可能性がある。
- 値束縛経路がどのように cast を適用しているか。同じ経路を再利用できるか。

## 関連

- `notes/bugs/2026-07-12-function-result-annotation-conformance-gap.md`
  （この経路を到達可能にした元の穴）
- `lib/std/core/convert.yu`（`int -> float` を含む std の 4 つの cast）

## 解決 2026-07-25

`fbb9c62c` で閉じた。

### 診断

欠落は specialize2 にあった。結果境界は lambda body に cast call を生成せず、
`unit -> int` と `unit -> float` の差を関数全体の `FunctionAdapter` へ押し上げていた。

対して、動作していた境界は既存経路
`coerce_emitted_value` → `boundary_expr_with_argument_contract` → `cast_boundary_instance`
を通り、`Apply(InstanceRef(cast), value)` を mono へ生成していた。

両バックエンドでメッセージが違ったのは、adapter の扱いが 2 箇所に分かれていたため。

- evidence VM: adapter return の generic `adapt_value_result` → `UnsupportedExpr("runtime boundary")`
- mono interpreter: 別実装の generic `adapt_value` → `UnsupportedBoundary("coerce int => float")`

control-IR は adapter を忠実に lowering しており、そこで cast を失ってはいなかった。

### 修復

lambda body の actual result から declared consumer result への**直接の ordinary cast が
存在する場合に限り**、既存の cast-instance 機構を body 内へ適用する。emitted function shape も、
実際に cast を生成した場合だけ declared return へ更新する。直接 cast が無い effect / function
境界は従来の generic adapter 経路のまま。

初期案では consumer return をより広く適用したが、contract regression を検出したため撤回した。

### 測定

- `g()` と `g() + 0.5` を両バックエンドで実行し `run roots [1, 1.5]`。
  値まで確認したのは、cast が飛ばされていないことの証拠にするため
- companion method も同様に `run roots [1, 1.5]`
- `my f(): bool = 42` は両バックエンドで拒否のまま（健全性は非後退）
- 値束縛 `h` と引数境界 `k(1)` も従来どおり動作
- infer 958 / specialize 145 / yulang 364 / contract 229、fmt 通過

### 回帰テスト

- specialize IR: cast call が lambda body 内へ生成され、generic adapter / coerce が残らないことを固定
- runtime: plain function と companion method を両バックエンドで実行し `Float(1.0)` を固定

contract fixture は追加していない。既存の runtime test の方が両バックエンドと値を直接検証でき、
contract の文字列比較より強いため。

### 同種の欠落

`notes/bugs/2026-07-12-struct-field-type-conformance-gap.md` の field 境界にも同じ欠落があり、
そちらは `812bb5a6` で同時に対処した。
