# ⑦ branch join が implicit cast 境界を解決できない

## テスト
`tests::branch_join_uses_implicit_cast_boundary` — `crates/yulang-infer/src/tests.rs:916`

## 入力
```yu
role Cast 'from:
  type to
  our from.cast: to

struct user_id { raw: int }
cast(x: user_id): int = x.raw
cast(x: int): user_id = user_id { raw: x }

my id: user_id = 7
my pick (b: bool) =
    if b: id
    else: 0
```

## バグ表
| | |
|---|---|
| 期待値（正）| 型エラー無し（`0` が `cast(int): user_id` で user_id に変換される）|
| 実際値（誤）| `ConstructorMismatch`（`pos=PosId(5) neg=NegId(7)`, origin = literal `0`）|

## なぜ期待値が正しいか
`if b: id else: 0` は **第一分岐 `id` の型 user_id を join 先**にする仕様
（テスト名どおり "use the first branch type as the implicit cast target"）。
`cast(x: int): user_id` が宣言されているので、else の `0: int` は user_id に暗黙変換でき、
全体は `bool -> user_id`。エラーは出ないのが正しい。

## 診断（コードを追った結果）
`lower_if`（`crates/yulang-infer/src/lower/expr/control.rs:457`）:
- 結果 var `tv` を作る（458 行）。
- 第一分岐（`then: id`）で `arms.is_empty()` が真 → 501 行
  `constrain(Pos::Var(tv), Neg::Var(body.tv))` = **`tv <: id.tv`**。
  これは tv の **upper 境界に「id.tv という変数」**を置くだけ。具体型 user_id は
  `id.tv` の **lower** に居る（`my id: user_id` だから）。
- else（`0`）は `arms` が空でないので 537 行の制約は付かず、cast 境界
  `implicit_cast_boundary_with_effects(body=0, target=tv, preserve=true)`（539 行）へ。
- `state.rs:583` の `resolve_cast_method(expr.tv=0, expected_tv=tv)` は
  source を `concrete_tv_lower_repr(0)` = **int**、target を `concrete_tv_upper_repr(tv)` から読む
  （`solve/selection/role_method.rs:360,362`）。
- ところが tv の upper は「id.tv という変数」で、user_id は id.tv の **lower** に居るため
  `concrete_tv_upper_repr(tv)` が user_id を**見つけられない** → cast 解決 = `Unresolved`。
- `state.rs:653`（Unresolved 腕）が eager に `constrain(0 <: tv)` を発火。
  tv <: id.tv（lower=user_id）なので **int <: tv <: user_id → int <: user_id → ConstructorMismatch**。

### 鍵: 第一分岐の型は tv の **lower** に居る
第一分岐の cast boundary（503 行）も同様に Unresolved → eager `id <: tv` を発火するため、
**処理後 tv の lower に user_id が入る**（分岐は union として lower に集約される）。
else の cast はその user_id を **tv の lower** から探すべきなのに、`resolve_cast_method` は
target を **tv の upper**（`concrete_tv_upper_repr`）から読むので見つけられない。これが核心。

## ⚠️ 触ってはいけない場所
`state.rs:653` の Unresolved 時の eager `constrain(expr.tv <: expected_tv)` は **故意**。
`surface_diagnostic_defers_constructor_mismatch_to_cast_boundary` と
`surface_diagnostic_keeps_unresolved_deferred_cast_boundary` が「raw mismatch を surface filter が抑制する」
挙動に依存している。**この eager 制約を消すと別の 2 テストが壊れる**（前セッションで確認済み）。
直すべきは「cast の target を解決可能にする」方であって、eager 制約の除去ではない。

## 修正方針
**branch-join の cast は target を「join 集約先（tv の lower）」から引く**。else の
`resolve_cast_method(int, tv)` が tv の lower に居る user_id を見つけ、`cast(int): user_id` を
挿入できるようにする。

❌ 避けるべき素朴案（union typing を壊す）:
「第一分岐の具体型を tv の **upper** に hard 制約する」のは NG。`if b: 1 else: "x"` のような
**cast が無く union したい分岐**まで「第一分岐への cast 強制」になり、`int | str` を作れなくなる。
あくまで「cast があれば cast、無ければ従来どおり union（eager フォールバック）」を保つこと。

候補:
- (B') **本命**: `implicit_cast_boundary` 系（state.rs:524-660）の branch-join 経路でだけ、
  cast の **target lookup を tv の lower にも広げる**（`concrete_tv_lower_repr(expected_tv)` を見る）。
  これは「集約先の既存分岐型に cast できるなら cast」を意味し、見つからなければ既存の eager union に落ちる。
  branch かどうかは `ExpectedEdgeKind::IfBranch`（control.rs:508,544）で区別できるので、
  境界に「target を lower からも引く」フラグを足す形が局所的。
- (B) `concrete_tv_upper_repr` 自体を変えるのは広域影響なので避ける。

成功条件: `branch_join_uses_implicit_cast_boundary` が緑、`surface_diagnostic_*` 2 件が緑のまま、
かつ union 系の既存テストが無回帰。`case` も同じ構造（control.rs:333 付近の first-arm 制約）なので両方確認。

## ⚠️ 改竄防止
このテストは `errors.is_empty()` を見るだけ。期待は「エラー 0」。assert を緩める余地はない。
mismatch を抑制ではなく**解決**で消すこと。

## 設計確定（ユーザ判断 2026-06-06）
**cast が無い分岐は union が正解**。理由: 後から誰かが `int <: str` のような cast を
（望ましくなくても）実装してしまう可能性があり、その時に union として開いていないと破綻するため。
→ 上記 (B') 案（「cast があれば cast、無ければ従来どおり union にフォールバック」）で確定。
`if b: 1 else: "x"` は `int | str` になる。第一分岐厳格化はしない。
