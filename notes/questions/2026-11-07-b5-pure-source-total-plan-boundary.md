# B5: pure source 本体と total PureCasts.Plan の接続

状態: **Lean の限定された障害定理は検査済み。元 B5 の E2 ではない。設計変更は未承認。**

## 利用者から見える問い

pure cast は「effect を追加しない」が、純粋な本体の発散まで宣言時に排除する意味か。
あるいは通常の pure 関数と同様に発散でき、実行可能 plan に部分実行を表現するか。

```yulang
struct source_id { raw: int }
struct target_id { raw: int }

cast(x: source_id): target_id = (\f -> f f) (\f -> f f)
```

この Yulang 例は問いを示す表記であり、parser/name-resolution から下の厳密な Core term への elaboration は未証明。
検査した反例は、内外とも **Core.strictApp** を使う閉じた lambda 自己適用である。
旧 Core.app を勝手に strict と同一視していない。

根拠: `spec/06-roles.md` 6.5 は pure body と即時実行を要求するが、全 body の停止判定は指定しない。
`PureCasts.lean` は既存 well-founded computation の定理であり、その本文も source termination theorem を仮定／証明していないことを明記する。

## Lean で通った正確な境界

`lean/Yulang/CommonPureCastTotalityBoundary.lean`:

- `Fragment.source` は全 original var/lam/app node を保持し、app を Core.strictApp にする。
  `Fragment.runtime` は同じ有限木を既存 EvaluationOrder の bound/lam/app にする。
- `omega_typed`: 任意の full role nominal Common 環境 Γ、任意の同じ新 regular carrier の結果型 R について、
  独立した元 `Core.CommonSyntax.Typing model Γ omega.source (pure R)`。
  一状態の正則型 `T ≈ (T -> R)` を実 guarded closure で構成する。型付け証明や body purity を外部から受け取らない。
- `unit_bool_body_typed`: 入力 `unit` の実 mono binder を持つ環境で、同じ本体は結果 `bool`・空行を持つ。
  正則型は内部 witness のみで、cast endpoint 自体に再帰型を必要としない。
- `omega_no_eval`: 任意 global 数・既存 program/store・captured value 環境・返却値・read trace に対して、
  既存 **EvaluationSafety.Eval** に同じ厳密な fragment の有限返却導出がない。
- `no_faithful_total_plan`: 任意 scope/global 数・任意 runtime 型 A/B・Key/Payload/Response・program/store/captured 環境・入力について、
  次の最弱の返却忠実性すら持つ既存 `PureCasts.Plan ... A B` は存在しない。

  ```text
  ∀ returned,
    plan.run input = pure returned →
      ∃ sourceResult sourceReads,
        EvaluationSafety.Eval program store captured (omega.runtime globals) sourceResult sourceReads
  ```

  `PureCasts.Plan.run_eq_pure` が返却を供給し、上の nontermination に矛盾する。
  返却値の一致や全 source evaluator の意味をこの反証の前提にしない。

## 選択肢と推奨

1. **推奨: 一般 source cast には部分実行を表す plan を使う。**

   精密化する接続の statement:

   ```text
   任意有限検証済み registry D と、元 source 型付けが空 immediate row を持つ各 body b に対して、
   実有限 search が返す plan は有限の executable syntax / regular shared code を持つ。
   runtime は返却・request・無限の内部実行を表現する。
   同じ元環境・元入力での各有限実行 prefix と各有限返却を元 b と対応させ、
   新しい immediate effect を導入しない。
   arrow は入力変換の実行後の引数で元関数を呼ぶ。
   body の返却がない場合に、型付けから返却を導かない。
   ```

   既存 total `PureCasts.Plan` の theorem は、実際に total な resolved fragment の theorem として保存する。
   元 B5 が最終 plan 表現を total PureCasts に固定したとは書かれていないため、これは元 statement の反証ではない。
   「request tree 全体」が返却の有無を含む等号なら、一般 pure body に対する言い換えも明示する必要がある。

2. **pure cast body に宣言時の停止性検査を追加する。**

   ```text
   body の実 source Typing が pure であり、さらに実行が total と検証された有限 registry D のみを受理する。
   この追加された verified 前提の下で、同じ元 body を既存 total PureCasts.Plan に移す。
   ```

   これは現在書かれた純粋性条件だけより強く、元目標の verified 前提と利用者が書ける cast を変える。
   ユーザー承認なしに採用しない。今回、全 source の停止判定器は構成していない。

## 未確認と次の証明

この module は source fragment の二つの node-preserving map と、既存 CBV の非停止を扱う。
全 Core operational correspondence、実 source declaration/name/type verifier、一般 search の完全性、
全 request tree / rows / construction sites の接続は別義務である。
新部分 runtime 表現の採用、元 B5 の E2、B5/B1 完了のいずれも主張しない。
