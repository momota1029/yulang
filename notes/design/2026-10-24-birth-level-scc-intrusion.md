# 生成レベルごとの Value SCC と intrusion

Status: Authoritative for the explicit user-selected qualification rule
Scope: immutable Value generation levels, SCC qualification and its application to retained extrusion occurrences
Approved-by: user, direct decision in this conversation, 2026-10-24
Drafted-by: primary
Review: exact frozen review scope and result are recorded in the [sprint outcome](../../tasks/agent-loop/sprints/birth-level-scc-20261024-outcome.md); this header does not certify the global preservation theorem
Supersedes: only the cross-level SCC qualification in the three sources listed in §5

## 1. 直接の決定

ユーザーは、Value の固定された生成時レベルごとの参照グラフで SCC を構成するという説明を受け、次を選択した。

> では生成レベルでSCCをつくり，intrusionを行うことにしましょう．extrusionが働くので，親子等置でも同じことができるはずです．

前半を算法の選択として記録する。後半は extrusion と親子等置の対応を証明する方向を示す。局所の対応定理を適用し、一般化・使用まで含む結論はその実際の前提を満たしてから導く。ユーザーの決定そのものを保存定理の証明とはしない。

今回の作業対象は意味論・証明・文書であり、実装変更は含まない。共起分析と保護解除に関する[既存の直接訂正](2026-10-24-cooccurrence-release-clarification.md)は維持する。

## 2. 固定された生成レベル

`G=(V,Ref)` を既存の source Value と実参照のグラフとする。各 Value `v` に、その source constructor が Value を生成した時点の推論レベル `birth(v)` を保持する。

- 既存の source constructor が定める生成時のレベルを使用する。今回の nested definition の例では外側 F が1、内側 G が2である。
- `birth(v)` は以後変更しない。型制約による level 低下、型座標の quotient、後の一般化・使用では書き換えない。
- 同じ Value を参照する Name は同じ Value とその birth を参照する。型記述の freshening は source Value の新規生成ではなく、birth を付け直さない。
- 型変数の現在の level と Value の birth は別の情報である。extrusion の親子の型変数が同じ現在 level であることを条件にしない。
- 同じ数値の birth は、同じ lexical scope、registration component、一般化境界または capture telescope を意味しない。それらの既存情報は保持する。

この定義は generation level の意味を固定するものであり、既存実装が既に全経路でその情報を保持しているという主張ではない。

## 3. レベルごとの誘導グラフと資格

各生成レベル k について、次を定義する。

```text
V_k   = {v ∈ V | birth(v) = k}
Ref_k = Ref ∩ (V_k × V_k)
G_k   = (V_k, Ref_k)

qualifies(e)
  ⇔ ∃k. origin(e), receiver(e) ∈ V_k
          ∧ SCC_G_k(origin(e)) = SCC_G_k(receiver(e)).
```

同じ SCC に属するという条件は、両方向の参照経路があり、その **全頂点** の birth が k であることを意味する。全グラフ G で SCC を求めた後に両端の birth だけ比較する方法ではない。別レベルの頂点を通る経路は資格を与えない。単一頂点も SCC であり、同じ Value を両端とする実 occurrence を特別に除外しない。

元の Ref からレベルをまたぐ参照を削除しない。それらは source の参照・依存として残る。G_k は intrusion の資格判定に使用する誘導グラフである。

helper node や圧縮表示を用いる場合も、まず semantic Value incidence の上で上記の資格を定める。実装用 helper に便宜的な birth を与え、その filter が元の G_k の経路を変えることを許さない。圧縮表示を採用する owner は、各 G_k の到達性を保存する対応を証明する。

## 4. 資格を持つ occurrence の親子等置

既存の[occurrence 規則](2026-10-12-intrusion-value-type-association.md)を継承する。extrusion が実際に生成した occurrence identity、origin/receiver Values、polarity 別の parent/copy pairs を保持する。

`qualifies(e)` が成立する場合、その e の実 pair を親子等置し、蓄積済みの全制約を保持して後続の伝播・使用へ反映する。対象 pair の選別を型座標の SCC や表示型の一致で代用しない。freshening 自体から新しい extrusion occurrence を作らない。

資格を持たない occurrence については、元の level-based extrusion の一方向の近似関係とコピーを保持する。この資格規則に基づく親子等置を追加しない。他の独立な正当な制約から等式が導かれる可能性は排除しない。

Value birth は型座標を同一化しても変わらない。型座標の level・bound・non-generic 情報を保持する既存の責務も変わらない。

## 5. 置換する範囲

以下の元文書は履歴と未変更の規則の出典として保持する。

1. [parent-copy SCC intrusion](2026-10-10-parent-copy-scc-intrusion.md) の、Value SCC eligibility を lexical/inference level で制限しないという節を、§2–§4で置換する。
2. [Value/type association](2026-10-12-intrusion-value-type-association.md) の全 Value graph による資格式と、nested F/G および O/E を跨レベルで資格ありとする適用を置換する。実 origin、receiver と parent/copy pair の規則は継承する。
3. [top-level principles §1.1](2026-10-11-yulang-inference-top-level-principles.md) の SCC による取消しは、今後この生成レベル別の資格を用いて読む。制約生成・蓄積・extrusion・一般化の基本構造は維持する。

[旧 SCC 証明](../theory/2026-10-24-value-scc-qualification-proof.md) の一般グラフ補題は各 G_k に適用できる。その旧 §6 の F/G qualification と、そこから C=B,D=R を追加する履歴は旧規則についての結果であり、現行規則の例として使用しない。

新しい規則の選択は、旧規則の反例候補をそのまま現行算法の拒否とする前提を取り除く。旧 helper の完全 source membership が証明済みになったという意味ではない。前の受理意図の質問は、旧拒否を維持するかという判断の待ち条件から外す。未回答を肯定・否定に読み替えない。

## 6. 証明の接続と残る責務

局所 extrusion の既存結果は再使用する。

- 有限 store、空の初期 polar memo に対する一回の extrusion の停止と level 境界。
- 正負の一方向近似、および元の demanded comparison を満たす同一 valuation から、実コピーを親と同じ値に解釈する局所 diagonal lift。
- 全 clause を保持した equality quotient の解対応。

この局所 lift は、同じ cut の元の demand を満たす valuation を入力に取る。原 source の一般化・捕捉・各使用の telescope をまたぐ joint strategy の存在までを自動的に与えない。新しい資格の全 occurrence について、どの source law がその入力を供給し、どの publication/use action が等式を運ぶかを証明する。

生成レベル別の経路・更新、nested helper と odd/even の適用、および局所 lift の接続は[後続証明](../theory/2026-10-24-birth-level-scc-intrusion.md)に記録する。全言語の健全性、必要な主型性、combined inference の停止性、source/native 実装対応は各々の証拠を要する。
