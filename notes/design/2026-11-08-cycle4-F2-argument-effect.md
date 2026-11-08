# F2: explicit argument-effect conversion, not arrow subtyping

Basis: spec 5.5c (user decision), I-4, audit `f1-effect-passthrough.md`.
Y2 implements passthrough inside structural subtype; new spec deliberately places
it outside subtype. Y2 explicit higher-order annotation has check/run mismatch;
this implementation does not import that mismatch.

## Critical source/kernel distinction

Spec 5.5c explicitly says an omitted source argument row accepts all rows. The
`rowEmpty` in these lemmas is **not** the translation of that omission. It is the
existing kernel value-only interface: strict lowering evaluates the argument and
passes a pure value. The adapter quantifies over arbitrary incoming rows, but that
alone does not establish a source elaboration from omitted rows. There is no
source omission carrier or omission-to-kernel correctness theorem here. Therefore
this is a proved auxiliary kernel interpretation for F2, not F2's complete source
coercion judgment. All references below to ordinary arrows mean that explicitly
empty kernel interface, not omitted source annotations.

## Data and independent judgments

`ArgumentCast source target` has the sole rule
`arrow A empty B E => arrow A F B (E ∪ F)` for arbitrary Common A,B,E,F.
It does not modify `Common.Subtype`. Its inversion theorem records all witnesses.
For any nonempty F the source need not subtype target; prove this directly.

Runtime uses the existing resolved request-tree model, whose historical arrows
receive suspended computations. Its explicit adapter forces the argument once
before calling the original function with a pure value. This is not a new runtime
operation: prove equality with the already-defined common strict application
lowering. Preserve the complete tree, not just a row set. The transformed value
has the stated target arrow validity; any valid higher-order consumer can accept
it. This is resolved semantic preservation, not a parser/inference insertion
algorithm and not full F2/X25 completion.

## Targets

For all source/target Common types: ArgumentCast iff the displayed constructor
witnesses exist. For every environment/function/argument with ordinary-arrow
and actual argument typing, the existing `forceApplication` has the merged row.
For all n,Key,Atom,input/output shapes, A,B,E,F and f: ValidValue ordinary f implies
ValidValue converted (forceValue f). For all actual computations, strict
application of f equals application of its explicit adapter in the historical
core. Higher-order uses quantify over arbitrary consumer, not a fixed example.

Unresolved: expected-type insertion at source high-order/pipe positions, linkage
between Common regular types and resolved shapes, and source normalization. Do
not claim X25 PROVED or global B5/B6 completion.

## 証明済み宣言（11本）と主定理の側

- `CommonArgumentEffectCast.argumentCast_iff`（補助・定義のexactness）:
  任意の source/target 共通型について、独立変換判断が成り立つことと、
  引数型・結果型・body行・incoming行が存在して両端が規定のarrowに等しいことは同値。
- `nonempty_cast_not_subtype`（補助・責任境界）: 任意の引数/結果型とbody/incoming行、
  incomingに属する任意のoccurrenceについて、元arrowから変換先arrowへの標準subtypeは成り立たない。
- `rowJoin_comm`（補助）: 任意の2行の集合joinは交換する。実行順序の定理ではない。
- `ordinary_application_preserved`（健全性）: 任意の環境と式f/x、型A/B、行E/F/functionRowについて、
  fがordinary arrow、xが(A,F)を持てば既存forceApplicationは(B,functionRow∪(E∪F))を持つ。
- `ArgumentEffectCastRuntime.converted_valid`（健全性）: 任意のshape/値carrier/行/関数について、
  元arrowの意味的validityから、forceValueの変換先arrowのvalidityが従う。
- `resolved_cast_sound`（健全性）: 任意のresolved変換導出・元arrowのvalid関数は、
  forceValue後に変換先arrowでvalid。
- `pure_call`（補助・意味保存）: 任意の関数とpure引数値について変換前後の結果request treeは等しい。
- `force_idempotent`（補助・意味保存）: 任意の関数についてforceValueを二度適用しても一度と等しい。
- `strict_application_agrees`（意味保存）: 任意のresolved関数式/引数式/実行環境について、
  実common strict loweringの評価と、関数を評価してそのforceValueへ引数計算を渡す評価は完全なtreeとして等しい。
- `checker_retains_incoming`（健全性・生成器接続）: 任意のchecker環境と式、型、行について、
  ordinary関数と引数の推論結果を前提として、実strict loweringの推論結果は
  functionRow ++ incoming ++ bodyを保持する。
- `higher_order_consumer_valid`（健全性）: 任意の元ordinary関数と、変換先arrowをpure引数として
  受け取る任意のvalid高階consumerについて、変換した関数を渡した計算はconsumerの結果型/行でvalid。

完全性・主型性・source挿入の成功は今回の定理からは主張しない。
`Common.common_arrow_iff`も歴史的`.app`も変更なし。
Focused build: 173 jobs, exit 0。11定理のtrust-zero公理監査: 標準 `propext/Quot.sound` のみ。
