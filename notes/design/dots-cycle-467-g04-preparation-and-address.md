# C467: G04 実準備相と native address の接続（I-89）

単一可視 head・事前検査済み GD の同一要求だけ。C466 の実 C332 assembly の receipt を元の出現・宣言番号・元 capture・物理行番号のまま C360 の実 preparation に入力できるかを検査する。新しい candidate matching・目標 selection・GD は扱わない。

## データ・独立判断・実行

- まず実な old `State` と実準備 `Prepared.stage` の比較。その構文、モデル集合、raw Alias、既存観測と raw K2、既存 native origin は別々の観察。後の相で data が増えたとき、元スロットで同じことを別途証明する。構文上同じ相と呼ばない。
- 任意の別々に与えられた snapshot: Eq と観測済み footprint がそのまま、旧 interval/ordinary alias generator を保持、新しい generator は指定された戻し写像で既存 bound に落ちる場合、固定された旧名上の Alias と raw K2 は保存・反映。footprint は実 shape の owner と子を有限列に抽出し、余分な raw open はしない。写像/証明は実構造の境界であって native issuer を作らない。
- 実 C360 `compile` は既に要求された associated output を data ordinal で読む。実 `prepare` が成功しても、この出力が無い要求には可能な `compile` は存在しない。出力を人工的に足さない。他の genuine compiler publisher がある場合は、実 source/source address の来歴、配置、既存 release をそのまま追う。検証された値等式から物理発行者を推測しない。

## 期待定理と対照

同じ実元 head と C332 output receipt から、実 C360 preparation の成功ないし正確な失敗、数個の完全な provenance/reflection を Lean で示す。対照は source occurrence・元宣言 ordinal・生成行が同じでも追加 bound がある合法相、正しい Fits のまま保持される一部観測と変わる別の観測、出力無しの `compile` 不可能。任意の既存発行の soundness と、未発行の現行 native issuer を生成できるという主張を分ける。真正な production API と有限証拠が足りなければ G04 は未完。旧 checker Bool、仕様、canonical writer は変えない。G05/G10/G08、G06/G07、G20/G21、GD は外。
