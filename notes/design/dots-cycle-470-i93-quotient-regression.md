# C470 / I-93: raw を変えない最小商の回帰（単項 record）

+30 に I-93 を確認。正本 `yulang3@fcc2aba451c3cfc7e443092d296e84aa044f1482`、`spec/06-roles.md` blob `a3d903781fef0691b773f886ba8976a6b4ac871d` L505。**再帰型として等しい点を同一視した商の上で循環を判定する。** C469 の元 named raw edge が無い事実は変わらない。意味上 inline field が K2 となるのはこの新決定による。旧 Yulang2・既存判定を後から PASS と読み替えない。

## 計算と独立な対照

C464/C469 の元入力は実 GD、単一可視、出力なし、point 4。実 raw 行は `4={30:{40:var 5}}` と `5={40:var 5}` のまま。既存 `shapeOf` から 4→5 を取り出さない。比較するのは実 head の field30 に対応する **source occurrence** の inline `{40:var 5}` と、既存名 5 の `{40:var 5}`。この回帰では各点を（record field label, payload の子）と抽象化した。inline occurrence は raw の新名でも旧行の追加でもない。

| 点 | 観測と子 | 商での判定 |
| --- | --- | --- |
| 既存 point 5 | label40、子 5 | 循環上 |
| field30 の inline occurrence | label40、子 5 | `[(inline,5),(5,5)]` の照合で同じ class。子が同じ class に戻るため循環上 |
| 独立な対照 stem | label77、子 5 | 5 に到達するが循環上でない。正の歩数後は常に 5、最初の label が 77 と 40 で異なる |

単項で**全ての constructor と子を与えた**抽象グラフに限り、型の等しさを全ての有限深さでの label trace の一致と置く。関係の各対について label 一致と子対の所属を data-only で検査し、深さへの帰納で全 trace 一致。正の歩数の戻り先が同じ class なら商の cycle。負の証拠は、最初の子を含む子閉包の有限列と、各点が根と異なる有限 trace 深さ。全正歩数に適用できる。**正の対応が見つからないのは安全性の証明ではない。** 例えば `[(5,5)]` だけでも正しい関係だが、inline の正の照合は通らず、inline は実際に循環上。旧 escape を未最小化のまま流用しない。

独立の `Std` のみ、Lean 4.35.0 `lean --trust=0 -DwarningAsError=true --stdin` で確認。5 件（有限対応→全 trace 一致、inline の正、stem の独立な非循環、負の証拠の健全性、stem の負 witness）の公理照合は `propext` / `Quot.sound` のみ。守られた実行列 `(true,true,false,false)`（正関係、inline、偽 stem 対、子対欠落）／`(true,false,true,false)`（stem 負証拠、inline 負証拠、恒等関係、恒等関係だけで inline 正）を確認。C464 actual Lean へ import した test ではなく、**数学的な転記**。project Lean・既存監査に追加無し。

## 次に必要な実接続

1. 既存の元 occurrence、実宣言・引数、original/normalized path を保持し、**実際選んだ**非変数 constructor の inline field と元 raw 点との有限対応を actual compiler event の入力根拠から読む。C463 `locateRoute` は既に `MixedPath.childName` を要するため、この欠けた hop を先に要求しない。隠れた同名 field・未訪問 sibling・別相の値は使わない。
2. 正枝は実 label/子の checked correspondence と同相 raw 5 の実 cycle を結び、全同じ `FitsFull` の意味を証明する。全 Model の値等価は checker 入力にしない。単なる循環への到達、同じ形の別 occurrence、既存 publisher の旧版、未完の出力だけを代用しない。
3. 負枝は完全な局所観測の抽出・商での安全証人が先。単項の回帰で一般 pair/variant/nominal や incomplete raw `shapeOf` に対する完全性、exact original report、同じ Fit の soundness を主張しない。G04 は未完。State/spec/旧 checker/既存 raw 行、他の G 行は変更しない。
