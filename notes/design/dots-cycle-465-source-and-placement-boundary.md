# C465: G04 の producer と検証器の間に残る接続

I-89（単一可視候補、外部の検査済み GD）に従う。I-90 は報告の道具・委譲の記録だけで、作業対象は不変。

| 既存処理 | 実際に出すもの | この処理からは出ないもの |
|---|---|---|
| `NativeValue360.compile` / `NativeInstall360.install` | actual prepared input に由来する有限 code、owner/version/source/output 等を含む board write と exact install | compound ordinary endpoint と、G04 の `I65.State.origins/routes` の発行。今回の reader は保持済み原行・発行済み route を照合する。 |
| `NestedMaterial332.assemble` | 旧 head/capture の実構文に基づく ordinary の新座標と行、span、旧モデルの限定した保存 | 旧 origin predicate を正しく transport しても、新規 allocation 行は利用可能な source origin にならない。I65 の issuer の発行は別。 |
| `deriveOriginalCompoundOutput394` | 実 associated output の元 occurrence、出力 ordinal、slot、本文と compound code | 古い literal write への射影には独立に検証した狭い再帰文法しか入らない。さらに associated output は head の訪問位置・発行権を意味しない。 |

今回の接続は、既存 report/wire から実際に使った raw row と native origin の二つの ordinal を固定し、後者の完全な board release と論理原位置を検査する。物理 slot の一意性は不要。旧限定 reader は、同じ wire 上でこの検査に旧一意性条件を足したものと同値。report の raw 行／端は変えない。全原行が Native360 の像なら field の必要な開き方が一つも成立せず、現行の field receipt を作れない。これは比較対象の producer の限界であり、言語の拒否ではない。

次の一つの証明目標は、実 head/capture の構造帰納が出す **元位置付き typed projection** から、実 compiler 相の **新座標・完全な issuer/address・保持済み native view と route** の同時発行を示すこと。C401 の typed associated-RHS と C332 の普通の名前付けは補助になり得るが、両方を合わせるだけではこの発行は出ない。C464 の raw ordinal/safe cut と値の保存は別に照合する。新 raw 辺や発行権を同値・新名・存在から仮定せず、既存相との連結が示されてから有限 replay へ進む。K2 の優先や候補の列挙（G05/G10）、残余 join（G08）、open tail（G06/G07）、一般 nominal（G20/G21）、GD はここで決めない。
