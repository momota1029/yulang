# 元の Yulang 全体の証明：継続 r2

対象は `momota1029/yulang`、`yulang3`。開始点は
`45d307a0aa01722b5aac289b07d71953630abca7`。
ユーザーの「それぞれこまめにコミットプッシュしながら、証明を終わらせる」
という指示に従い、構成・検証・独立レビューが揃った単位で公開した。

**元の全言語についての四つの主定理は未完了。**
今回の四つの成果は具体的な前提を減らす証明であり、元の
`SourceProblem` の全体 instance を構成したという意味ではない。
supported source、完全 Call、Effect、共有 witness、元の instance 順序、
将来の use の量化を変更していない。

## 1. 公開した証明

| コミット | 内容 | 単独監査の定理数 |
| --- | --- | ---: |
| `b8115116ff24f99e882c7bd1cb2137d93062879a` | 元の再帰 source の Call owner、完全 App 規則、実 returned-callee の読み出し | 73 |
| `ecde5039c2de4abd49fd3ad33145e1915e1c0cb4` | 実 fresh allocation から導く旧 inventory 上の単射性と scope 評価の可換性 | 50 |
| `d29e73ff9e974e68745c4bc22c42441a9e62883d` | source の注釈に対応する record adapter と、構成した子変換の安全性 | 307 |
| `61397ece06557c36cb1a5ef47825d76667c3ec1b` | 成功した Context expansion 全体から得る post/fiber/child の形の不変条件 | 50 |

各コミットは証明、理論ノート、再実行可能な全定理監査、producer 記録、
独立した非著者の review を含む。生の build/audit ログは新たにコミットせず、
コマンド・結果・入力 hash・完全な監査プログラムを記録した。

並行コミット `ff12ce504` と `4c5fff3b2` も保持した。後者の
goal-indexed Function checking admission 修正が依存先を変更したため、
record を再ビルド・再監査・再レビューし、source receiver の構成も
primary が非著者として再検証した。旧先端への record ref 更新が失敗した時は
実先端を読み直し、変更を保持して新しい先端へ積み直した。force push は無い。

## 2. Effect の fresh 化で実際に閉じた部分

[`NativeFreshScopeTransport.lean`](../theory/lean/YulangClosure/NativeFreshScopeTransport.lean)
は、`ScopeInventory::fresh` の成功した ID 割当てを構成する。
現在の個数を n とすると、新しい ID は n、その後の個数は n+1。
旧 key に対する map の値は `HashMap::insert` と同様に更新され、
コピー対象でない key は identity のままになる。

この map は自然数全体では単射でない。例えば個数2で key0をコピーすると
0 と inventory 外の2の双方が2へ写る。それでも、**コピー前に存在する全 ID**
の上では単射であり、コピーした局所 ID と、固定した外部 ID は衝突しない。
その性質を仮定せず、各割当てでの交換写像から証明した。key の重複にも対応する。

旧 inventory 内に収まる transformer と入力状態について、実 map による
名前替えと transformer の評価が可換になる。外部 protection を含む入力全体を
扱うので、局所 release が外部の protection を消さない。評価後の有効範囲も
構成し、次のコピーに同じ結果を適用できる。

残るのは、すべての元 source 経路がその inventory の有効範囲・owner・
同じ map の対応を満たすことと、receipt/current-world/resume などの本来の
Effect 意味との接続。二つの有限座標の保存だけでは全衛生性は完成しない。

## 3. Principality に必要な source receiver

[`SourcePrincipalTransport.lean`](../theory/lean/YulangClosure/SourcePrincipalTransport.lean)
は、既存の具体例を元の raw AST から構成する。

```text
let top = lambda h.
  let rec f = lambda x. lambda y.
    {first = h x, next = f {a = y}}
  in f
in top
```

recursive f の monomorphic binding、両 App の完全 Call と computation の条件、
先行 h の Return を待つ後続フィールドを保持する。元の current installed tuple
から h の局所 Name 導出を作り、任意の先行 frame 列の後にも元 owner が保たれる。
callee の `finalRoot` と App が読む `returnedValue` は区別し、供給された Return
データから同じ value/provider/current event の読み出しを構成する。
そのデータ構成自体は Return の admission や発生を証明しない。

最初の未解決の対応は、同じ後着 extrusion occurrence z についての次の等式。

```text
actualOccurrence(z).receiver
  = receiving_index(source_frame(Z_real))
```

source 側の receiver は得られるが、それを native の同じ occurrence に認証する
constructor が未構成。source support のいずれかが SCC 資格を持つことから、
その一つの receiving projection は導けない。さらに元の principal coverage には、
publication/use と全 future family に整合する一つの strategy と元の
`instanceOf` 順序が必要。この具体例は原言語の反例ではない。

## 4. Record の子変換を仮定から構成へ進めた部分

[`OriginalSourceRecordBoundary.lean`](../theory/lean/YulangClosure/OriginalSourceRecordBoundary.lean)
は、identity と有限に入れ子になった record 変換を実際に生成する。
各 child の型保存・安全性、順序付きの実 record-machine 実行、有限な外側 prefix
の安全性を導く。`ValidPlan` や `ChildrenSafe` を呼出し側へ要求して終えていない。
一般の定理には生成成功と独立した入力型の前提があり、具体例ではそれらも構成した。

raw source の expression annotation と binding annotation は別の境界として
登録される。前者は `synthesis`、後者は initializer の `finalRoot` を入力とする。
具体的な二段の変換では二段目が一段目の実出力を受け取り、隠れた field を
復活させない。共通 optional field の値が実行時に無くても静的な型比較は行う。

対象の child は純粋な identity／有限 record の族。一般の effectful cast、
cyclic descriptor、input-specific presence、open row、spread 等の契約まで
構成した結果ではない。`recordKernel` は明示的な局所 conversion 拡張であり、
元の任意 Kernel との等価性ではない。元 descriptor と完全な `structuralFields`
への readback、および full source/native soundness の接続が残る。

## 5. 停止性で残った具体的な増殖

[`NativeInferenceProgress.lean`](../theory/lean/YulangClosure/NativeInferenceProgress.lean)
の主結果は、既存の `expand` の成功結果と浅い入力 Context から、すべての
inline filter と残りの continuation を含めて、post-context と出力 bound fiber
の Context が Identity、operand child が元 source の単一 filter 形になること。
通常の Effect 注釈の初期化が作る `PrefixLeft(weight, Identity)` も保持する。

この形は table の追加を含む明示的な constructor history の下で保たれる。
その history は元の `inferStep` ではなく、任意に長くなれる。まず全 native 実行
からこの projection を取り出す対応が必要であり、形だけから全体の停止は導けない。

大域的な尺度の具体的な障害は、**別の extrusion 呼出しが同じ親から兄弟コピーを
繰り返し作れること**。memo は呼出しごとに新しくなるため、親子の level が毎回
下がることだけではコピーの個数が有限とは言えない。後の FreshUse が捕捉する
live graph も、それ以前の drain で増える。source の Name 数だけでは足りない。

元の demand/copy descriptor の有限供給、scope/view の増加、完全 relation key、
intrusion generation の更新、入れ子の drain の戻り順序を一緒に扱う整礎尺度が
必要。元の source の発散反例を発見したという主張ではない。
`Contracts.InferenceTermination` は推論算法の停止性であり、全プログラムの
評価停止性を主張する定義ではない。

## 6. 統合検証

`WholeMetatheory.lean` は前回の4モジュールと今回の4モジュールを import する。
既存の default target、元の予約済み closure root、compiler、依存パッケージは
変更していない。固定 Lean 4.35.0、Lake `5.0.0-src+eb6cafb` を使用した。

| 検証 | 実測結果 |
| --- | --- |
| `lake build` | exit 0、112 jobs |
| `lake env lean -j1 -M1536 AuditWholeMetatheory.lean` | exit 0、717個の異なる定理、89必須 root |
| 監査ブロック | 717個の開始・終了が一意に一致 |
| 型・公理 | 全対象の完全な型と推移的な公理依存を出力 |
| 入力一致 | 176個の Lean/config 入力が検証後も一致 |
| 新規警告 | 今回の proof／audit には無し |
| 既存警告 | 668件、開始時と byte-identical な9ファイル |

結合 import では record の生成補題の帰属が変わる。単独307という数を機械的に
合計せず、結合環境での8モジュールの671定理に、共有 `sourceRules` の46定理を
明示して追加した。単独 record census の定理はすべてこの717定理に含まれる。
他の5個の共有補題は既に結合 census にあり、重複して数えない。

公理集合の内訳は、空333、`propext` のみ121、`propext, Quot.sound` 168、
標準の3公理95。`sorryAx`、project axiom、native-evaluation assumption は無い。
通常の proof build は `-j1 -M1024`、大きな完全監査だけ既存の局所上限
`-M1536` を用い、各呼出しを120秒で制限した。

scratch evidence は `/workspace/scratch/e3678bef96db/whole-integration-r2`。

| 証拠 | SHA-256 |
| --- | --- |
| default-build.log | `af2a2b2179c58aa251b21fb71ee4893f6f85eb243ec4d55df6deff8544a39ce3` |
| whole-audit.log | `7292aedea4a63e6f7cfa26073a2c3724c7ec36d56dfe7c8a2558f6c055c3291c` |
| input-hashes.json | `0f03489fa0e97f302bef93f5977a9bc95b5d580485f53c76eb48d65bb6a031da` |
| summary.json | `690f366f13a22e533b0dd70346db0ff21dbc60ae3298cc2f07da4e6985567726` |

再現用の監査コードと全 component の review は repository に残る。
途中の exec-server 切断は復旧し、保存された出力を再取得した。
数値 exit が失われた reviewer の一回の build は、その事実を記録し、
後続の直接 Lean 検査・全監査の観測済み exit 0 と区別した。

## 7. 主定理へ残る接続

| 元の主張 | 最初の残る構成 |
| --- | --- |
| 全体 soundness | 元 descriptor／primitive／record field の独立意味、recursive introduction、全 source case と同じ native history の成功への接続 |
| Effect 衛生性 | 全 source 経路の inventory・owner・map の真正な対応、現在 world の receipt／resume／compaction の相関 |
| Principality | 同じ extrusion occurrence の receiving incidence の認証と、全 use／future に共通する元の principal strategy／instance 順序 |
| 推論停止性 | 全 native step からの projection と、兄弟コピー・live graph・generation・nested drain を数える大域的な整礎尺度 |

これらを未証明のまま仮定へ移したり、言語を制限したりして主定理を完成扱いに
していない。今回の公開は上記の具体的な証明と、その正確な適用範囲までとなる。
