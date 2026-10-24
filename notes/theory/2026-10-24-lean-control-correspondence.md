# Lean の具体的 control layer と元の七 frame

LEAN-CONTROL-20261024/r1。producer 停止後に primary が制御の保存・進行と主定理適用を共同構成した。以下は元の規則との対応監査であり、元の全 raw 値・metadata・source からの完全な simulation は未構成である。元の全言語・推論 A/B は OPEN。独立査読は以下の制御抽象と適用境界を受理した。BLOCKING/MAJOR 指摘なし。

## 1. 対象と規則の優先順位

[操作稿](../../docs/yulang-operational-type-safety-ja.tex)の値型・raw constructor・型規則を使い、[V4–V6](2026-10-24-corrected-core-value-continuation.md)の修正核、[G §4–7](2026-10-24-source-core-action-coverage.md)の全 exit と frame、[CM §4.2](2026-10-24-corrected-machine-simulation.md)の immutable/current-world 分離を同時に要求する。操作稿の古い snapshot/一様改名の文章だけから、保存済み receipt/receiver/target を改名することは許さない。

型付けは raw transition と独立した構文的導出とする。raw state に不正 response、間違った値 constructor、Bad を表せることが必要である。型添字に合う状態しか定義しない機械から、元 raw 機械の Bad 排除を直ちに結論しない。

式本体の code 実行、値/型代入、graph lookup、primitive の各定義は別の義務として残せる。ただし次の frame 消費規則を、一括した「安全な code 実行」の仮定へ移してはならない。

## 2. 全 frame の対応条件

| Frame | Ret / Req / Fail に必要な raw control | 元の規則 |
| --- | --- | --- |
| bind | Ret は値を suffix binder に渡す。Req は同じ event/payload を保ち、suffix を K の後ろに置く。Fail は suffix を実行せず同じ理由を伝播。 | O §3.2–3.3、V4、G §4 |
| scope | Ret は own/borrow の規則に従い current control を戻す。Req は suspension と復元 frame、immutable evidence を保持。Fail は failure channel へ進み、未規定 cleanup を選ばない。 | O §3.4、S lifetime、CM、G §7 |
| View | Ret は actual result route を運ぶ。Req は元 event と保存 Observe を保持し、残りの exposure を K に入れる。emission-time 全 active Views の観測は別の実生成義務。 | O §3.6、CM Fork、G §4 |
| handle | Ret は value search。Req は instance/eligibility を現在 world で調べる。選択した arm へ渡す K に当該 handler を加えない。全 operation arms が不成立なら handler を加えた K で転送。value exhaustion は MatchFailure。 | O §3.5、H、G Search |
| mapop | Ret は値を返す。一致 Req は payload adapter の後に paired target instance を発行し、response adapter の後に mapper 内の suffix へ戻る。両 adapter 自身の Req/Fail を残す。不一致は元 instance を保って frame を捕捉。 | O §3.8、V4、G mapop |
| wait | Yes は body-result boundary を経た B。No は attempt の現在 world で pending packet を Rejoin し再検索。別 Req はその新 event と K に wait を追加し、元の pending q/p/K を閉じたデータとして保つ。Fail は次の arm へ進まない。 | O §3.5、G Wait、CM Rejoin |
| release | Ret は target route を作り L を変更しない。Req の実 crossing だけで対応する L を追加し、同じ release を K に残す。Fail は同じ理由を伝播し、release 自身は world を変更しない。 | O release 追加節、修正 S、CM/G |

各 raw rule の型保存は、同じ operation instance の payload/response 型と、同じ frame input/output 型を使って証明する。request 全体の型は response 型ではなく、継続後の正常結果型である。handler の選択時 `Kont(Q,A)` と転送時 `Kont(Q,B)` を混同しない。

## 3. 全履歴への接続で検査する事例

1. **試行 → 別 request → resume → No。** 保存されるのは元の pending q/p/K と残りの候補である。別 request q′ の継続から戻った現在 world が No の検索へ渡る。元 q を q′ として再発行したり、attempt 開始時の L/activity を復元したりしない。
2. **effectful mapper。** payload adapter が request を出す場合、その request に同じ mapper を再適用しない。response adapter も mapper の外で実行する。その後にだけ元 suffix の mapper を復元する。
3. **選択/転送された shallow handler。** 選択時は handler を arm の K に追加しない。転送時には追加する。この差は型の input/output の違いにも現れる。
4. **Fail。** 七 frame の任意有限列を同じ failure tag が外へ進む。残りの guard、No、adapter、Call は起動しない。Bad はこの列挙済み failure と別の raw tag とする。
5. **同じ K の複数使用。** 毎回の response を同じ Q で検査し、異なる現在 world を入力に取る。元 immutable evidence を使い、現在 control の再構成は必要な actual action として残す。

これらは checker に小さな例だけを通すための代用条件ではない。対応する一般的な transition/typing の場合を欠かしていないか確認するための識別条件である。全 source から当該状態が生成されることは、元の別の correspondence 義務である。

## 4. 凍結版との照合と適用境界

[ControlSyntax](lean/YulangClosure/ControlSyntax.lean) は型証拠を持たない raw 構文と `ControlStep`、[ControlTyping](lean/YulangClosure/ControlTyping.lean) は独立した相互帰納的な値・frame・stack・packet・候補列の型付けを定義する。[ControlComposition](lean/YulangClosure/ControlComposition.lean) の `control_preservation` と `progress` は全 control constructor を場合分けする。内部 code の `BodyLaws` は source head が `Head.run` の場合だけを扱い、frame 消費や候補検索を含まない。

| 必要な制御 | Lean の実 constructor / 証明 | 元の対応で残るもの |
| --- | --- | --- |
| bind/scope/View の通常終了と捕捉 | `bindCode/scopeRet/viewRet`、`bindReq/scopeReq/viewReq`、`frames_append/capture_typed/packet_capture_typed` | scope 活性化の own/borrow と View result-route は抽象 metadata。 |
| shallow handler | `handleReq/select/searchRequestEnd`。選択は元 K のまま、転送だけ `Packet.capture (.handle h)`。 | 実 operation の polymorphic instance 化と eligibility の CM/H 解釈。 |
| value arm の順序付き試行 | `handleRet/searchValueTry/searchValueEnd`、`Handler.valueArms` と `ValueArmsTyped`。各試行は独立 code、No で残りへ進み、空列で Fail。 | 各 pattern/guard/body と direct result adapter の code 化、Yes を包む時点。 |
| Wait / pending | `waitYes/waitNo/waitReq`。No は入力 state の現在 world、Req は新 packet の K に元 pending を持つ wait を追加。 | pending の immutable route と現在 ambient cell を CM Rejoin へ写す対応。 |
| mapop | `mapHit/mapMiss/mappedRet/responseRet/enterSavedRet`。payload/response adapter は普通の run と bind、元 suffix だけ mapper 内へ戻る。 | adapter body の具体型付けと effect analysis、実 payload/response 値への対応。 |
| release | `releaseRet/releaseReq/failRelease`。cross は Req の時だけ呼ぶ。 | Ret の route transport はこの値射影で消去。実 L 更新の式と saved target/evidence の保持。 |
| Fail / Bad | `failFrame/failRelease/badFrame/waitBad`。`prefix_fail_absorbing` は全 raw internal prefix で同じ failure reason を保持。`typed_not_bad` は外在的型付けを反転。 | Fail 後の cleanup は `Metadata.failWorld` の全域関係として未規定のまま。 |
| raw resume | `resume/responseOK` は誤 response を Bad にする。`resume_atom_typed/admissible_resume_typed/resume_reusable/resume_formation` が paired response と同じ K の型付けを構成。 | current control を実際に再構成する L-Enter と全値 graph の weakening。外部 world が独立に進む場合の lawful host-state formation。 |

producer 版には、値の pending に nonempty operation-arm list を付けても型付けできる欠落があった。primary は二種類の候補列を raw の異なる位置に分け、`SearchTyped` をその構文に対応させた。値の試行列自体も raw transition へ展開した。安全性を型規則の前提にする修正ではない。

`finite_trace_safety` は、同じ `StateTyped` result を持つ任意の初期 state からの `Prefix (YulangClosure.Step (machine md body)) n` **全て**に対し、末尾の型保存・Bad 排除・Ret/Req/Fail/次の内部一段を導く。`n` や外部 resume 回数に上限はない。これは `BodyLaws` が与えられた制御抽象の定理であり、未具体化の Yulang body にその前提が成立したとは主張しない。

`localLaws` は既存の `LocalLaws` の `internal_preservation`、`resume_formation`、`no_bad`、`progress` を今回の証明から埋める。`AnalysisLaws` は実 seed/simulation/observation だけを別入力として残す。`finite_prefix_control` はその instance に既存 `finite_prefix_composition` を実際に適用する。全出力を許す dummy certificate や singleton cell を作っていない。有限解析の前提自体の解消は未完である。

## 5. 何がまだ全言語の具体化ではないか

`Value.atom Nat Nat` と `Ty.base Nat` は値形状の境界用の抽象である。元の tuple/record/nominal/union/intersection/recursive/polymorphic/evidence/closure/graph value を定義したものではない。元の全 response がこの単純 tag 検査へ写る証明もない。元の subtype/evidence を通る canonical forms、代入、Force/Call/primitive/eabs/eapp、graph allocation は、実 body 関係と `BodyLaws` の構成に残る。

`Metadata` は値型から独立した world 操作であり、CM/H の具体 world を構成したものではない。`Kont` に world snapshot はなく `resume` は与えられた現在 world を使うが、immutable receipts と activation の実再構成を既に証明したとはしない。`Machine.exposed` は terminal request のみであり、emission 時点の全 View 観測や Ret/latent/reentry ports の実 inclusion は未構成である。

したがって今回閉じるのは、明示した制御抽象での全有限実行の型安全性と、既存 root へのその適用である。元の source/native/elaboration、initial formation、original scoped coverage・principal coverage・termination の命題は変更しない。元言語からこの抽象への全 case の対応と残る field の実証明を供給するまで、元 Yulang 全体の閉鎖は OPEN のままである。
