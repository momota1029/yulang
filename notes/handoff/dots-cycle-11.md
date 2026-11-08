# dots cycle 11: checked producer capture provenance

## 状態・時間

- Cycle 11 / max12。ACTIVE、STOPなし。integration/m1-finalをfetchし基点 `cddf0884e` をmerge。前回heartbeatはcycle10 completedだったので並行実行しない。
- 開始 2026-11-08T17:23:51Z、検証・5artifact一致確認 17:29:47Z。報告準備まで5分56秒。公開・completed心拍の時刻はGitHub履歴参照。
- 既存 `yulang-cycle6` の1キャッシュを再利用。空き開始19G、終了19G。未公開ローカル履歴があるためworktreeを削除しなかった。
- 中断・環境再作成なし。全25分上限内。今回10分を超えないので開始と完了の心拍。

## 到達点

実producerのcaptureを親endpointの構造位置へ戻す橋を追加。`CommonRoleCaptureOrigin`。Ty値が同じだからsource IDも同じ、と推論していない。literal headのunknown sentinelにはcapture位置を与えない。lowerとupperを独立に扱い、単一区間の仮定なし。宣言のcheckを通ったwhereの使用変数について親・子の位置の存在を導出する。

8定理すべてB4のsoundnessを支える補助命題。B4の完全性・principal inference・全体resolve_exactを証明したという意味ではない。

## 宣言（名前は Yulang.CommonRoleCaptureOrigin 以下）

1. `inspect_origin`: 任意のPattern p、型t/payload、自然数depthに対し、captureDepth p=some depthかつ独立判断Inspect p t (.hit payload)なら、tをdepth本のunary辺に沿って辿った型はpayload。
2. `inspect_origin_exec`: 同じ全量化と位置仮定に対し、実inspect p t=.hit payloadなら同じ位置結論。
3. `instantiate_origin`: 任意のTemplate、payload、depthに対し、variableDepth template=some depthなら、実instantiate後にdepthで取り出す型はpayload。
4. `production_origin`: 任意のvisible宣言列、request q、宣言d、payload lp/hp、depthに対し、実production visible q=some(d,lp,hp)かつcaptureDepth d.head=some depthなら、q.lower/q.upperのその位置はそれぞれlp/hp。
5. `child_origin`: 任意のvisible、q、child、d、lp/hp、headDepthに対し、上記production・head位置仮定とchild∈children q d lp hpがあれば、その子を作ったrequirement∈d.requirementsが存在し、child.roleはそのrole。さらに任意のdepthでrequirementのvariableDepth=some depthなら、childのlower/upperのその位置は親の対応capture位置と等しい。
6. `named_capture`: 任意のpとnameに対しname∈p.namesならcaptureDepth p=some depthとなるdepthが存在。
7. `named_variable`: 任意のtemplateとnameに対しname∈template.namesならvariableDepth template=some depthとなるdepthが存在。
8. `checked_requirement_origin`: 任意のvisible、q、d、lp/hp、requirement r、nameに対し、d.check=true、実productionがd/lp/hpを返す、r∈d.requirements、name∈r.2.namesなら、headDepthとchildDepthが存在し、両位置計算が成功し、親lower/upperの位置はlp/hp、rを実instantiateした子lower/upperの位置はそれぞれ親のcapture位置と一致する。位置の存在を追加仮定にしていない。

## 検証

環境: ELAN_HOME=/workspace/scratch/1d0b4aaa3394/dots-probe-elan、同binをPATHへ。Lean4.35.0。

`cd lean && lake build Yulang.CommonRoleCaptureOrigin --wfail`: exit0、270jobs、実時間1.456秒。全文:

```text
✔ [270/270] Built Yulang.CommonRoleCaptureOrigin (1.3s)
Build completed successfully (270 jobs).

real	0m1.456s
user	0m1.140s
sys	0m0.541s
```

`cd lean && lake env lean /tmp/cycle11-axioms.lean`: exit0。新モジュールをimportし8公開定理の#print axiomsを実施。全文:

```text
'Yulang.CommonRoleCaptureOrigin.inspect_origin' depends on axioms: [propext]
'Yulang.CommonRoleCaptureOrigin.inspect_origin_exec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCaptureOrigin.instantiate_origin' depends on axioms: [propext]
'Yulang.CommonRoleCaptureOrigin.production_origin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCaptureOrigin.child_origin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCaptureOrigin.named_capture' depends on axioms: [propext]
'Yulang.CommonRoleCaptureOrigin.named_variable' depends on axioms: [propext]
'Yulang.CommonRoleCaptureOrigin.checked_requirement_origin' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`git diff --check`: exit0。新モジュールにsorry/axiom/native_decideなし。Audit.leanへ8件追記済み。

最初の実行はELAN_HOME設定忘れで `/home/agent/.elan` Read-only file systemにより失敗。設定後、存在しない補題List.mem_of_head?_eq_someで1回コンパイル失敗。head?のcasesによる証明へ修正して上記PASS。隠して再試行成功のみを報告しない。

全体lake build・全Audit・verify-lean.shは最新I-5指示に従い未実行。verify出力は存在しない。監督役の全体検証待ち。

## 公開と保存

以下5artifactはGitHub appでwork/dots-mainのみへ公開し、fetch後blob SHAとローカルgit hash-objectを全件照合し一致:
- lean/Yulang/CommonRoleCaptureOrigin.lean
- notes/design/2026-11-08-cycle11-capture-origin.md
- lean/Yulang.lean（追記のみ）
- lean/Audit.lean（追記のみ）
- lean/README.md（追記のみ）

5artifact公開末尾commit `09a1267c7dab7dc86c78ee3b46be872910e2b385`。報告本体と心拍は別途公開するので、合計7ファイル。integration/main/yulang3への書込みなし。
ローカル小コミット: `7ad0e958e` capture origin、`88f5e7a04` checked bridge、`812b0b058` registration。公開はgit pushではなくconnectorのcreate/update。

## 未達・次の主要な橋（3群）

1. 今回は単引数unary構造位置。実source graphのラベル、共有DAG、複数引数、narrowing後位置を保持する生成とcycle10 growStateへの接続が未達。有限動的仕事領域も未達。
2. ordinary updateと候補・兄弟再生成を結んだ単調飽和と停止。
3. 安定状態の四方向分類・子結果診断tree・正規順dictionaryを結んだ一般B4 exactness/soundness/completeness。

残りはこの3群であり「あと3本の小補題で済む」とは主張しない。Main.B4Statement、X13–X16は今回PROVEDにしていない。parser/Yulang2実行からの意味保存も未確認。audit x-oracleを読み、Y2の構文制限をLean成功の代用にしなかった。新しい意味論の設計選択なし。

使用量のどの枠に計上されたかは、この環境から確認できない。
