# Cycle254: source入力readback、辞書出力の加算上界、raw templateの有限menu

開始2026-11-18T10:35:05Z。50分まで研究・回帰・自己点検を継続し、50〜55分で
本報告を公開。最終の終了時刻・公開SHA・tree照合・ファイル数はreceiptに記録。
最新integration `155c7aa0c99075af020d0c12e528915f05204de3` のstanding ordersと
inboxを再読しI50を継続。終了前の再取得でも変更なし、ACTIVE、上限なし。
前回253はcompletedでremoteと手元bytes一致、復旧を要せず、競合writerなし。

## 成果と正確な範囲

1. **全inputNamesの個別readback。** 実Frame・Holds・ground Inputsから、各入力名
   に閉じた正規Partを構成し、encode size/depthを入力massで抑えた。queryの複数名
   leafにも対応し、coveredHeadやwhere非空を要求しない。source traceの祖先定理で
   local massを元root入力massへ接続した。重複名を足したjoint massの主張ではない。
2. **実child/defaultから出力へ。** CheckedProducedで指定されたchild要求のtargetと
   parent output binderの一致を証明。defaultはimpl binderでなく位置引数を読む。
   実証明書の全child出力を再帰的に使い、親出力の閉じた意味代表を構成する。
3. **sourceから一つの加算上界。** `SourceOutputDepth254.mixed_uniform` と
   `point_uniform` は、source InitialからDを先に一つ選び、その後の全到達状態・
   全Modelsについて、**現在の有限Evidenceを持つ要求出力**にdepth≤Dの閉じた
   同値Pattern代表が存在することを証明した。
   - R=正規化した初期入力のencode総サイズ、T=有限explicit/default body深さbudget。
   - N=source invocation frontierのlist長=(1+branching)^R。重複を含む。
   - D=R+T*N。実child-callごとにfrontierの残り要素数rankが真に減る。
   - Dはfuture state/modelに依存しない。**代表自体はmodelごと**に選ぶ。
   - Nをownerペア数や辞書node数と同一視しない。停止時間の評価でもない。
4. **raw template側を別に閉じた。** `RawOutputBudget254.source_template` は、実trace・
   Frame・要求member・Supplies・compileBody成功だけから、raw Exprがsource由来の
   固定有限menuに属すると示す。Models/Evidenceは不要。任意のsource名をvar参照に
   したmaterialized Exprも固定raw深さbudget以下。explicit RHSはcompileBody通り
   正規化せず扱う。raw budgetと上記ground代表budgetは別物。
5. **静的producer順序。** 実candidate-frame child-callのEdgeはsource trace/model
   条件下で整礎。Selectedを仮定したgraphではない。scheduler Step・alias graph・
   一般等式graphの整礎ではない。

14個の新module、84明示宣言の完全名・日本語の主張・共通前提は
`notes/verification/cycle254/declaration-guide.md` に記載。
M1上は全て補助。意味同値は健全性の支援、有限menu/rankは停止性へ向けた支援だが、
外側の健全性・完全性・主型性、B4 Statementを完成したとは言わない。

## 実例・重要な制限

- 実cycle252 sourceに初期Evidenceを具体的に構成。入力size2、raw template深さ2、
  出力ground代表bound4を確認。全後続状態でもModelsと現在のroot Evidenceがあれば
  bound4。偽だったmax2を再利用しない。
- 実cycle202 defaultの位置引数readbackはdepth≤1、raw template menuはvar0でbudget0。
- 重複を含むrank、非coveredな複数名query、その他を含む**19使用例**をstrict検証。
- 閉じたbalanced variant rowがnormalizeで深さ4→5になる構文guardも検証。
  source到達の新反例でも実scheduler非停止例でもない。今回のground代表の深さは
  再normalize前であり、正規形やsecond-normalize後の上界は主張しない。
- **Evidenceの存在・生成は未証明。** この条件付きground boundをEvidenceNodeや
  停止性の無条件invariantとして使えば循環し得るため、その用途には使わない。
- raw menuはfreshなcompileBody出力を覆う。参照先名のsource全体での有限性、全atom
  の支持、繰返しmapping後のmenu閉包はまだ示していない。244/251の構文増大診断を
  無効にした結果ではない。全model共通の実行可能readback producerも未完成。
- I50の循環時K2拒否、全sourceのSnapshot pool閉包、private非流出、strict新fact、
  operational Step Acc、後継境界とEvidenceNodeは未完。古い反例に依存する部分だけ
  保留し、許された独立研究を続けた。新しい意味論判断・質問ノートはない。

## 次の具体的な穴

1. **PublicBasisSourceClosure**: outputだけでなくordinary/heads/intervals/nominal
   type・row引数/観測pathまでconsumerを分類し、source由来のpublic参照に対する
   置換とCheckedNormal.prepare成功を示す。purpose8/9のfresh centerだけでなく、
   binderが継承する実端点名も分類する。条件付きground boundで代用しない。
2. **TracePrivateFree**: 上記の意味保存なpipelineで、private aggregateが全source
   traceのconsumerに流出しないことを示す。単なるpoolのpurpose分離では足りない。
3. **CanonicalStrictProgress**: 同内容のreobserveを除き、各Stepのstrict新factまたは
   細分化測度を証明。有限候補だけでcycleを除いたとせず、239/240回帰後にAccへ。

設計・前提・consumer位置と依存循環を避ける順序は
`notes/design/2026-11-18-cycle254-input-readback-plan.md` に保存した。

## 検証

Lean4.35.0。実行した最終コマンドは

```
bash notes/verification/cycle254/final-build.sh
```

全文は同directoryの`final-build.txt`、exit0。各14moduleを依存順に
`lean --trust=0 -DwarningAsError=true` で再build、Usage19件、Complete audit84宣言、
Full audit154宣言（生成・private含む）を検査。許容依存は
propext/Classical.choice/Quot.soundのみ。新しい公理・sorry・native_decideなし。
旧default fixtureの未cache依存4moduleもstrict buildしlist/logを保存。
前回1653 source hash不変、今回Usageを含むimport closure1429 sourceを照合。
旧Lean凍結、barrel追記のみ、禁止語検査PASS。全体lake build、verify-lean.sh、
Yulang2実機は未実行。全体PASSは監督役の検証を待つ。使用量枠は不明。

前半3moduleは665ae242で独立read-onlyレビュー済み。後半は枠上限で独立レビューを
開始できず、自己点検のみ。独立再buildは行っていない。各記録はverification内。

## Yulang2・文書照合

spec/06-roles.mdのdefault・中心・K2のユーザー決定を再読。言語規則は変更なし。
監査branch `55574b6052ef1534fd0fc36d6d3617ebede59a0e` のoracle X8/X12/X13を
確認。X8は構造再帰μ生成の証拠がなくK2一致と採用しない、X12は名前付きenumの
実例のみ、X13は任意区間制約の実機表現ではない。今回のreadback/menuそのものは
実機未照合であり、Yulang2の停止性や一般適合を検証したとは言わない。

## 公開

GitHubアプリでwork/dots-mainだけに公開。開始・約10/20/30/40分の心拍と途中成果を
保全し、50分時点の心拍・本報告も公開する。40分時点のe9d7a13bは再取得でtree一致。
最終報告commitと最後のcompleted heartbeat/receiptもそれぞれ再取得して照合する。
公開の承認待ちや安全審査拒否は発生せず。旧247/248復旧quarantineと248/249 lockは
公開対象外。今回の検証済み成果をpublication holdとして残さない。
