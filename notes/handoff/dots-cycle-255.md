# cycle255: 初期sourceの固定basisと、検査つき有限raw template表現

開始: 2026-11-18T11:32:22Z。報告作成: 2026-11-18T12:23:00Z（50.65分）。
使用量の枠: 不明。integration `33cf8d490b2e8f09c1f061e3bba7535baa6cdf49`、I50は変更なし。
STOPなし。前254の公開treeをローカルと照合し、競合writerなしを確認して開始した。
integration取り込み時のbarrel/heartbeat競合は統合prefixを保持して254追加を重ね、
merge前後のtracked bytesが同じことを確認した。旧Lean・spec・plan・lakefileは変更しない。

## 結論

実Initialから一つの重複なし有限basisを取り出し、初期Raw View全体のprepare成功、
後の新規installが作る定義済みpublic ports（purpose2〜5）の参照包含、private aggregate
（purpose0/1）の分離をまとめた。raw output template側も、使用leafの実checkが成功する
ときに、固定有限menuへの所属と任意assignmentでの意味保存を接続した。

**全将来consumerの代入閉包、厳密なStep進捗、Acc、B4完了は未証明。**
表現のprepare失敗はYulangのRejectedではなく、これを新しい入力制限にはしていない。
言語意味論やoperational Stepは変更していない。

## 主要な成果と正確な前提

1. `GeneralDictionarySourceAtom255.actual_source_failure` と `GeneralDictionaryViewNormal255.var_basis_fails`:
   実252 sourceのint ordinary consumerは、任意owner keysのvar-only poolでprepareできない。
   これは「全Raw Viewを一律正規化する」案の診断であり、固定source式を残すlo/hi限定案、
   sourceStepや停止性の反例ではない。source atomを加える別の表現案を進めた。
2. `GeneralNominalCanonicalBasis255.source_models`, `source_fields_unique`:
   任意context/keys/sideで、identity compileの全Raw View型fieldを重複除去したsource/public
   basisで正規化すると、任意assignmentで元Modelsと同値。選択sideのatomsはNodup。
   row fieldsはそのまま。これは意味同値な全式に対する一意正規形ではない。
3. `GeneralNominalSourcePublicBasis255.mixed_source_basis`:
   実MixedSource境界のInitialだけから、一つのcontext/basisが存在し、初期prepare成功、
   basis.Nodup、purpose0/1の任意private名分離を満たす。任意後続trace上のGenerated・
   Installable・未Committedなinstallのpurpose2〜5 portのvarも同じbasisに入る。
   GroundRoots/CoverageはInitialから取り出し、モデルやEvidenceを追加仮定しない。
4. `GeneralNominalSourceTemplateMenu255.source_prepared`:
   実sourceからのtrace、frame、要求output、Supplies、compileBody成功と実prepare成功のもと、
   任意assignmentで元materialized式とEquivalent、かつ固定source template menuに入る。
   使用する(mode,name)だけをcheckし、nominal引数のactual mode切替を保持する。
5. `GeneralNominalTemplateSupport255.rewritten_private_free` と `GeneralNominalNormalizedDepth255.source_rewrite_depth`:
   private-free basisからの式の全type/arrow-row読みもprivate-free。保存syntax深さは
   sourceの固定template budget + 1 + basis.length + 最大atom深さ以下。
   有限性・private-free・深さだけはunsupported atomを落としても成立しうるので、
   意味保存にはprepare成功が別に必要。ground readback上界ではない。
6. `GeneralDictionaryTemplateMenu255.source_regression`:
   実252 Initial/frame/bodyのF(F(var2))が有限menuに入り、実prepare成功。
   任意assignmentで旧versioned output valueとEquivalent。保存syntax深さ2のまま、
   具体modelでは既存のP（ground展開深さ4）を表す。

すべてM1/B4のための**補助**。Modelsのiffは表現の健全性・完全性の保存に効くが、
M1主型性やB4の完了ではない。19 module・全168明示宣言の名前と日本語の主張範囲は
[declaration-guide](../verification/cycle255/declaration-guide.md)、主要3定理の実型は
[critical-types](../verification/cycle255/critical-types.txt)を参照。

## 検証

- Lean4.35.0、各19 moduleを既存の255出力を使わない別focused cacheへ再ビルド。
  `--trust=0 -DwarningAsError=true`、全19本exit0。
- Usage20例exit0。side-sensitiveな追加4個のkernel probeもexit0。
- Complete audit168明示宣言、Full audit245宣言（生成・private含む）PASS。
  許容依存はpropext/Classical.choice/Quot.soundだけ。禁止語・新公理なし。
- 依存source closure1549ファイルをhash。全2628 import行がcollectorの構文に一致。
  254の1429・253の1653ファイルの旧hashも全不変。旧Lean凍結、barrel追記のみ。
- T7b式の読み取り専用到達解析: 選択した12根から168明示宣言中142へ到達。
  外側26は別API・回帰入口・mutual wrapper等を含み、不要と断定せず削除しない。
- 焦点ビルドのコマンド・全文出力:
  [final-build.sh](../verification/cycle255/final-build.sh),
  [final-build.txt](../verification/cycle255/final-build.txt)。最終完了12:17:49Z、exit0。
- 全体lake build、verify-lean.sh、Yulang2 runtimeは常設指示どおり未実行。
  旧依存のoleanを再利用し、全依存の独立再ビルドをしたとは主張しない。
- 独立読取レビューは9dc0b446の5本と87a36708の追加6本。範囲混同なし。
  最後のDictionaryTemplateMenu255/SourcePublicBasis255の独立読取はスレッド上限で未実施。
  自己点検・strict再ビルドは実施。独立再ビルドは全体を通じ未実施。

## 残る義務・次の優先候補

1. 実old/current role environmentが、全使用consumerのside別Supportedを導くこと。
   初期source＋public port包含だけでは足りない。lowerでintersection、upperでunionを
   そのまま通せないことを4 probeで確認したが、これは実source traceの反例ではない。
2. 固定source式保持案とsource atom拡張案を比較し、旧block solve・reobserve・新規構造
   consumer追加を通じて同一有限表現を保つこと。default/explicit、binder/capture/target、
   historical/liveを混同しない。row項、slot数、plan/effect/観測listの多重度も未解決。
3. その後、意味的に新情報のない見直しを除き、各Stepが真に新factを増やすか有限段数を
   減らす測度を証明してAccへ進む。有限ownerだけで済ませない。I50(a)のground依存上界・
   正のconstructor循環の扱いも、今回のraw syntax上界とは別に残る。

設計・義務のfield別表: [design](../design/2026-11-18-cycle255-source-consumer-basis.md),
[self-review](../verification/cycle255/self-review.md),
[polarity probe](../verification/cycle255/polarity-probe.md)。新しい意味論の質問は積んでいない。

## 公開・復旧状態

数学ソースの最終checkpointは `944d1f576283143ffa570e9f5b6d30b38db1a425`。
そのtree `c01474637cc3672d353bdaf782ef3a5ff3d4e441`を再取得し全tracked bytes照合済み。
その後19数学moduleは変更せず、補助のReach audit、宣言ガイド・検証記録・本報告を追加した。
途中公開は09e75d62（開始）、6a089fa0、9dc0b446、87a36708、944d1f57。
開始・10/20/30/40分の心拍をそれぞれ公開。最後の報告とcompleted心拍を50〜55分内に公開し、
最終treeを取得して照合した結果を親へ返す。公開先はwork/dots-mainのみ。
過去247/248の未追跡recoveryと248/249 builder.lockは今回の成果に混ぜない。
最終報告込みのファイル数はpublication inventoryに記録する。
