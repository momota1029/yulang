# cycle261: 複数実requestとEqualOutputsのrebase表

状態: Draft。2026-11-18。I-51/I-52に従い、言語の意味は変更しない。

## 本命と順序

前cycleの単一request decoderを、そのまま複数requestへ繋がない。
まず任意の固定Plan・有限request列について、各bodyの実lookup/target/scopeと
同name target間のEqualOutputsを、名前付きrequestの固定tableへまとめる。
終点Models iff基底Models∧ClassEffectsを狙う。翻訳失敗とmissing bodyは
constraint stateの不充足とは別に扱う。run成功はモデル存在判定ではない。

次に実sourceのalias classに二つのrequestがある回帰へ接続する。
候補は既存AllocMergeのaTarget/bTarget。旧V7の実trace・HistoryModelsと
EqualOutputs矛盾が既にあるので、その有限rebase義務を閉じる。
これは現在のversioned全source compiler完成ではなく、境界差を明記する。

## 表現

- body住所: (owner, body-kind, request.name/target, equation-index)。
- EqualOutputs住所: 別kindの固定schema。旧owner-only表と混ぜない。
- 同じrequestを何度見ても同じ住所、違うrequestには違う住所。
- 各factの意味は固定全table中の該当義務の連言とする。住所非衝突は別に証明し、
  ひとつのfactが別要求の意味で済まされることを防ぐ。
- markerは言語のCommitted判断と同一視せず、今回必要なら実owner markerと
  namespace table markerを分ける。現時点で表のconstraintsだけを一歩で記録する。

## 証明する型と未完

任意固定state/root/plan/modelで、実requestsを入力したtableの全facts成立 iff
versioned ClassEffects state root plan model。missing body/unknownの検査が成功する iff
Ready（実lookup存在・翻訳済み）。有限stateの終点モデルはこの全factsと基底モデルの連言。
固定tableのobserverからClosed・有限完了・Step Accを導く。
実requestsの取得はnoncomputableなalias判定を含む。実例では有限列を具体的に求め、
一般の実行可能alias inspector・全trace固定candidate producer・pool閉包は未完とする。

旧source regressionの矛盾は既存の型同値制約を要求した結果であり、新たな拒否規則を
導入しない。前半の定理が条件付きなら実fixtureがその前提を満たすことを後半で示す。

## 実source接続の確認

AllocMergeの二つのrequestは実alias classに所属し、反例用に足した内部引数ではない。
全requestsのmembership iff `[⟨0,aTarget⟩,⟨0,bTarget⟩]` を証明した。
leaf実lookup bodyはInt、二つのtargetは異なる。固定class表はReadyを満たす。

ただし、現在のraw状態の制約だけを基底にすると、過去のparentが要求した
`aTarget = Int` と `bTarget = Variant Int` の履歴を失う。次はHistoryModelsを保持した
新終点が不充足となることを、実EqualOutputsから示す。raw-only版のuniformモデルとの
対照も取る。有限constraintsのrunが成功することとモデル存在・source受理を混同しない。

## 実alias class・履歴保持の接続

二つの実requestから6factsのtableを構成し、有限runは初回で終点へ進み以後停止する。
一方、過去parentのHistoryModelsと終点ClassEffectsの連言は不充足。終点生成の成功は
充足性判定ではない。旧V7の実到達終点と拒否判定にも接続し、誤ったraw-only版の
uniformモデルと対照する。現在のversioned全source traceの再構成とは区別する。

旧fixtureのGood・Supportedから現行versioned Frameを構成し、raw-only uniformでは
leaf Evidenceが存在することも確認した。これはHistoryModelsを満たす証拠ではない。
履歴は当該fixtureについて、初期snapshot Modelsと固定2出力制約へ同一assignmentで
圧縮できる。任意履歴・将来journalの一律有限化とは主張しない。

独立読取レビュー（前半5本）では射程不整合なし。独立buildは未実施。
EqualOutputsの住所は固定schema内indexに依存し、可変・並べ替えtableで同一keyの
意味が不変とはまだ主張していない。body側の位置非依存住所と混同しない。
