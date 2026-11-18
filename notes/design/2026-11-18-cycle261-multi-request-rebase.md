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

## 位置非依存EqualOutputs住所への更新

新kind3で同name要求の順序付きpairを(name,target)二組から注入符号化した。
旧kind2のindex表とは混ぜない。同じpairは列位置・列の追加・並べ替えに依存せず
同じ意味を持つ。body側も固定Planに対する全requestの局所意味として定義し、
実観測のsubsetに意味が依存しないようにした。住所衝突なしから全fact成立 iff
そのsubsetのClassEffectsを示す。任意Plan間の意味同一性までは主張しない。

固定有限candidate列に全selected requestが入るという明示前提の下で、動的observerの
Closedとsettle完了が得られる。成功Stepのモデル変化は現在のモデルと選択された
実ClassEffectsとの連言に厳密一致する。候補producerや全source traceのcoverageは
この前提に隠さず未完とする。翻訳検査、制約生成、モデル存在判定は引き続き別物。

レビュー補足: AllocMerge例では二つのbody自体も両方Intを要求するので、履歴との
不整合をEqualOutputs「だけ」の効果とは説明しない。EqualOutputsと履歴との矛盾を
示す補題はあるが、body制約も独立に同じ不整合を生む。

成功traceについて、各Stepで実際に選択されたrequest列の記録を構成し、その同じ記録で
全assignmentについて「終点Models iff開始Models＋全履歴ClassEffects」を証明した。
記録は監査用の存在証人であり、runtime storageに追加されるjournalではない。
AllocMergeの任意atoms段階で実requestsは同じ二候補内にあるため、このfixtureでは
任意state→atoms選択からClosedを実証する。ただしrequest取得は既存のnoncomputable
alias関数であり、有限stateから一般sourceを復元する実行compilerではない。

## 動的観測の実Planへの橋

レビューが区別した固定Plan解釈について、AllocMergeでは全atoms-stageの実bodyがIntで
同じため、固定tableのEffects iff実観測stageのcandidateのClassEffectsを別に証明した。
Good・Supported・現在raw Modelsを追加すれば、実packet Holdsとleaf Evidenceへ接続する。
実requestsを用いたproposalのwriteも固定6facts書込みと同じで、観測runは固定表の
実行可能runと関数等号、初回一歩・以後停止・成功Step数≤1となる。
これは任意の変化するPlan、一般source observerへは拡張していない。

固定候補layoutを先に検査するfinishも追加する。missing/unknownは内部layout error、
basis外は別errorとして保持し、成功なら全選択履歴Readyと正確なモデル連言を保証する。
ただし候補に未使用unknownがあれば失敗し得るため、その失敗を言語の拒否とは呼ばない。
成功してもモデル存在は保証せず、履歴保持の実AllocMerge終点不充足と両立する。

内部CandidateBoundaryProbeでは、実requestsに属さない未定義name1を候補表に追加すると、
空の選択observerは即完了するのにlayout検査はmissing errorを返すことをkernel検証した。
これは全candidate検査の保守的な内部エラーで、実sourceの拒否反例ではない。

## 一般sourceへの残りを具体化した確認

`SourceOwnerCandidates252.mixed_finite_owners` と `PublicPorts253.mixed_finite_ports` を
再読した。いずれも実source由来だが、Generated・Installable・未Committedという実installの
条件が付く。これを全ての保持済みsiteのrequest targetにそのまま適用するのは不正確。
`HeadOutputs.mem_requests_iff` は実alias classのrequestを保持siteのoutputsへ戻せる。

そこで固定snapshotについては、全site.outputsをcandidate列に取り、任意rootの実requests
が含まれることを前提なしで証明した。候補列自体はalias判定なしに計算できる。
これで固定snapshot上の動的root選択のClosedとClassEffects書込みへ接続した。
各snapshotで有限列を作り直すことは、全traceで一つの有限basisが使えることの証明ではない。
次の本質的義務は、初期siteと新規installの両方について保持request targetの固定pool所属を
帰納的に示し、同じownerのPlan・capture意味を更新しても過去factsを再解釈しない橋を作ること。
実request取得のalias判定はなおnoncomputable。一般Evidence/Permittedと12性質の移植はその後。

## 次の実行可能alias観測の具体設計（未形式化）

実 `SaturationState.Alias` はaliases辺の反射・対称・推移閉包だった。
K2の意味的型同値判定ではない。したがって固定snapshotのrequest抽出だけなら、
有限無向グラフの到達可能性で置換できる見通しがある。既存 `JointEquality.alias_same`
もalias辺列だけに依存することを確認している。

- 頂点候補は root identity、全query/site identity、全alias辺の両端を含める。
  site identityだけでは、中間辺頂点がsiteにない経路を落とすため不十分。
- visited={root}から両方向の隣接辺を反復追加する。strictな追加時には未訪問頂点数が減る。
- 停止時の両方向edge-closed性から、Alias導出の帰納法で完全性を示せる。
  soundnessは各追加にedgeとtransを付ける。有限長最短経路補題を別に仮定しなくてよい。
- 元のsites列を元の順序でfilterし、outputsをflatMapする。重複を勝手に消す必要はない。
  述語一致を示した上で既存requestsとのlist等号を証明するのが次の目標。
- この算法は固定snapshotの実行可能観測を解消する候補であり、source更新後も同じ
  candidate basisが使える不変条件、Plan/capture意味の接続、言語受理判定とは別。

`alias-closure-prototype.py` は4頂点の全64無向グラフ×5rootを独立union-findと比較し、
site外の中間頂点、出力列の順序・重複保持も試した。これはPythonの算法実験のみで、
LeanのAlias同値定理やYulang実機検証としては数えない。

実center mergeとrefreshではraw sitesが変わらないため、snapshot candidate列はliteralに
保存されることもLeanで確認した。実versioned installでは既存 `Absorbed` が成り立つとき、
新raw childのoutputsは既存alias requestsに含まれ、candidate membershipを保存する。
そこからinstall後の任意root requestsを旧poolへ戻せる。list重複・長さまで同じとは言わない。
`Absorbed` は新child出力が既に表現済みという条件であり、任意sourceのinstallに自動的に
成り立つとはしていない。これが新public targetを許す一般sourceへの残る帰納義務である。

### 次の優先順位

1. `GeneralRebaseAliasClosure262`（候補名）：上記有限alias算法をLeanで実装し、
   `Alias` iff computed membership、続いて既存requestsとのlist等号を証明する。
2. `GeneralRebaseRequestPool262`：初期source outputs＋owner由来public portsについて、
   新規installが追加する全child request targetのpool所属を示す。Absorbedの場合だけの
   今回の保存補題と、真に新しいpublic targetの場合を分ける。
3. `GeneralRebaseSnapshotAdvance262`：Plan/captureが変わるときの既存fact意味の保存と
   mixed-time packetの証明書を接続。任意変更Planの意味保存を仮定して終えない。

質問を要する言語意味の選択は今回発生していない。上記は実装・証明義務であり、
ユーザーに未解決数学を承認してもらう問題にはしない。
