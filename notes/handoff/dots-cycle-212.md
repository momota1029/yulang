# dots cycle 212 — I40: exact evidence-domain and terminal joint-model reductions

開始 2026-11-15T12:26:40Z。55分の締切は13:21:40Z。
integration/m1-final、standing orders、inbox I40 を取得し直した。
前211は完了済みで、並行するYulang writerはなかった。
初回integration dc8dd0f4e、途中更新73bd0e7a3をowner-firstで統合した。
公開先は work/dots-main だけ。Local/Models/Step/Stable/Certificate は変更しない。

## 主結果と完成していない範囲

1. 任意のrolesと検査済みregistryの、実際の修正済みStepの到達状態で、
   現在のselected親の子が1個でも登録済みなら、同じ親identity・同じ宣言の
   過去のplanが存在する。子のEvidenceは登録を含意するので、EvidenceNodeの
   子Evidence前提のもとでは、新規親はterminalに限られる。
2. 元のEvidenceNodeは `FreshTerminal ∧ HistoricalReplay` と**同値**。
   どちらか一方を無条件に証明したという主張ではない。頭部の構文や区間を
   制限せず、全体の場合分けを縮めた。過去の親のidentity/keyから、現在の
   occurrence・入力center・report・Frameが同じとは結論しない。
3. 任意のterminal planの全packet Holdsは、raw HeadModels、中心つき
   HeadEquations、全Outputsと同値。任意のeffectではsnapshot classの本体式
   からterminal Outputsが従う。従ってterminalのI40(B)は、**1つの代入**で
   journal Models・raw HeadModels・effect.Holdsを満たすことと同値になる。
   これとA=ChoiceCompatibleがあれば、Stableから各journal modelでterminal
   Evidenceが得られる。Aと共同代入の存在自体は未解決。
4. 任意のtotal packet・修正済みjournalについて有限の代入依存範囲を証明。
   過去/snapshot/live effect、明示/default、全子schemaを含む。journalとlocal
   の二つのモデルが依存範囲の交わりで一致すれば、spliceで1モデルを構成する。
   存在条件も同値に書いた。一致をLocalから導いたとは主張しない。
5. 補助的な構成法: nominal内でactual modeに切り替わる正確な依存範囲、
   同じtargetを許す互換な式の同時代入、完全なjournalを保つ拡張。readyな
   明示/default本体の等式から同名出力の等価性も従う。閉じた回帰例は、
   lower nominalがactualだけ読む例と、重複targetを残した構成例。
   freshness/互換性の前提は一般のselectedに対して証明していない。

**I40は未完了。B4の残りは引き続きEvidenceNodeの1本。**
Composition211の他の12 operational lawsと、条件つきB4全体の合成は変更なし。
FreshCompletionは取り下げ済みで、再び仮定していない。GeneratedChildrenは
この合成で不要。今回の結果は辞書soundnessへの補助/条件つきassemblyであり、
新しい言語規則・実行時機能・無条件のB4証明ではない。

## 反例を先に調べた結果

211の空journal反例ではEvidenceNodeは空虚なので再利用しない。
210の単純な反復captureのbottom→Int衝突はraw Preparedに拒まれる。
raw Preparedとjournal inhabitanceの別々の存在から共同代入は得られない。
選択の非OutputConflictも、journal-relative ChosenHeadがない限り不足する。
親identity/keyの一致からpoint/nonpointで変わるbinder/child centerの一致を
推論する案も退けた。実際の到達性・同じmodelでの全子Evidenceを伴う新しい
閉じた反例は作れていない。STOP例外による早期終了はしていない。

## 次の大きな穴

1. `FreshTerminal`全域で、Aおよびterminal `common_iff`右辺の共同代入を
   導く。source/予約名のfreshnessを、意味上の依存のなさと混同しない。
2. `HistoricalReplay`全域で、変更後report/端点/center/順序つき子を持つ
   現在のCertificateを構成する。従来209/210のreport一致や限定的なreplay
   条件が必要な場所を明示し、無条件の持ち越しを装わない。
3. 1/2が偽と思われる場合は、journal modelとEvidenceNodeの全前提が揃った
   到達状態の反例を先に閉じる。新しい選択の歯止めは追加しない。

## 検証・公開・制限

12新規モジュールをfocused `lake build ... --wfail`で検証。
`Audit/Cycle212Construction.lean`は全12モジュールの全定数をtrust=0で監査。
許す公理はpropext/ Classical.choice/ Quot.soundのみ。補助定義や自動生成定数
も数えるので、監査個数は独立した数学的成果の個数ではない。
全体lake build、従来umbrella Audit、Yulang2実行は行っていない。
初期の型推論・インデント・beq変換等の失敗を直し、通過版だけ公開した。
verify-leanの全文と正確な最終個数はverificationノートに保存。
2個のREVIEWは全定数を走査する新監査のrun_cmdで、手作業確認済み。

中間公開1: 07008654580f8cfe37ab7054074d1f915eb2052b、24/24 blob照合。
中間公開2: 86d0f0b11f4899f4a32ae9535d0d9853644f25b1、8/8変更blob照合。
公開のGitHub処理で最初の中間公開は約21分、次は約21分後になった。
心拍は開始、12:35、12:45、12:54、13:05に公開し、最終まで継続する。
リポジトリの既存importはowner順を保持し、新importだけ末尾追加した。
新しい意味論の質問ノートは作っていない。実行環境で利用量上限は参照できない。
最終公開commit、照合数、終了時刻、所要時間は完了心拍に記録する。

## 新規定理の索引

各モジュール内のroles・state・plan・model等は任意。前提を含む正確な型は
各リンク先の宣言そのもの。上の本文とdesignノートに量化範囲と残る前提を記した。

### GeneralDictionaryDefaultBodyGlue212

`compiled`, `same_body`, `equal_outputs`, `class_iff_bodies`, `effect_iff_bodies`

### GeneralDictionaryDefaultEvidenceSplit212

`nonempty_child_evidence_historical`, `fresh_child_evidence_empty`, `evidenceNode`, `evidenceNode_iff`, `composition`

### GeneralDictionaryDefaultJournalFrame212

`effect_iff`, `models_iff`, `models_assign`

### GeneralDictionaryDefaultModeRegression212

`exact_read`, `targets_unique`, `mode_independent`, `not_all_modes_independent`, `constructed`, `duplicated_targets`, `duplicate_independent`, `duplicate_compatible`, `duplicate_constructed`

### GeneralDictionaryDefaultModeSupport212

`congr2`, `value_same`, `values_same`, `extend_holds`, `journal_extension`, `nominal_lower_reads`, `primitive_lower_reads`

### GeneralDictionaryDefaultModelGlue212

`local_iff`, `splice_keeps`, `splice_agrees`, `common_of_overlap`, `common_iff_overlap`, `disjoint_common`, `installable_of_overlap`

### GeneralDictionaryDefaultPacketFrame212

`head_iff`, `fits_iff`, `packet_iff`

### GeneralDictionaryDefaultProvenance212

`raw_origin`, `root_le_registered`, `child_registered_parent`

### GeneralDictionaryDefaultSharedTargets212

`chosen`, `extend_holds`, `journal_extension`

### GeneralDictionaryDefaultTerminalOutput212

`generated_holds`, `outputs_of_bodies`, `outputs_of_class`, `outputs_of_effect`

### GeneralDictionaryDefaultTerminalReduction212

`terminal_of_children`, `packet_iff`, `common_iff`, `installable_iff`, `stable_terminal_node`, `no_output_binders`, `no_output_names`, `associated_inputs_only`

### GeneralDictionaryDefaultTotalFrame212

`variables_sources`, `reads_member`, `value_same`, `schema_iff`, `plan_schema_iff`, `body_variables_sources`, `body_iff`, `class_iff`
