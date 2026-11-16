# dots cycle 220 — I-41 V8共有等式の再実装と残余

## 結論

**EvidenceNode は未完成。B4全体の証明完了とは報告しない。**
I-41 の V8 target、実際のhead中心の共有等式、具体的な共有矛盾境界、12則、EvidenceNodeのみを仮定する合成、199/202/204/206/218回帰を新環境で実装し直した。
cycle219の失われたソースを回収したのではない。

## 復旧・基点・運用

- 開始: 2026-11-16T06:33:57Z。
- integration/m1-final: `383a655201fb12543c163b89b75b1bde3511ebe3` を再取得し、standing orders、inbox末尾I-41、cycle219公開報告を読んだ。
- 前回は環境切断によりコード未公開。今回は新しい書込み可能環境を確認、integrationから独立worktreeで再構築した。既存の別タスクのtoolchainを読み取り利用し、Yulang用focused cacheを作った。
- 公開はGitHub appを通し **work/dots-mainのみ**。integration/main/yulang3への書込みなし。
- 以前のwork branchがintegrationの218モジュールやI41より古かったため、中間treeの基底をintegrationにし、旧workの心拍とcycle219報告を保存した。中間commitは双方の履歴を親として保持する。
- 親からの上限は開始55分以内の検証・公開・報告。約10分前まで独立課題を続け、最後を検証・公開に充てた。

## I-41受入条件と主要定理

1. **共有等式（補助／健全性）**: `HeadSharing220.equations` は同名head useのactual originの全対を有限列で列挙。`holds_iff_agreement` はFinishedなheadについて旧Agreementと同値。constructor解釈の単射性を仮定しない。自己対についてもreachable frameのactual値の存在・一意性をPrecision220で示した。
   - `packet_holds`, `effect_holds`, `committed_holds` は既存のtotal packet/effect/schemaが既にactual sharingを強制していたことを示す。
   - `packet_with_sharing_iff`, `effect_with_sharing_iff`, `committed_with_sharing_iff` は明示的共有条件を加えても同じ命題となる。したがって今回はStepを変更していない。「区間端点だけの比較」を新しい意味として採用したのではない。
2. **V8分類（仕様の拒否／補助）**: `B4TargetV8` はSharingConflictを追加し、曖昧の優先と拒否理由を明示する。concreteのFeasibleは、現journalモデルと当該keyの現Frameが共有等式を同時に満たす存在命題。AtKeyはbaselineモデルとFrameを要求し、どのモデル・Frameでも共有が成り立たないときだけ矛盾とする。
3. **12則（補助）**: `HeadSharingLaws220.twelveLaws roles` は任意rolesについて、定義されたchecked/initial/reachableの量化範囲で12 operational/order則を証明。StepとModelsは旧Default208のまま。selected child relationの制限、規則順序輸送、canonical executorを新Localに合わせた。
4. **合成（健全性・完全性の条件付き外側）**: `HeadSharingComposition220.composition` は **B4SkeletonV8.EvidenceNodeのみ** を前提として、同じ境界・executorのfull Statementを導く。GeneratedChildren/FreshCompletionを追加前提にはしない。EvidenceNode自体を証明したとは言わない。
5. **回帰（補助）**: `HeadSharingRegression220.final_rejected/final_not_pending/final_not_selected` はGroundCopy218のsaturated final demandを新境界で拒否とする。`Prior220.Rejected199`は拒否、`Default202`と`Join204`は選択と各currentモデルのtotal evidenceを保持。`Install206.genuine_default_change`は実Step、intモデル保持、bottomモデル除外を保持。
6. **非反復断片の保守性（補助）**: `Accessible220.holds_of_reachable_frame` はreachableなcurrent FrameがNoDistinctSameNameを満たせば、全currentモデルで共有を証明する。一意keyならsharing conflictなし、および旧V7 selectedとV8 selectedの同値はmodel inhabitationを要しない。Feasibleの存在にはinhabitationを明示する。head-use names Nodupを十分条件とする系もある。
7. **厳密な残余仕様（補助）**: `Specification220.selected_iff_feasible` はinhabitedかつreachableな状態で、V8 selected iff V7 selected∧同key Feasible。`common_iff_sharing_overlap` はsource/point/ground/coverage/checked/trace/current Frameを前提に、journal+raw head+head equationsの共通モデル存在 iff journal+sharing+protected Overlapの共通モデル存在。

8. **分離したamalgamation（補助）**: Amalgamation220はcurrent Frameのp0/p1 aggregateがprotected supportと分離していればOverlapが自動成立し、sharing witnessからcommon head witnessを作れると証明。全inputNameのcaptureがsingletonなら十分。一般のhistorical captureにこの条件を仮定なしで付けたのではない。
9. **tight raw provenance（補助）**: RawSupport220.private_sources_localは一回のprivate headのsemantic raw supportが旧support＋当該宣言のp0/p1だけに含まれると証明。private_new_originは新規源のinvocation/key/inputName/purpose/positionを精確に特定。全reservedの粗い上界を避ける。別keyの源は元から旧supportにあったものに限る。全traceのfreshnessは未証明。
10. **意味的supportの共通モデル橋（補助）**: SemanticSupport220.Dependsは有限pool上で一致する任意2assignmentでModelsが同値という独立条件。refresh/reobserveで同じpoolを保持し、extension_iffはこのpoolに関するcommon raw head extension iff Overlapを証明。common_headでexact HeadEquationsまで進む。current syntactic journalSources全体を保護する必要はなくなるが、任意selectedに適切なDepends/Overlapを供給したわけではない。

## 未完了、次に必要なもの

- full `B4SkeletonV8.EvidenceNode (HeadSharingBoundary220.boundary roles)` はOPEN。外側の残りfieldはこれ1本。
- 選択からはsharing-compatibleなモデルの存在が得られるが、raw HeadModelsの独立証人と同じモデルとは限らない。一般amalgamation、特にcurrent protected supportのOverlapを得る橋が未証明。その後、packet/effect共通モデルとChoiceCompatibleを通してInstallableを組み上げる必要がある。
- Stable+InstallableからCommitted、全currentモデルのpacket/schema、certificateを得る既存の橋は使える。「存在条件だから全モデルEvidenceが直ちに偽」とは言えない。
- cycle219にあったstale aggregate案は、この環境で閉じた反例として確認していない。単純な古いloose extremaと新しいpoint extremaの不一致は、旧raw ordinary mergesが残るためPrepared/Survivor自身を失う可能性がある。反例成立として引き継がない。
- 次課題: (1) selected/stable reachable Frameのamalgamation、(2) common headからfull packet/effect/ChoiceCompatibleへの接続、(3) historical/current replayの同じfieldへの適用。
- 詳細: `notes/design/2026-11-16-cycle220-evidence-gap.md`。意味論の新しい決定はしていない。

## 中間公開と意味論レビュー

- `ff34dc3bc5fc63f77087cde297a58310cff765fb`: target/skeleton、設計、105 constants監査のcheckpoint。remote tree照合済み。
- `1cafdcddd5853a540de206ffad62dfb2826a2acc`: concrete/回帰15modules、269 constants監査checkpoint。17変更entryをremote treeと照合。
- その後のレビューで、中間ConflictがUniqueだけを要求しSafeKnownを欠いていた点を発見。I41は選択後の等式であり、旧OutputConflictと同様の既知・検査済みguardに合わせる必要がある。中間版は最終的な仕様適合完了と扱わない。最終ConflictはUnique∧SafeKnown∧AtKey。修正後focused1410jobs PASS、Semantic220がV7 pending/ambiguousの完全同値を証明。rejected iff 旧rejected∨Conflict、旧selectedから新rejected iff Conflictも証明し、中間版の穴を閉じた。

- 訂正公開 `c75cb1e0af1a2d959d3ad8cb2067a198899df6a5`: SafeKnown・semantic preservation・断片を公開し、19変更entryとrefを照合済み。

## 検証

- 修正後 `lake build ...Composition220 ...Regression220 ...Witness220 ...Accessible220 ...Specification220 ...Prior220 ...Amalgamation220 ...Semantic220 --wfail`: PASS 1410 jobs。
- `lake build Yulang.GeneralDictionaryHeadSharingRawSupport220 --wfail`: PASS 958 jobs。
- `lake build Yulang.GeneralDictionaryHeadSharingSemanticSupport220 --wfail`: PASS 1335 jobs。
- 訂正checkpoint全定数監査: `CYCLE220-COMPLETE-PASS: 311 constants in 20 modules`。以下の最終再監査がその後のraw provenance/semantic support追記まで含む。

- `lake build Yulang.GeneralDictionaryHeadSharingComposition220 Yulang.GeneralDictionaryHeadSharingPrecision220 --wfail`: PASS 1316 jobs。
- `lake build Yulang.GeneralDictionaryHeadSharingRegression220 Yulang.GeneralDictionaryHeadSharingWitness220 Yulang.GeneralDictionaryHeadSharingPrior220 --wfail`: PASS 1398 jobs。
- `lake build Yulang.GeneralDictionaryHeadSharingAccessible220 --wfail`: PASS 1342 jobs。
- `lake build Yulang.GeneralDictionaryHeadSharingSpecification220 --wfail`: PASS 1341 jobs。
- `lake env lean --trust=0 Audit/Cycle220Target.lean`: `CYCLE220-TARGET-PASS: 105 constants in 2 modules`。
- 初回 `lake env lean --trust=0 Audit/Cycle220Complete.lean`: `CYCLE220-COMPLETE-PASS: 269 constants in 15 modules`。
- 許可公理はpropext、Classical.choice、Quot.soundのみ。個別の主要定理表示だけでなく新モジュールの全定数を走査した。
- 既存Leanファイル凍結：barrel/Audit/READMEのintegration内容が厳密なprefixであることを確認。変更は追記のみ。他の過去Leanファイルは変更しない。
- **全体 lake build / tools/verify-lean.sh は実行していない**。standing orders末尾のfocused-only指示に従い、全体gateは監督役が実行する。
- 最初のbaselineバックグラウンドshellは空logのまま終わり、成功として数えていない。後のfocused buildが必要依存を実際に再構築した。

## Yulang2との照合

work/dots-auditを取得しx-oracle.mdの既存実機結果を読んだ。古い具体例の一致は参照したが、今回の任意区間・同名actual sharing・amalgamationの完全一致をYulang2で検証したとは言わない。新しいYulang2実機は未実行。意味論の権威はI41とspecのowner決定。

## 最終記録

最終検証・公開・時刻は追記予定。使用量の枠は不明。

## 承認後の最終公開整理（2026-11-16 09:54 UTC開始）

本人の再開承認を親が確認した後に、最新integrationとI-24/I-27を再確認。凍結されたAudit.leanとREADME.mdはintegrationの厳密なbytesに戻し、cycle220で誤って追記した行を撤回する。既公開Cycle220Complete/Registeredは既公開bytesのまま保存し、新しいCycle220Final.leanに全21モジュール監査を置く。RawSupport220とYulang.leanは既公開内容への末尾追記のみ。remote-only cycle219報告を保持する。新規監査・設計ノートが登録と説明を担う。

回復再監査: `lake env lean --trust=0 Audit/Cycle220Complete.lean`（整理前の全21モジュール版）は324 constants PASS、exit0。整理後は同じ監査を新名Cycle220Finalで再実行する。全体gateは未実行。EvidenceNodeは引き続き未証明。

RawSupportの旧namespace終端も既公開bytesとして保持し、新補題は末尾でnamespaceを再開して追記する形へ整理した。Cycle220Finalの全定数監査がこの整理後のソースを対象にする。

整理後の最終検証: focused build PASS 1336 jobs、exit0。`lake env lean --trust=0 Audit/Cycle220Final.lean` は `CYCLE220-COMPLETE-PASS: 327 constants in 21 modules`、exit0。namespace再開のlocal notation補助定数も監査対象となるため、整理前324から327になった。凍結2ファイルのintegration bytes一致、既公開監査2ファイルのremote bytes一致、Yulang/RawSupportのremote prefix保持、git diff --checkを確認した。今回の公開は最終成果・新監査・報告・心拍の11 entry。公開済cycle219報告とその他のremoteファイルを基底treeから保持する。B4/EvidenceNode完成の主張はない。
