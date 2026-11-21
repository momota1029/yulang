# C310: 親の明示出力と、実際に生成された二子の名前付き要求の健全性

開始 2026-11-21 01:30 UTC / 10:30 JST。終了は完了心拍に記録。
前回完了 `b1bf6868ffa0792b6a034cb09fd8e8550a1c9fab`。
開始時・作業中に integration `5df350afcf817a22337ffae5d5409eef5dd85c52` の
standing orders と inbox を再読。I-55 を新規最優先として適用。
この integration は前回照合済み `b5b1ddc44f670e24537b8d8ffe39d6ecfef21ab8` から
inbox 一ファイルだけが変化。統合ブランチや言語仕様は変更していない。

## 1. 実 source の同一モデル健全性

- Checked の親は `List[Int]` を検査し、通常引数 `Int` を持つ二つの
  where を逆順に宣言していても、コンパイラは canonical 順の二発生点を生成する。
  二つの名前付き出力は、異なる where 句の同じ出力専用 binder `z` を指す。
  親の外部出力は明示式 `.variable 5` を評価する。二つの通常引数はいずれも
  `(1,1)` で `z≠1`。出力専用 binder を子の入力頭に使うことを許したのではない。
  `GeneralVersionedOutputFlow310.input_excludes_output / named_request`、
  `GeneralSharedNamedPlan310.shared_receivers`、
  `GeneralSharedNamedDependence310.makes_no_input_claim`。
- 実 parent install 後は任意の (m) について
  `Models after m ↔ Models initial m ∧ Equivalent (m 1).1 (m z).1`。
  同じ公開入力でも、私有 `z` を Bool に変えたモデルは前状態では妥当で、
  名前付き出力の式を据え付けた後には妥当でない。従って見かけだけの結線ではない。
  `GeneralSharedNamedInstall310.step / models`、
  `GeneralSharedNamedModelSeparation310.live_model_strict`。
- 実 merge が二つの入力クラスを結ぶ。追加される式は同じ型座標の `z=z` だけで
  全モデル不変。両子の出力は明示の `Int` を評価し、親の外部出力と同じモデルで
  一致する。after merge の現 Frame は ordinary 追加に対応して実際に再検証。
  親、左子、右子すべてが `Local selected`、実 resolver と検査済み辞書は
  `1[2,2]` に一致する。台帳に子の packet がなくても実同一モデル証拠は立つ。
  `GeneralSharedNamedMerge310.step / models`、
  `GeneralSharedNamedSelection310.actual_pick`、
  `GeneralSharedNamedCompiler310.exact_root_tree / nonvacuous`、
  `GeneralSharedNamedFinalFlow310.current_outputs / certified_package`、
  `GeneralSharedNamedNoHistory310.witness`。
- 同じ key 2 と alias があっても二発生点は異なる。辞書の子位置 0/1 は
  読み出し位置 1/2 へ行き、それぞれの現 Frame・出力証拠を同じモデルで回収。
  一つのかたちに畳むと arity 2 対 1 として違反。
  `GeneralSharedNamedTrace310.sound / both_addresses / not_deduplicated`。

## 2. 一般の証明に使える部分

- 任意の現親・子 Certificate と合法な二つの named request（同じ output binder を
  指す）があれば、同じモデルで親の明示式・子の明示または default 由来の実評価を
  合成できる。根の外部要求と、子の入力の観測可能性を混同しない。
  `GeneralVersionedOutputHandoff310.parent_child`、
  `GeneralVersionedOutputFlow310.paired_certificates`。
- recorded plan と ordinary extension で実際に再構成した現 Frame があるなら、
  履歴中の Holds/現在 class 式と生成辺を取り出せる。新たな installable/Stable
  を入力にせず同一モデルの子証拠を再帰合成する。C310 の実親は install と merge
  の拡張を一つに合成でき、その分岐に入る。
  `GeneralVersionedHistoryEvidence310.from_recorded_extension`、
  `GeneralSharedNamedHistoryReplay310.replayed_tree`。
- 明示式と対応する場合は、現 `Holds` 自身がローカル出力 witness を含む。
  alias だけが追加した target は同じ output 名を持つ実ローカル代表と、
  同一モデルでの class equal があるときにだけ移す。過去 packet のない類の選択
  互換性も別に閉じた。過去のある類でも同じ occurrence と拡張・所有キーを
  実際に再検証できれば、過去 Prepared を復元できる。
  `GeneralVersionedExplicitFromHolds310.certificate / live_from_represented`、
  `GeneralVersionedCheckedResidual310.installable_of_explicit`、
  `GeneralVersionedHistoryChoice310.choice_of_rechecked_history`。
- 上記の現 Frame による replay 分岐と、新 effect の互換・共同モデル分岐を
  合成。一般の ChoiceBridge と JointBridge を受け取れば、checked reachable
  endpoint が停止して返ったという仮定と実 `Classify=selected` から、
  任意の妥当な同じモデルで辞書全体の Evidence が成立する。
  帰納は渡された辞書構文のみ。 `GeneralVersionedSelectedSoundness310.on_returned_snapshot`。

## 3. (2) 診断木の返却はどこまで正しいか

- 実 merge 前は親は選択済みだが、両子は既知の入力と実 Survivor を持っていても
  alias 管理がまだ済んでおらず pending。後は選択済み。全 Models、すべての
  Survivor（候補 key・順序付き子）、登録点、生成辺、plan ledger は同じ。
  それらだけでは真の Local を再現できない。
  `GeneralSharedNamedHeadSeparation310.equal_observations_different_selection`。
- 実 alias を読む二点の observer と診断木チェッカーは、
  merge 前 `selected(1,[pending,pending])`、後 `selected(1,[selected(2,[]),selected(2,[])])`。
  先の木を pending / rejected の根単独に潰すと検査に通らない。
  `GeneralSharedNamedPremerge310.preserves_pending_children / not_flattened`、
  `GeneralSharedNamedDiagnostic310.distinguishes`。
- 一般でも認証済み current rows、返り値の実経路、停止したという仮定の下で、
  出力木と `Resolves` の完全な照合を証明した
  (`GeneralVersionedCheckedReturn310.exact_tree`)。この実例の merge 後に
  raw が一般停止するという意味ではなく、Rust や一般 Sat 実装には未接続。

## 4. I-55 の残り

**(4) は 2 本**: ordinary replay で覆えない selected について、(4a) alias を
またぐ過去 key と現選択の互換、(4b) 現 Holds/output/class を同じ全モデル証人に
まとめること。**(2) は 2 本**: (2a) 履歴を読んで一般の実 Local rows を作る
observer/compiler、(2b) 一般の Sat 成功返却について実 Step 路、停止の証明、
返した診断木の照合をそろえる実装の対応。
[厳密な内訳と次の焦点](../design/2026-11-21-cycle310-dictionary-soundness-bridges.md)。
一般健全性は未完。停止性の新規証明・有限商・手数上限の議論はせず、Rust、CI、
全 Lean build は未実行。仕様判断の質問は積んでいない。

補足: 互換・共同モデルの二橋をこの実例の三点にも実適用した。根は過去
packet の actual 旧発生点・所有キーと二拡張の合成から互換。両受け手は alias
類に旧 packet がないので互換。任意の現 Models の同じ (m) が三点の
`InstallationModels` を満たし、各 `Current` / `Installable` が成立する
(`GeneralSharedNamedCurrentGuards310.compatible_root / joint / all_installable`)。
これは受け手に新しい install step が必要、または既に実行されたという意味ではない。

次の最小の区別: 片方の receiver が新しい実 child を生成して *記録* された後、
別の発生点の同 role receiver を同じ入力で merge する例。今回は二受け手の
semantic commitment は確かだがどちらも記録されていないため、二発生点を
またぐ旧 Prepared の輸送は使っていない。次はここで古い capture/所有キーと
新しい frame の両立を実モデルで検証し、(4a) の一般化に絞る。単なる停止判定
や数学的に同じ読み出しの反復には進まない。

## 検証・公開

- 新規 Lean 35 モジュールの focused Lake build（`--wfail`, 2450 jobs）と
  全 35 ソースの個別 `--trust=0 -DwarningAsError=true` は全件 exit 0。
  [Lake](../verification/cycle310/focused-lake.txt) /
  [各ソース](../verification/cycle310/focused-source.txt)。
- 13 独立監査すべて exit 0。435 出力 / 373 固有宣言（32 公理なし）。
  それ以外は標準 `propext`, `Classical.choice`, `Quot.sound` のみ。
  [監査集計](../verification/cycle310/standalone-status.txt) /
  [1](../verification/cycle310/audit-00.txt) /
  [2](../verification/cycle310/audit-01.txt) /
  [3](../verification/cycle310/audit-02.txt) /
  [4](../verification/cycle310/audit-03.txt)。
- `tools/verify-lean.sh` は検証済み C309 作業 baseline を用いた
  diff-only 検査で exit 0。出力全体を
  [1](../verification/cycle310/diff-00.txt) /
  [2](../verification/cycle310/diff-01.txt) /
  [3](../verification/cycle310/diff-02.txt) /
  [4](../verification/cycle310/diff-03.txt) /
  [5](../verification/cycle310/diff-04.txt) /
  [6](../verification/cycle310/diff-05.txt) /
  [7](../verification/cycle310/diff-06.txt) /
  [8](../verification/cycle310/diff-07.txt) に分割。
- [Lean の評価 14 件](../verification/cycle310/executable-smoke.txt) を実行済み:
  exact dictionary、燃料不足、欠けた子、誤った右 key、二つの証明住所と
  圏外住所、実 merge 有無、前後の診断木受理/棄却。
  [入力](../verification/cycle310/executable-smoke-source.txt)。
- 中間固定ピン `9612920e43ddc0ea723a49b1254a4ac60c593836`、
  `de470bc5f8165b879ef9f2de6aa47d45bdfca394`、
  `80a6199e8434d1643b526b484d58c3d9dd5e83c6`、
  `27e84a4464f4d50a099660e5926790a467aaeca7`、
  `b24594d2761a1e8c04eef66e94253e5c532fb414`。
  公開は expected-head 非 force の `work/dots-main` のみ。
  [検証対象の固定バイト再読](../verification/cycle310/readback-substantive.txt)。
