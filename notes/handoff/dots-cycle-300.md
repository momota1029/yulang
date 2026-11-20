# Yulang dot 作業報告 第300周

2026-11-21 00:30 JST の回、実作業開始 2026-11-20 15:34:00 UTC。
前周の完了 pin は `8ea24d0ffabde73f974a4556b846a17ed2eb6feb`。
最新 standing orders・inbox の I-54 に従って B4 の実 source を進め、公開は `work/dots-main` のみ。

## 結果

1. **V8 の深さ2の例で、二回の raw install を実際の遷移として証明した。** 第299周で条件だった二つの `Installable` を、それぞれの raw 状態で全て証明した。最初の据付で外側の Display から中央を生成。第二候補は第一据付の実 raw／center site、拡張済み context、所有済みキーから再構成し、末端を生成した。両段とも同じ全モデル集合を保つ。記録される辺は空 → 外側→中央 → 外側→中央・中央→末端。どちらの遷移も raw refresh では置き換えられない。
2. **最終状態の型と辞書を同じモデルで閉じた。** 親の再演は第一段で既に所有したキーを保持し、第二段の制約と両立するモデルのもとで frame を再構成した。中央と末端も最終時点の実 frame から作り、全ての最終モデルについて根の辞書は `1 → 1 → 3`。初期と中間では、どのモデル・payload に対しても完成した根辞書 evidence は存在しない。旧 rigid の深さ2の例とは別で、こちらは V8 raw である。
3. **三つの最終行が独立した V8 選択判断と一致し、有限 reader でも同じ辞書になった。** 親・中央・末端を別の occurrence として保持し、親と中央で同じ実装 key 1 が現れることを保った。C299 の reader に渡した最初の成功 fuel は `[3,2,1]`。三つとも最終状態の `Current` と `Installable` を持つが、すでに `Committed` であり、再据付条件は成り立たない。固定最終状態の `EvidenceAt` を証明した。任意の到達 source の `EvidenceNode` ではない。
4. **この固定初期状態からの raw 遷移を尽くした。** 最初の唯一の後続が第一 install 後、その唯一の後続が第二 install 後、最後は後続なし。未確定の予約 ID の値を変えられるモデルを使い、誤った refresh や等式追加を除いた。3相の残り raw 歩数は `[2,1,0]`。これは辞書 reader の fuel とは異なる。特定の初期状態・registry・root の証明で、V8 の一般停止性は主張しない。

## 主な定理の範囲

- `GeneralDepthTwoFirstInstall300.enabled` と `GeneralDepthTwoSecondInstall300.enabled`: それぞれ固定された実 effect が、固定された初期および第一据付後の raw 状態で全据付条件を満たす。各 `actual` は実 `Step`。 `GeneralDepthTwoEvidence300.actual_dictionary` は二歩、末端の生成、モデル非空、全割当での初期・最終 `Models` 同値、全最終モデルでの親辞書をまとめる。
- `GeneralDepthTwoFrameCarry300.frame_carried`: 任意の型付き frame に対して、旧と追加の所有キーの和が必要キーを覆い、拡張した plan を満たすモデルがあるなら、普通の制約拡張で frame を再構成できる。これは raw refresh イベントの導出ではない。拡張後のモデルや新しい所有キーを仮定なしに捏造しない。
- `GeneralDepthTwoObserved300.exact_on_actual`: 固定最終状態の全登録行・任意の辞書について、燃料3でその辞書を返すことと独立 `Classify ... (.selected d)` が同値。 `GeneralDepthTwoCertifiedRead300.evidence_at`: 固定最終状態で到達 root／生成子、局所選択、安定性、子 evidence を入力とする EvidenceAt。別途 `compiled_final` で子辞書を仮定せず、実行済み有限読み取りから根を構成する。
- `GeneralDepthTwoMachine300.exact_step`: この三状態の任意のペアに対し、本来の raw 一歩と相機械の一歩が同値。`phases_complete` はこの固定初期からの任意の到達経路を三状態のいずれかに限る。`source_accessible` も同じ初期だけ。`GeneralDepthTwoRootAvailability300.exact_availability`: 任意の三相とその相の任意のモデルについて、根の辞書 evidence があることと最終相であることが同値。

## 検証・未確認

- Lean 4.35.0 の差分を分離再ビルドし **28 モジュール**、独立監査6本で **全 267 定理**を `--trust=0 -j 1 -M 3200 -DwarningAsError=true` で確認。新公理なし（標準の `propext`、`Classical.choice`、`Quot.sound` のみ許可）。旧監査29本、4実行の出力バイト一致、barrel 末尾・source SHA-256も確認。
- `tools/verify-lean.sh --no-build` を前周と正確な統合木で実行し、[全文ログ](../verification/cycle300/static/)と[検証手順・監査](../verification/cycle300/)を保存。前周木 `3e886fa9ddca3d749392a3169f3f9092c076a692`、再読した統合 `1e37baa34586187f63709b0dd46d068752cc10c7` の木 `2e2894f46c9bc2303708ab8c8b8a4405d187acba`。standing orders・I-54 inbox の blob は開始時から不変。
- [旧 Yulang2 oracle](https://github.com/momota1029/yulang/blob/55574b6052ef1534fd0fc36d6d3617ebede59a0e/notes/audit/x-oracle.md)の X1 はより狭い子 Display 使用、X2 は増大 where と旧 lowering の差。どちらも今回の V8 深さ2の主張の根拠ではない。Rust・Yulang2・全 Lake ビルド・CI は未実行。仕様、既存 Lean kernel、Rust は変更なし。仕様選択は不要で質問ノートなし。枠の使用量は不明。

次の候補は (1) この二段で使った実 frame／所有キー輸送を別の到達 source へ適用し、有限 compiler の被覆条件を明示、(2) 実 depth2 の独立 observer と二段 effect の一般化、(3) raw 停止を狙うときは第298周の silent 相の障害を受け継いで別途検証、の順。今回の有限相から一般停止・任意の証跡自動生成は導かない。

[次の入力族と残る条件](../design/2026-11-20-cycle300-next-family.md) に、観測済み scalar と単なる scalar 方程式の違い、実 frame 輸送、選択 rank と raw rank の分離を記した。監査目録は行末に直接書いた二つの証明項も取りこぼさないよう修正し、同じモジュール全体を改めて検査した。

- 最終報告書の固定時刻: 2026-11-20T16:24:07Z（経過 50.12 分）。前周からの変更 68 ファイル（完了心拍・報告を含む）。
  書き込み後に固定 pin で報告と完了心拍を読み戻す。
