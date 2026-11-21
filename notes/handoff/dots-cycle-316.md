# C316: 親も子も選ばれる安定状態で、現在の辞書健全性を反証

2026-11-21 07:30 UTC / 16:30 JST 枠。開始時に integration
`fc059f2157cf0dc4bcf35697ccc956951b174571` の常設指示と inbox を再読し、
C315 の完了 `5e22ff4b1aed2868798b9a340174051ad40ddcca` を照合。
再確認でも両指示の版は不変。I-55 (4) の一般辞書健全性を優先した。

## 結果

**現在の Lean の mixed/source 境界について `EvidenceNode` は偽。**
今回は C315 の棄却子を使った補題だけの反例と異なり、同一の到達状態で親・葉がともに
安定し、同じ live model で実生成の葉の辞書証拠があり、**再帰的 `Classify` も親・葉を選ぶ**。
しかし親の現在の証拠はどの live model にも存在しない。

- `GeneralLiveCompoundCounterexample316.not_evidenceNode` は現在の
  `B4SkeletonV8.EvidenceNode (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)`
  を直接否定。`not_revisit_rhs` は子の証拠を前提とする C315 の
  共通モデル条件 `RevisitRhs` も否定する。単純な過去の frame の replay も不可能。
- `GeneralLiveCompoundFullResult316.selected_without_evidence` は、実到達、親・葉安定、
  再帰的選択、モデル存在、選んだ辞書の証拠なしを一つの定理にまとめた。
  `not_sound_if_returned` は、**この状態を返すなら**任意の executor の `DictionarySound`
  が偽という条件付き結果。実際の Sat や Rust がこのスケジュールを採るとは主張しない。

## 試験と原因

既存 fixture の親 role 0 と別の role 1 に終端の variant 規則（宣言316）を置き、
親（宣言238）の where がその role 1 を要求する実 checked registry を組んだ。
同一roleの構造規則は nominal 親を必ず棄却するとは限らず、保留を起こすので使わない。
生成する葉は variant の payload を捕獲し、この出現では関連出力を要求しない。

初回親据付 → nominal の再観測 → 2段階の実構造 refresh → 葉の実据付。
増えた予約名を含めて Step を再構成した。葉据付後の生モデルは据付前と同値だが、
辞書 journal は葉の packet と binder を追加する。使わない新予約名には独立に値を
与えられ、追加の refresh/equate には進めないことを証明した。親は共通 packet が
なく、葉は既に committed なので、どちらにも追加の据付はない。
`GeneralLiveCompoundLeafInstall316.reachable`、`GeneralLiveCompoundStable316.halted`、
`GeneralLiveCompoundPostFrames316.leaf_evidence` と `no_root_evidence`。

`GeneralLiveCompoundCulprit316.only_lower` は、到達後の任意の live model が現ヘッドを
満たすなら、二つの where 行のうち **下端一行だけ** が失敗することを示す。下端の番地が
同じまま、旧値は「厳密な空レコード、またはフィールド0だけを持つ厳密レコード」の
variant、現値は幅を許す空レコードの variant となる。上端・実際の子の中心・親の
関連出力をこの衝突と混同していない。実 root の既存選択鍵に衝突がないことも別に確認。候補の選択、受理範囲、spec の変更なし。

提案した新番地に現 RHS を入れても、実旧 journal・現ヘッド・class と葉の辞書証拠を
**同じモデル**で保てることを `GeneralLiveCompoundProposedRepair316.feasible_without_rewriting_history`
で確認。今のコンパイラの旧番地が失敗することもそのモデルで同時に確認した。
この試験は番地の可能性を示すだけで、現コンパイラの書き換えや子 descriptor の移植は未実装。

## 残りと次の判断

- **(4) 2群。** (4a) 別 owner に関する prior-choice/alias 宣言鍵の一般証明は未解決。
  (4b) 同 owner 再訪の旧・現 where RHS の一つの共通モデルは、今の表現では**偽**。
  新しい表現・証拠を、現行の受理意味を保って実到達に接続する修正が必要。
  (4b) は単に「未証明」ではなく、同じ定理の証明を続けても閉じない。
- **(2) 2群、未変更。** 実履歴を含む一般 observer/compiler の生成、および停止成功を
  仮定した到達経路・返却地点の安定・宣言的分類との一致。
  具体的な1状態の安定は示したが、一般停止性・手数・順序独立を追っていない。
- 次は [設計ノート](../design/2026-11-21-cycle316-live-child.md) のとおり、
  where 端点の版つき割り当てを実コンパイラ・新旧 child descriptor・既存 commitment に
  接続し、同じ選択木の証拠を復元できるか検証する。数値 owner と occurrence 全体を
  同一視しない。仕様変更の求め、質問ノートなし。使用枠残量は不明。

## 検証・公開

[対象ビルド、全ソースの trust=0、独立監査・追記差分のログ](../verification/cycle316/verification.md)。
Rust・CI・全体 Lake build は未実行。実行文脈の規則や言語の仕様を変更していない。
`work/dots-main` のみ旧 head 指定の非強制公開、固定コミットで全差分を読み戻す。
所要と完了時刻は同じコミットの heartbeat に記録。

対象 32 モジュールと全32ソース検査、監査251件、対象環境公理検査93,842宣言、
追記差分検査はすべて通過。完了コミットで公開する周期差分は、別更新の heartbeat を除き
60 ファイル。開始後の各10分の heartbeat と、本体の中間公開を同じ作業ブランチに残した。
