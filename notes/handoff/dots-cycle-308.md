# cycle 308: 最初の再観測が、据え付け履歴と現在の証明をどう分けるか

開始 2026-11-20 23:35:22 UTC（11-21 08:35:22 JST）。終了・正味経過は同じ公開の完了心拍。
C307 の完了心拍と報告を `abfa54cd3382d6d2b7fc9cb0961e71a10125ec0a` で確認。
統合版 `9c4a7274b51d423fc900bc8a3af861c0b9b07119` の standing orders と
inbox を開始・途中に読み直し、ACTIVE / I-54 の B4 本線を適用した。
終盤に統合版は `faf6b87900b6c446461b1d5f9133467abbb7dee912` に進んだ。
二つの指示ファイルは不変で、追加された C306 の Lean 47 ファイルは継続作業木と
全バイト一致、40 の barrel import もすべて既取り込みと確認した。
I-51 の監査ファイルは相互 import せず、I-52 の実 Step と独立 diff 監査、
I-53 の同一公開での barrel 追記を守った。既存 Lean の変更は barrel 末尾への import のみ。
変更先は `work/dots-main` のみ。使用量の枠は不明。

## 実 raw 運転

1. **据え付け先行側の実ダイヤモンド。** C238 の実 `installed` から、
   (a) 最初に nominal を point にする→三つの既予約 head を一括で refresh、
   (b) loose descriptor のまま三つを refresh→大きくなった snapshot の正しい
   nominal を point にする、は各二手でまったく同じ C307 `upperState` に至る。
   任意の一歩の `Step registry root installed upperState` は存在しない。
   refresh 一手では loose の (4,2) を point の (2,2) に置き換えられず、
   その他の候補は旧物理スロット数を変えない。同じ full model の話だけではない。
   主要: `GeneralMixedCompoundEarlySquare308.square`,
   `GeneralMixedCompoundEarlyNoShortcut308.no_shortcut`。
   証明書の cache は旧/新の input facts・履歴・query 読み戻し・class/alias の保存を
   それぞれ確認して移した。

2. **C238 の開始から最初の二手を厳密化。** 任意の (t) について、
   `Step registry root before t` と「(t=installed) または (t=pointBefore)」は同値。
   `pointBefore` からの任意の一手は `pointFirst` への実 install に限る。
   captured 区間は (2,2) で、旧の (4,2) で先に据え付ける経路とは違う。
   関連出力 (0,4) と同じ実 child を保ち、双方の full journal models は非空。
   任意の共通 raw 子孫が持ち得る完全モデルは空だが、任意の公開境界への
   モデル射影は同じ。空モデル子孫や最終診断の合流性までは否定していない。
   主要: `GeneralMixedCompoundSourceFork308.exact_fork`,
   `GeneralMixedCompoundPointFirstExact308.exact_second`,
   `GeneralMixedCompoundPointFirstInstall308.generated_child`,
   `GeneralMixedCompoundPointFirstPublic308.exact_projection`,
   `GeneralMixedCompoundInitialNonjoin308.no_inhabited_join`。

3. **公開射影を保存しても、有効な raw 操作が異なる。** 再観測先行で据え付けた直後は、
   同じ実 child の予約済み両端を等しくする novel raw feedback が有効。
   旧の `installed` は両端の意味型が違う同時割り当てを持つためこの feedback が無効。
   有効側で実 equate の `Step` を構成し、任意の完全モデルを順逆で保存し、
   同じ等式は直後にもう学習できないことも証明した。
   主要: `GeneralMixedCompoundPointFeedback308.public_projection_not_feedback`,
   `models_iff`, `not_repeat`。

## 真の observer / compiler と EvidenceNode

4. **実 child の pending→rejected。** 再観測先行側の実 install で child が生成される。
   既存の versioned 履歴 `.input plan` だけで両端と一つの親 aggregate を正当化し、
   raw の certified refresh を行う。未解決の子に依存する `.output effect` slice は使わない。
   その子に対する実 report は、未観測の pending から、型 head mismatch をもつ
   完了結果へ進む。C238 向けの fixed-snapshot resolver 自体が子に対して
   `pending`→`rejected` を返すことを示した。
   主要: `GeneralMixedCompoundPointViewTrust308.step`,
   `GeneralMixedCompoundPointChild308.report_exact`,
   `GeneralMixedCompoundPointTrace308.actual_emission_observation`,
   `resolver_waits`, `resolver_rejects`。

5. **親ローカル証明はあるが、再帰辞書はない。**
   先行側の refresh 到達点では checked source の親に実 current frame、(2,2) capture、
   一つの同じ実 child、関連出力 (0,4) の witness と局所 `Certificate` がある。
   V8 の独立な親局所選定・子の局所棄却を両方証明した。
   proof-level resolver の木は `selected parentKey [rejected]`、全体分類は rejected。
   任意の model・payload について根の再帰 Evidence は不可。局所 frame だけで
   生成 child の証拠を補えない。任意の有効な次の一手は、strict refresh または
   novel equate のどちらかと同値。親はすでに committed、子は frame がなく、
   再 install・enqueue・再観測・merge はどれも次にできない。ここからの
   全スケジュールの終了・残り最大手数は主張しない。
   主要: `GeneralMixedCompoundPointEvidence308.local_certificate`,
   `witnessed_request`, `no_recursive_root`,
   `GeneralMixedCompoundPointOutcome308.tree`, `result`,
   `GeneralMixedCompoundPointSteps308.exact_operations`。

6. **現在 readback と公開意味だけに依存する compiler への反例。**
   C307 停止点と C308 先行側 refresh 到達点は、公開割り当てへの射影が任意の
   境界について同じで、現在の親 readback もスロット座標を source ID に
   正規化すると一致する。それでも前者には実モデル上の親局所証明が一つも
   なく、後者には存在する。この二状態を同じコードに写す表現からは、親局所
   証明の有無を正しく復元できない。一般の compiler が不可能という意味ではない。
   主要: `GeneralMixedCompoundCompilerGap308.equal_readback_separates_local_cert`,
   `no_factorization`。

## 範囲と次の候補

一般 source の observer/compiler 完全性、全 B4、一般の据え付け前後の停止・順序独立、
子も選択される一般 EvidenceNode は未解決。Rust/Yulang2 は今回は実行していない。
先行側 refresh 以降の証明対象は
(1) 任意 cert の新規 Known を支持 ID へ射影して残手数を計算、
(2) 保持された input/class slice まで区別する compiler 契約、
(3) 実生成子が選択される別 source で同一モデル・順序付きの再帰 Evidence 正例。
設計のまとめは [observer contract](../design/2026-11-21-cycle308-compound-observer-contract.md)。
意味論の変更を要求する質問はなし。
C306 の `GeneralMixedFullControlPresentation306.present` は、対象と到達閉包が
明記された既存テンプレート。C238 に当てる前に、先行側の任意 refresh/equate
後で `Known` と `RawEqual` の有限支持を保存する補題、および現 frame の
`Committed` が保存される補題を作るのが次の最小単位。C306 のコードをそのまま
C238 完全表と扱わない。

## 公開と検証

途中のピン: `a685e0310e95fb42715fac971fcbcb0f4c2aedac`（早期ダイヤモンド）、
`6f754f4a4f5695ebda96afa2143cfcef5401d0ce`（開始分岐・モデル分離）、
`9b203d47b6e041ce21ceae9aa5c81d6053ee16cd`（feedback・実 child の観測）、
`12ff12a0b26cc79254d2b10345e7ab826ed7c869`（局所証明・実 resolver・反例）。

- `cd lean && lake build --wfail <31 C308 modules>` 終了 0（2856 jobs、対象と依存関係）。
  31 modules すべてを `lake env lean --trust=0 -DwarningAsError=true Yulang/<file>.lean`
  でもソースから検証、全 31 件終了 0。
- 独立 11 監査 `lake env lean --trust=0 -DwarningAsError=true Audit/Cycle308*.lean`
  （各ファイル個別）も全件終了 0。324 件の出力記録、異なる公開名 290、
  axioms なし 3、残りは `propext` / `Classical.choice` / `Quot.sound` の範囲のみ。
  [監査ステータス](../verification/cycle308/standalone-status.txt) と
  [出力 00](../verification/cycle308/audit-00.txt)・[01](../verification/cycle308/audit-01.txt)・
  [02](../verification/cycle308/audit-02.txt)。
- `bash tools/verify-lean.sh "$PWD" 89edc6c8f --no-build` は終了 0 / diff PASS。
  出力全文: [00](../verification/cycle308/diff-00.txt)・[01](../verification/cycle308/diff-01.txt)・
  [02](../verification/cycle308/diff-02.txt)・[03](../verification/cycle308/diff-03.txt)・
  [04](../verification/cycle308/diff-04.txt)・[05](../verification/cycle308/diff-05.txt)・
  [06](../verification/cycle308/diff-06.txt)。
  [対象 build](../verification/cycle308/focused-lake.txt)・
  [対象 source](../verification/cycle308/focused-source.txt)。
  常設の指示どおり無指定の全体 build・全 repo axiom gate は実行していない。
- 成果一式の固定 pin `128142cd80a5905c3695379a9ee02c647b660f12` で、
  C308 全 59 ファイルがローカル想定内容と一致。直前 C307 の barrel にこの周の
  31 import だけを加えた内容も一致。[連続公開の照合](../verification/cycle308/readback-substantive.txt)。
  完了公開で本報告と連続公開の照合記録の 2 件を加え、完了心拍を更新する。
