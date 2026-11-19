# dots-main cycle 282: 全 journal と証拠を保ったまま、現用の集約を固定ポートへ移す

- 定刻 2026-11-19 21:30:00 UTC、実際の開始 21:35:10 UTC。終了 2026-11-19T22:25:11Z（50.02 分）。最初と途中に `integration/m1-final` の standing orders・inbox を取得。pin は `707497ab`、指示は ACTIVE で変更なし。I-51〜53 と凍結範囲を保持。cycle 281 の完了 `80c7a8c3` を照合し、作業者は一人、書き込みは private `work/dots-main` のみ。
- 中間の検証済み tree: 20 分 `8926d0de`、30 分 `942071eb`、40 分 `c8bb00dc`。全 tree を取得し直しローカルの検証済み tree と一致を確認。

## 1. fixed ポートから履歴全体を切り離した

任意の実 source 到達状態で、seed・owner・宣言・binder・上下から決まる固定ポート（purpose 0/1、版 0）は、**全 mixed journal の意味が読む識別子**に含まれない。current raw だけの主張ではない。元の source、raw/centered site、過去の plan、保存した effect snapshot、その歴史時点と現在の live class をすべてたどった。子 demand、出力 target、actual center、explicit body と role-default の positional center も区別して扱った。過去の effect は実際の以前の到達状態から保存されたものと示し、比較する seed が同じことを追跡した。

これにより任意の二割当が固定ポートの外で一致すれば、全 `Models` と任意の recursive `Evidence` の payload は同値。親だけでなく同じモデルで全子を読む。これは特定の成功モデルを選び直して成立させる補題ではなく、実到達状態での読み出しの分離。

履歴の versioned 集約は実 plan 台帳から取得した。同じ key の定義が同じであること、式中の versioned 依存が ID を真に下げることから、実行可能な dedup/topological sort が必ず成功し、履歴の全定義を保持する。得た substitution を raw current・source・全 packets/effects の compiler と全 Evidence ノードに共通で渡す。新しい compiled model はその decoder で旧全 journal のモデルになり、旧モデルは履歴の定義式をすでに満たすため相互部分型で復元される。古い versioned 型の参照は展開後の typed support には残らない。row は全ての ID で変更しない。

## 2. 全 owner の最新の表、共通アドレス上界、実回帰

各 owner について最新の plan を一つだけ選び、その固定集約表の RHS を上の履歴写像で展開する。別 owner の書き先は衝突せず、同じ owner の重複行は同一の定義。全 owner 分を一つの割当に同時に実現した。任意の source 到達状態と payload について、**初期 seed 以下の有限な型座標 + 全 row** 上で「旧全 journal と Evidence」と「compiled journal と同じ Evidence、最新固定表」の存在射影が厳密に一致する。これは source を最初に固定した全有限経路に同じインターフェースを使う定理。

同じ初期 source の全到達状態に対し、Paterson の実 owner 候補と checked registry の inputNames から作った一つの有限リストで全 live target を覆う。重複なしの canonical table のセル数もそのリスト長以下。ただし RHS の展開サイズや全履歴の保持量、全到達族に共通する有限な意味命題リストまでは有界としていない。

- **旧239・240:** 任意の completed round n+1 で、全履歴の lower chain は旧 source 2 と相互部分型。240 の upper は source 4 を読む。従って最新表は全 n で、239 は `(2,2)`、240 は `(2,4)` を読む二つの固定セルへ縮約可能。旧 journal 全体・leaf payload・全 row を一つの witness で保ち、公開結果は元 source の Models と `.node 0 []` にちょうど一致する。
- **I-45 optional:** 関連出力を未確定のまま受け取らない。最終 compiled journal + fixed 表 + leaf は既存の正しい関連出力条件と payload に一致。実 point の旧 live 下端は source 4、二回目 install 後の新 live 下端は同じ固定ポートで source 2 を読む。両値が異なるため、定義を上書きせず両方の表を足す設計は、実公開条件で不可能だと閉じた定理で確認した。履歴の旧 versioned 定義は消さず、別に展開する。
- **206、218、Display:** actual 206 は既定 associated output の `.node 37 []` を同じ witness で保持。218 は selected-node の `EvidenceAt` を保持し、旧 child の rejection を成功扱いしていない。Display は実の非葉 `.node 1 [.node 3 []]` 全体を保持。

## 3. 到達後を仮定せずに compiled 据え付け候補を検査

まだ共通モデルが分からない候補について snapshot が一致するだけで、仮の install 後の全 journal を読み出しコンパイルできる。seed 台帳と legacy-empty は Common を仮定せず追跡。**仮の compiled journal がモデルを持つ ⇔ 旧 `InstallationModels` の共通モデルが存在**を両方向に示した。その後で、その他の既存 guard と Generated・未据付条件を満たす候補について、最新固定表を同時に実現しても iff と示した。安全性、trusted cache、materialization、choice、cycle、alternatives は既存 predicate のままであり、子の証拠を据え付けの新前提にしていない。

この guard を使う raw-indexed driver を定義した。任意の実到達点から、非 install は元の規則のまま、install は compiled guard 経由で、実一歩と有限 path が双方向に一致する。従って無制限 driver では旧239・240の非停止性も残る。一方、cycle 281 の chart/phase を別に課した driver では `Acc` を保存し、optional の三歩、239/240 の最初の round を残し、以後の反復 install を除く。完全運転を有限型に圧縮したという主張ではない。

`Equal` が問うモデル上の型の等しさを compiled term 上の同値な条件へ移せること、`SameInputs` の意味条件も compiled 模型の decode と iff を確認した。さらに root/generation・選択・安定性を同条件に保った `EvidenceAt` は、任意の到達状態で旧義務と同値。これは旧義務が全到達状態で成立する定理ではない。

## 主な Lean 宣言

| 宣言 | 適用範囲 |
| --- | --- |
| `GeneralRebasePrivateJournal282.journal_private`, `models_iff` / `GeneralRebasePrivateEvidence282.evidence_iff` | 任意の実到達状態で全 journal 支持から固定ポートを排除。その外で一致する任意の二割当で、全モデルと任意の evidence payload が iff。 |
| `GeneralRebaseHistoryOrder282.ordered`, `member_exact`, `preserves_joint` | 任意の台帳の rank により sort 成功、実到達なら内容保存、任意の旧全モデル＋証拠を同じ normalization に運ぶ。 |
| `GeneralRebaseWholeJournal282.exact_view`, `compiled_history_closed` / `GeneralRebaseWholeRow282.source_interface` | 全 compiler と証拠の正確な decode。歴史型の読出しを消し、固定初期型座標・全 row 上で全 owner の表との共同射影が iff。 |
| `GeneralRebaseLiveStore282.live_unique`, `projection` / `GeneralRebaseFixedBasis282.common_cardinality` | 任意の source 到達状態で最新表の全書き込みを共同で実現。初期 source ごとに全到達状態の重複なし live 表セル数を一様に抑える。 |
| `GeneralRebaseLoopView282.Version.projected_constant`, `Loose.projected_constant` | 両実族の任意 completed round で、二セルの定数表と初期 source 条件・leaf の正確な往復。 |
| `GeneralRebaseOptionalView282.compiled_terminal` / `GeneralRebaseOptionalOverwrite282.stale_append_fails` | 実終端の公開出力と leaf を維持。出力が正しい任意の割当に、point/終端の両 live 表は足せない。 |
| `GeneralRebaseProspective282.acceptance_before`, `GeneralRebaseCompiledInstall282.same_install` | 任意の到達前状態と snapshot 一致だけで仮 install の共通モデル iff。残りの既存 guard、Generated・未据付があれば最新固定表込みでも同じ。 |
| `GeneralRebaseCompiledStep282.driver_path`, `guarded_accessible` / `GeneralRebaseCompiledRegressions282.Version.driver_not_acc`, `Loose.driver_not_acc` | 到達点から全有限実経路の iff。無制限旧反例は残り、chart/phase を課す関係だけが終わる。 |
| `GeneralRebaseCompiledQuery282.equality`, `same_inputs` / `GeneralRebaseCompiledEvidenceAt282.equivalent_at` | 任意の実到達状態で、compiled 上のモデル比較と選択済みノードの再帰証拠義務を旧規則に正確に読み戻す。 |

## 残り・照合・検証

- 今回の driver は immutable raw snapshot を指標に残す。全対象の実行可能な独立 successor、すべての到達源で共通の有限 RHS 命題集合、live/evidence phase の一般的完全性、全言語の EvidenceNode は未証明。次に (1) 版付き履歴を消した lookup で SafeKnown、Generated/Local と class requests を exact に再現する、(2) RHS の source/owner 共通支持閉包を分離して証明する（予約 metadata をそのまま公開名にしない）、(3) 必要な private phase を落とさない guarded completeness を実 proof から出す。
- Yulang2: 監査 branch `55574b60` の `x-oracle.md` X1（名目 wrapper + 裸変数 where）、X2（構造増大をそのまま前提にする場合の差）、X3/X5（構造観測の限界）を確認。同じ pin の y2-claims-record-role-cycle-3.md C3-ROLE-01/02 も参照し、子 where の受理・拒否を区別した。実機で既に記録された例との照合で、今回新しい parser・型規則は定義せず、同じ旧 Lean 意味を表現し直した。ローカル Yulang2 バイナリ確認なし、新しい実機試験なし、意味の選択を要する質問ノートなし。利用枠不明。
- 32 新規原本、6 独立監査（259 宣言、標準公理のみ）、barrel の一回ずつの import、7 型付き使用例と 8 行の実行 probe を確認。probe では実 packet データから各 owner の最新が一つ、両族の dedup+sort 後の履歴が4行、固定表の RHS 参照が `[2,2]` と `[2,4]`。補足で既存206・218・230・233の6監査を個別に再検査。
- scoped `lake env lean --trust=0 -M 3200 -DwarningAsError=true -R .`。統合 pin と cycle 281 の両基準に対し `verify-lean.sh --no-build`、diff、I-51/53、凍結ファイル・禁止構文を確認。全 Lake build、全統合検証、CI は実行しなかった。
- [実行コマンド](../verification/cycle282/commands.txt) / [全新規監査](../verification/cycle282/independent-recheck.txt) / [監査対象一覧](../verification/cycle282/audited-declarations.txt) / [旧監査](../verification/cycle282/legacy-check.txt) / [統合基準の出力全文](../verification/cycle282/integration-diff-full.txt) / [前周期基準の出力全文](../verification/cycle282/prior-diff-full.txt)。
- 公開対象は 71 パス。最終更新は expected-head、非 force。取得し直した全 tree、完了心拍と本報告を照合する。
