# C312: 実 alias の履歴から現在の候補・同一モデル辞書を組み立てる

開始 2026-11-21 03:30 UTC / 12:30 JST。前回 C311 の完了
`b39f83745fd539d96f67480745fe454e31d76c4b` を確認。integration
`9e1ac23910ea8f3866c4d5714eb4479ec5ae3de4` の standing orders / inbox を
開き直し、I-55 (4)、次に条件付きの (2) の順。今周期は (4) に集中した。

## (4a) 別発生点・異なる read bounds でも旧選択が読める

- 任意の source-checked 実 mixed 到達路で、全登録 center の出所（初期点か実 install の
  ordered emission か）と、各保存 plan の実入力・同一 seed/constructor/interpretation
  を復元した。等しい数値 invocation の異版の center は任意の**同じ**妥当モデルで
  意味的に一致する。各実 merge で保存した二点の中心の意味的一致を経路に沿って保存し、
  alias の対称・推移閉包全体に広げた。
  `GeneralVersionedSiteOrigins312.reached`、
  `GeneralVersionedIdentityCenters312.same_identity`、
  `GeneralVersionedAliasCenters312.same_alias`。
- 実登録済みの旧 plan と、同じ宣言を検査する現 alias 発生点を任意に取る。
  任意の現妥当モデルで、旧 head の確かなテストと変数の指示値を現在の center に移した。
  現 capture の interval 適合、cross 制約、self-check、projection がそこで成立し、
  現 inspection の conflicts は空。現候補の Prepared/Frame を先に仮定せず、
  旧・現 bounds の文字上一致、過去と現在の発生点一致、ordinary replay の仮定も不要。
  `GeneralVersionedAliasReadback312.readback`、
  `GeneralVersionedAliasReport312.from_alias`。
- 集約式の既存 target は実履歴の equation entry から再利用し、未保護の target
  だけを補う。旧選択を現在の検査にかけると、実 Local selected から
  Prepared または Failed が既に分かる。後者の blocked/arity/Fresh/現在 bounds と、
  上記 conflicts 空・非集約のモデル、履歴集約の条件から現 Prepared を作り直せる。
  現候補の一意性から旧鍵の互換を得る。鍵の一致は前提ではない。
  `GeneralVersionedProtectedPeer312.complete_head`、
  `GeneralVersionedHistoricalTransport312.prepared`、
  `GeneralVersionedAliasChoice312.choice`。
- 集約の保護範囲には、現 raw 全体でなく「全 journal Models を支える名前」＋
  「候補レポートが実際に読んだ名前」を使ってよい。その場合、補った**同じ**
  assignment が journal Models と候補 HeadModels を同時に満たす。
  `GeneralVersionedSemanticPeer312.full_head_of_trace / choice`。
  実履歴の有限 ID 照合は `GeneralVersionedProtectedLookup312.verify_iff`、
  必要な ID の名ごとの正確な意味は `GeneralVersionedProtectedName312.on_trace`。
  一つの名前の版が違っても、別の名前の旧集約式の再利用は妨げない。
- 予約と実定義を区別した。registry 全体を予約する install は、選んでいない
  宣言の slot も予約可能だが、実 ledger entry の一致には同じ発生点・鍵が必要。
  また実 refresh の証明書に既存名の反射的な通常原子を付けても、実 Step の条件と
  全 Models は変わらない。対象が ledger にない場合 raw 全体の lookup が落ちる
  ことを条件付きで示した。これは選択の反例ではなく、raw support を一律に
  保護する検査の限界。`GeneralVersionedReservedOther312.reserved /`
  `absent_with_different_key`、`GeneralVersionedHarmlessRefresh312.step /`
  `same_full_models / raw_scan_blocked`。

## (4b) 出力と順序付き子を、一つの実割当てから作る

- source-checked かつ到達済みなら**同一の exact occurrence と同じ宣言 key**の
  現 Frame は同一 Plan に決まる。数値 invocation だけでの構文同一性ではない。
  そのため、実 selected の「出力衝突なし」から回収した head＋class の証人を、
  無関係な候補に移すことなく今の packet に使える。現 `HeadEquations` の
  存在は、この回収の条件として明示した。
  `GeneralVersionedCurrentFrame312.frame_exact`、
  `GeneralVersionedSelectedJointHead312.effects_for_frame`。
- 既存 journal・現 head・現 class・実際の右辺読み出しを保護し、保護外 target のみ
  を更新する有限書込み表を作る。重複 target は型の構文同一でなく相互 subtype で
  合えばよい。保護済み target の式が元モデルで成立し、同 target の RHS が一致する
  ことは、その元モデルを保護したまま全出力・全順序付き子の式を得るための必要十分条件。
  この表は一つの元モデルから評価し、別々の存在証人を合成しない。
  `GeneralFiniteTypedWrites312.exact`、
  `GeneralVersionedJointWrites312.complete`、
  `GeneralVersionedJointWriteExact312.exact`。
- 根自身の明示出力の予定行は実 live class の式に含まれ、根の target は保護される。
  よって未解決の検査は内部 where/子の行だけに絞られる。
  同じ宣言の alias 履歴があれば head の初期証人も得られる。点 capture の binder は
  現観測値で既に一致し、異なる保護外 private binder は衝突しない。
  保護中の private binder は実 owner を照合すれば同じモデルで再利用できる。
  `GeneralVersionedRootWrites312.outer_live / lift_table`、
  `GeneralVersionedBinderTargets312.point_agrees`、
  `GeneralVersionedBinderReuse312.head_table`、
  `GeneralVersionedHistoricalJoint312.head_from_history / joint`。
- リテラル入力変数の転送と、出力専用 binder をそのまま子に渡す where は
  何個あっても内部書込みが恒等式なので、内部書込みチェックが不要。
  実 alias 履歴・保護集約・必要時の private owner を確かめれば、任意の
  そのような非葉候補は joint / Installable を得る。実 selected、Stable と
  同じモデルの順序付き子証拠が与えられると、親証拠と生成辺を返す。
  複合式の入力や計算された named output には、この恒等式の主張を延長しない。
  `GeneralVersionedForwardedWrites312.internal`、
  `GeneralVersionedForwardedJoint312.evidence_node`。
- これらを条件付き一般 `EvidenceNode` につないだ。与えられた辞書木に関する
  再帰であって、飽和が停止するという証明ではない。現候補の書込み表検査と
  履歴集約のカバーが一般に供給されることは別の義務。
  `GeneralVersionedRecursiveReducers312.evidenceNode`。

## I-55 の残り（未証明インターフェースの本数）

- **(4) 2 本。**
  1. **(4a) 保護集約の履歴カバー。** 実 alias/refresh から現観測の非集約項を
     全て得られた。残りは、現候補が読む名前と意味的 journal support の両方で、
     保護が必要になった各集約 target に対する実 owner・宣言鍵・その名前の
     観測版の照合（または同じ固定値を意味的に既に満たす別証明）。
  2. **(4b) 同一モデル用の有限表の証明書。** 型付き表を解いて実候補・順序付き子・
     class/output 全体をまとめる部分はできた。一般の no-history の初期 head、
     保護集約/保護 private binder の由来、内部 where/子の保護済み式と
     保護外の同一 target の整合を、任意の非 replay 選択で供給する部分が残る。
     リテラル転送の内部行は解消済み。
     `TargetChecks` は十分条件であり、出発モデルが違うときも同じ表が通るとの主張ではない。
- **(2) 2 本。** (2a) 履歴付き実 Local 行を生成する一般 observer/compiler。
  (2b) 実 Sat が成功して返ったとき、実 Step 経路とその地点での停止証拠を取り、
  実行が返した木をその Local/Classify と照合する橋。
  今周期は (4) を優先し、(2) の一般橋は追加していない。

上記は最終定理の未証明入力群の本数で、補題数の予測ではない。
言語仕様と受理条件は変更していない。Rust と CI は未実行。停止性は対象外。
質問ノートなし。使用枠の残量は不明。
[選択の設計](../design/2026-11-21-cycle312-protected-peer-choice.md) /
[現 Frame と書込み表の設計](../design/2026-11-21-cycle312-current-frame-and-writes.md)。

## 次の証明対象

1. `GeneralVersionedSemanticPeer312.Sufficient` の producer。
   `GeneralNominalVersionedTraceSupport237.source` の実支持に対して、候補 report
   に現れた aggregate 名がどの実 producer/owner/version から来たかを追う。
   予約されたというだけの名前と、式を実際に支える名前を混ぜない。支持の粗さで
   検査が落ちただけなら言語の反例にしない。
2. `GeneralVersionedRecursiveReducers312.TargetChecks` の producer。
   根の明示出力とリテラル転送は既に済んだ。複合 where の新規 target、
   alias で継承した固定済み target、履歴のない初期 head を分けて追う。
   固定値が不足する場合は、新たに選んだ別の witness で埋めず、実到達の
   同じモデルで保護されるかを確かめる。
3. 上記から独立に (2) を進めるときは、返却した実 Sat のトレースに限定する。
   新旧の raw 停止性や有限性はこの目的の前提に戻さない。

## 検証

最終照合でも integration と二文書の blob は開始時と同一。
Lean 4.35.0 で追加 29 モジュールの focused build、各 source の trust=0、
10 件の個別監査、差分ゲートが PASS。明示的な public 宣言 169 個を含む
215 件の公理確認（重点再掲を含む）で非標準公理なし。全体 build は未実行。
以前の C311 実経路を追加の独立 probe に通し、親・中継が転送断片を満たすことと、
merge 後の実 peer の現 raw report に一般 alias 読出しが適用できることも確認。
完成版の変更は 61 ファイル（心拍を除く）。所要時間は完了心拍に記録。
[コマンド・結果](../verification/cycle312/verification.md) / [公理](../verification/cycle312/axioms-00.txt) / [差分ゲート全出力の先頭](../verification/cycle312/diff-00.txt)。
