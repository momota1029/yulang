# cycle 307: 出力要求と実 child を伴う source の raw 停止

開始 2026-11-20 22:33:16 UTC（11-21 07:33:16 JST）。実所要は同じ公開の完了心拍。
先行 C306 は `50a73cbeb72cfa7ae59a372cffa9cf8e5339d5f4` と完了心拍を確認。
開始時統合版 `b7fcac3da0a905a5a745fa6e4acc5717f007107c` の standing orders/inbox を再読し、
ACTIVE / I-54 優先順を適用。作業中に `9c4a7274b51d423fc900bc8a3af861c0b9b07119` に
進んだが、2本の指示は不変で、新規 C305 Lean 30ファイルは継続作業木と全バイト一致。
既存 Lean の変更は barrel 末尾への import 追加のみ。書き込み先は `work/dots-main` のみ。

## 結果と境界

1. **実 child の hidden actual center を独立に検証**。C238 の checked source は
   root で関連出力 `(0,4)` を要求し、一つの実 child を生成する。C239 の
   実到達状態では、すべての full journal model が child の actual center と
   upper port の型を同値にする。しかし raw snapshot の model には反例があり、
   center の名前は allocator の予約にも、base/ordinary の sources にもない。
   したがってその pair を raw equality-feedback に使えず、任意の certified
   refresh でも直接 `Known` にできない。関連出力と子は実在し、
   head が上端と一致することと、source 名の利用可能性とは別である。

2. **C239 tail の最小2状態、全 raw 後続**。C239 の子端点を出した状態からの
   **すべての** Mixed234 の一歩は、親の既に予約済みの versioned upper aggregate
   を新たに Known にする、証明書付きの refresh。逆にその証明書を満たす
   任意の context は実後続になる。どの後続も enqueue/equate/reobserve/install/
   merge/refresh のどれもできない。unused view catalogue により相異なる終点は
   無限にあるが、各実状態から行先を正確に持ち上げる最小 raw 商は
   `未観測 → 観測済み` の2状態。単なる正規形の1本の例ではない。

3. **棄却行は保存されるが、raw control は保存されない**。任意の C239 tail refresh
   で子の actual report は局所再計算して同じ1行の終わった head 不一致となり、
   V8 の局所判定は厳密に rejected のまま。全 journal model・出力要求も保つ。
   根の ordered capture/anchor report は source ID で比較すれば同じ。
   ただし旧 packet と現候補を一つの model で同時に実現できない。
   旧 output/child lower endpoint の保持が **履歴側**、現 report による二重 capture
   と同じ child の endpoint 生成が **現在側** の証拠で、同じ slice と扱わない。
   具体的な停止状態では根の選択済み全辞書も証拠も存在しない。EvidenceAt は
   生成 child の証拠が存在しないため前提が空であり、一般 EvidenceNode の証明ではない。

4. **純 equate の別定理**。任意の固定 anchor からの equate-only trace では支持名が
   保存され、現在の raw models は anchor の raw models と、有限支持上で現在
   entail される全等式のちょうど共通部分。等式コード同値と raw model 同値が
   一致し、同じ pair による任意の実 equate を両側で持ち上げる。equate を使い
   切った終点同士の raw model は同じ。一般 mixed kernel の有限性は主張しない。

5. **最初の再観測後は、任意の実運転で高々3手。1・2・3手すべて実現**。
   再観測済みの C238 point を始点とする任意の Mixed234 経路について証明した。
   次の水準では各厳密な一歩は child の下端・上端、親の upper aggregate の
   いずれかを新規に Known にする cert 付き refresh そのもの。逆向きも実規則。
   source ID 0/1 の二つの nominal に関する point descriptor を任意の slot
   埋め込みの下で保存して、reobserve は無効。根の再据え付けは旧履歴との
   共通モデルを持てず、子の候補は未配置・未観測・head 不一致のどれでも不可。
   支持名の等値類を full model で分離し、raw 採用済み等式以外は出ない。
   3ビットの個数が真に増え、`Acc` と各有限接頭辞から停止点に至る存在も証明。
   最初から一括、2群、1個ずつのどれでも同じ検証済み halt に着く。
   支持上の raw/full 等値には有限7タグの完全な決定表があり、管理上の child ID の
   タグは分離に使う証人の値であって、その型が固定だという意味ではない。
   point 後は根/子の実証拠が成立せず EvidenceAt は空の前提で成立する。
   point より前の全 install/reobserve スケジュールの定理ではない。

## 照合と範囲

I-54 の観測/棄却の完全性と停止性について、C238/C239 の固定 checked source を
前進。Rust/Yulang2 実機は未実行。このサイクルの追加は既存の Lean source・
C238 回帰・I44 の実操作と照合した。一般 source の有限表、任意の初期状態からの
install/reobserve スケジューリング、そして無条件な B4/EvidenceNode は未解決。
仕様判断を加えたり private actual center を新たに予約したりしていない。
利用量の上限は不明。追加の質問ノートは作らず、表現の差は design ノートに記録。

## 続きの候補

- `GeneralMixedCompoundPointSpine307` の、最初の再観測以前への拡張。古い loose
  context の選定と early refresh の順が変わっても、始点の exact kernel を保てるか。
- child が拒否される fixture とは別に、出力つき真正 child が通る checked source を
  作り、EvidenceNode の非空の再帰を閉じる。候補は C238 の root を保ち、
  既存の `variant 0 (.var 0)` を head に持つ leaf 宣言を別 key で追加すること。
  まず checked registry、旧 root の選択の保存、actual child frame の順で確認する。
  C299 の同一モデル再帰 reader は既にあるが、同じ associated-output 条件は未検証。
  新しい候補が通るとはまだ主張しない。
- arbitrary certificate が後で実行できる残りの reveal 群を各代表状態から作れるか。
  全到達グラフの一つの executable finite quotient は、この edge lift まで示してから。

## 主要な定理と検証

- 補助・モデル保護: `GeneralMixedCompoundChildHidden307.actual_center_gap`,
  `no_feedback_pair`, `no_refresh_into_support`; `GeneralMixedEqualityExact307.reconstruct`,
  `exact_code`, `exact_successor`, `canonical_terminal`。
- 観測の健全性・完全性: `GeneralMixedCompoundUpperRefresh307.step`/`models_iff`,
  `GeneralMixedCompoundAnyRoot307.same_read`/`no_packet`,
  `GeneralMixedCompoundAnyChild307.report_exact`/`failed`,
  `GeneralMixedCompoundTailChildOutcome307.unchanged`。後者は任意の cert と任意の
  frontier について、C239 前後の実 child の Local が同値。
- 実 tail の運転完全性: `GeneralMixedCompoundTail307.exact_anchor` は任意の候補
  後続を対象に refresh certificate + Known 条件との iff、
  `every_successor_halted` は許された任意の後続の全 Step を否定。
  `GeneralMixedCompoundTailFan307.infinitely_many_halts` と
  `GeneralMixedCompoundTailPresentation307.present`/`exact_tail_minimum` は
  それぞれ無限状態、厳密な有限表示と最小性。
- 実 point の停止性・完全性: `GeneralMixedCompoundPointEquality307.exact_pair`,
  `GeneralMixedCompoundPointExact307.decompose`/`exact_run`/`arbitrary_raw_bound`/
  `all_maximal_length_stop`/`exact_lengths_to_verified_halt`、
  `GeneralMixedCompoundPointAcc307.accessible`/`saturated_from`。
- 局所の辞書健全性境界: `GeneralMixedCompoundPointEvidence307.no_child_evidence`,
  `no_root_evidence`, `evidenceAt`。根の証拠否定は full model を仮定する。
  `GeneralMixedCompoundUpperOutcome307.no_selected_tree` は具体的な停止状態で
  root の再帰的 selected を否定する。主型性・全 source の辞書構成は対象外。

実行した検査:

- `cd lean && lake build --wfail Yulang.GeneralMixedCompoundPointAcc307 Yulang.GeneralMixedCompoundPointEvidence307 Yulang.GeneralMixedCompoundTailFan307 Yulang.GeneralMixedCompoundTailChildOutcome307`
  は exit 0（2823 jobs の対象依存グラフ、全体の barrel build ではない）。
- 主要4ソースをそれぞれ `lake env lean --trust=0 -DwarningAsError=true Yulang/<Module>.lean`
  で直接確認し、すべて exit 0。
- 監査10ファイルはすべて単独で `lake env lean --trust=0 -DwarningAsError=true Audit/Cycle307*.lean` の
  該当1ファイルを実行し exit 0。audit 同士の import なし。
  35新規 Lean モジュールの公開宣言340個を登録し、代表定理を再監査。
  許可集合 `propext`, `Classical.choice`, `Quot.sound` 以外なし。
  Smoke は有限 edge、実 1/2/3 手、4手不可と別 halt の検査。さらに
  `fastQuotient` の具体的な representatives、2つの射影、辺 [true]/[] を
  カーネル計算で検証（[入力・出力全文](../verification/cycle307/finite-code.txt)、公理なし）。
- `bash tools/verify-lean.sh "$PWD" 8204610a5 --no-build` は exit 0、diff-only PASS。
  `git diff --check`、各新規モジュールの barrel import、凍結ファイル不変更を確認。
  standing orders に従い、全体 build/全体監査は実行していない。
- 出力全文・終了コード: [検証ノート一覧](../verification/cycle307)。
  主成果は [固定チェックポイント](https://github.com/momota1029/yulang/commit/d74ea12ad197557ce7f32b1a51eabd06b20a47c7)
  で report 以外の47差分を全バイト照合（barrel は前の公開版に import を追記した内容）。
  この報告・検証ログは完了心拍と同じ non-force / expected-head 公開で照合。
