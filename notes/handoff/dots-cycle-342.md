# Yulang dot 第342周: 古い where 下端を引き継がず、実際の現行子を同一モデルで読む

- 範囲: `work/dots-main` の Lean 側。C341 完了 `ada2a1282181c1a78f73d9a1bfadfbb575146f8b` を起点とし、`integration/m1-final` の `3bf96b5e51be8312b28a13c47c6d5cadc243be05` で立案順序・inbox・仕様を再読した。I-62 に従い比較対象は実 solver と最新の証人つき分類。旧 `Local` 対応は**方針により対象外**で、証明したという意味ではない。
- 証明の固定コミット: `73fb5b55f80eb6a9c2e17314a6f49320bd7312fe`。以下の C317–319 は旧実行器と別の、既存の隔離された版つき where の試作である。

## 確かめたこと

1. **元の C316 をそのまま比べた。** `VersionedOriginalCut342.original_cut`: 任意の実 C316 最終モデルに対して、旧 raw 状態には `Produces` がない。一方同じフィクスチャの隔離 C317 は実 `InstallStep` と受理済み辞書を持つ。旧状態の全 source 名で一致するモデルが存在し、稼働後の `Frame`、版つき `Holds`、再帰 `Evidence` がそろう。`reported_targets` は文字通り `[4, lower, upper]`。別の二捕捉 C319 で元 C316 をすり替えてはいない。
2. **観測を保つ後段への移送。** `VersionedRetarget342.same/head/holds`: 元 plan の検査済み観測を保つ具体的な状態精密化、同じ解釈、旧版つき `Holds`、新状態のモデルがあれば、同じ割当で現行 head と版つき `Holds` を再構成する。一般の古い plan や term だけではない。`VersionedRows342.exact/aligned/fixed/all` は変数の評価モード（nominal 内部は actual）を保ち、行列の順・左辺の論理名・その宣言的意味をそのまま保持する。
3. **C319 の現行 raw 親と子。** `VersionedPhysical342.old_not_current`、`VersionedCurrent342.after_frame`、`VersionedTree342.modern_raw_tree`: 旧子と現行子が実に記録されており ID は同じだが occurrence は違う。現行親は事前ではなく実取引後の context（物理 slot 7→8）で `Prepared/Frame` と class effects を持ち、実出力の証人を出す。コンパイラが選んだ子は現行子だけで、実状態に Generated。ここでの再帰木は現行版つき親と raw 子証明をつなぐ wrapper であり、旧形式の親 packet を通したのではない。
4. **現行の target・値・由来。** `VersionedReceipt342.current_order/current_literals` は所有者の出力 target 4、新 lower、再利用 upper の順に実生成行を読む。`center_receipt` は別の、本当にコンパイルされた child center schema の行。旧 upper の式は同じで、旧 lower の式はモデル同値ですらない。`VersionedSeparation342.mode_changes` の旧捕捉は `(4,2)` で意味的に非点、現行親の捕捉は `(2,2)`。現行子の両端はアドレスが違うが意味はこの例では同じ。`VersionedStale342.no_substitute`: 任意の版つき最終モデルが普通の view にも適合するなら、ID・実 center・再利用 upper が同じでも、旧子を現行子の論理需要に alias で一致させられない。
5. **最新分類と同じ割当。** `VersionedChildView342.in_every_model/not_authored` は実 lower/center/upper を現行親の完了した出力として読み、parser source にはしない。`VersionedChildBody342.current_models` は任意の本当の版つき最終モデルから、旧版も含む全 journal footprint を保つ拡張を作る。`VersionedEndpointOnly342.no_center_observation` はこの現行子の対応する head を center の行なしでも得る（この例の head であり一般の分類ではない）。`VersionedPaired342.same_assignment` ではこの拡張上で、現行親を含む版つき再帰木、現行子の正確な配置と最新 `TaggedDictionary340` 分類、その子の辞書 `Evidence` と固定の出力行を同時に得る。ルート全体について最新分類が返ったとは主張しない。
6. **親の残差を絞った。** `VersionedRootRead342.raw_root` は任意の版つき最終モデルで物理 descriptor を普通の `Foo(2,2)` 行として読める。`VersionedRootGuard342.ready_iff` はこの実ルートの一行 view で readiness と独立した支持が同値と示す。行が真だから支持あり、とはしない。独立した支持を与えると `VersionedRootShape342.root_election/exact_inputs/current_bindings` が既存の選出規則・順序・実 packet の二捕捉との一致を与える。`VersionedRootCompiler342.source_compile` は任意の keep/fallback/targets で既存の通常 source compiler が実需要について子を一つ出し、親の固定出力は厳密に target 4 の行と示す。物理現行子と、通常 compiler 側の fresh compound 名・由来・順序レシートを結ぶ一般証明は残る。

## 残り

- **(4) 1 群**。I-61 追補の任意の支持つき nested/compound source、残差（open/closed）や真の異なる端点から、既存 witness-backed の捕捉・正確な順序出力を作る一般 producer。今回のタグつき現行子・確かめた名目 point root で全体を閉じたとはしない。I-58 は実の center の等式、I-59 は既存 K2 の境界を変更していない。
- **(2) 2 群**。① 実際に成功停止した raw solver 出力一般について、現行位置・出力 target・順序・由来を保持して最新の宣言証人へ結ぶ。隔離試作の C319 では真の出力から現行子までつながった。次は `VersionedRootGuard342.ready_iff` の支持を実 root source/action から出し、`VersionedRootCompiler342.source_compile` の通常 compound 子と `VersionedReceipt342.center_receipt/current_order` の物理 current 子への位置・出力の対応を証明する。② 成功停止結果の診断と辞書全体の射影。木を持つことと、現在の実 solver の返却とを同一視しない。停止性・Rust 実行・全 Lean build は扱わなかった。
- 未決の意味論を追加していない。質問ノートなし。使用量の残枠は不明。

## 検証

- 公式 Lean 4.35.0。環境再起動後、C341 を Git の固定コミットから復元して、焦点を絞った `LEAN_NUM_THREADS=1 lake build --wfail` を再実行した。初回 cold の回復は上限で区切り、キャッシュを引き継いで通した。全体ビルドを実行したとは言わない。
- 証明固定コミットを別の detached worktree に取得。全変更パスの blob ID、旧 barrel 全 320991 byte と新規 import だけの一致、`git diff --check`、I-57 の二ファイルの Git blob ID の一致（内容を展開せず）、凍結ファイルを読まない別版 `tools/verify-lean.sh --no-build`、新規 source と独立 Audit の `lean --trust=0 -DwarningAsError=true`。Lean source 18、独立 Audit 7、名前付き公理照合 51、scoped axiom gate 102423 宣言、すべて PASS。標準許可は propext、Classical.choice、Quot.sound のみ。
- 本文の各 `Versioned…342` は `lean/Yulang/GeneralDeclarative…`、独立監査は `lean/Audit/Cycle342*.lean`。`notes/verification/cycle342/` に標準公理の結果、差分検査全文、exact source/audit の実行結果を保存した。
- 主要 checkpoint: `bf2371dd37c036cd3bf872a0e97564faee036e47` (精密化)、`0ac791a98c18f9bfab85d59745d8f8a2fca8a2a2` (全行)、`de43e8f8844f268c2ded015cce8d75fa1afd9e6c` (C316/C317)、`82965fe47901ade90d9cbcc5fdab386a0cf199fd` (現行物理の証拠)、`090e9d1f2e3a4a0ca9cba4366d10a0e701050224` (同じ割当)、`d749c96c2d444d2968bd03c0e7cfada53fed0ec8` (過去端点の非代替)。
- 所要: 09:30:08 UTC 開始、10:20:08 UTC に報告の更新を開始。証明検証時点は 35 変更パス、最終報告・検証ログ追加後の見込みは全 41 パス。公開後に exact readback を実行する。

### 新規定理名
- `GeneralDeclarativeVersionedChildBody342`: tie_literal,compiled,edges,grown,not_original,level2,levelLo,levelHi,level_source,old_sources,lo_level,mid_level,hi_level,level_bound,ranked,current_models
- `GeneralDeclarativeVersionedChildView342`: in_every_model,supported,not_authored,actual_arguments,range
- `GeneralDeclarativeVersionedChildWitness342`: ordinary_read,heads,active_supported,choice,selected,declared,coverage,actual
- `GeneralDeclarativeVersionedCurrent342`: root_reserved,located,current_prepared,after_frame,current_parent
- `GeneralDeclarativeVersionedEndpointOnly342`: belongs,mid_low_key,not_center,no_center_row,no_center_source,endpoints,no_center_observation,preserve_current
- `GeneralDeclarativeVersionedOriginalCut342`: reported_targets,original_cut
- `GeneralDeclarativeVersionedPaired342`: same_assignment
- `GeneralDeclarativeVersionedPhysical342`: observed,transported,recorded_version,holds_now,actual_children,unchanged_targets,new_registered,old_registered,same_id_not_occurrence,old_not_current,actual_model_packet
- `GeneralDeclarativeVersionedReceipt342`: lower_exact,upper_exact,actual_exact,current_order,center_receipt,reused_exact,current_literals
- `GeneralDeclarativeVersionedRetarget342`: same,head,holds
- `GeneralDeclarativeVersionedRootCompiler342`: declared,fixed_root,source_compile
- `GeneralDeclarativeVersionedRootGuard342`: original_arguments,original_targets,every_model,ready_iff,selected_needs_origin
- `GeneralDeclarativeVersionedRootRead342`: recorded,same_type_name,same_root_name,encoded,raw_root
- `GeneralDeclarativeVersionedRootShape342`: read_modes,exact_inputs,current_bindings,ranked,root_election
- `GeneralDeclarativeVersionedRows342`: variables_known,exact,all,aligned,fixed
- `GeneralDeclarativeVersionedSeparation342`: root_output,exact_width,archived,unequal_operands,not_current_lower,mode_changes
- `GeneralDeclarativeVersionedStale342`: old_center,historical_argument,actual_argument,old_arguments,active_history,no_substitute
- `GeneralDeclarativeVersionedTree342`: pre_not_after,raw_sites,identity_of_alias,old_id,new_id,root_requests,child_requests,actual_place,actual_root_outputs,modern_raw_tree
