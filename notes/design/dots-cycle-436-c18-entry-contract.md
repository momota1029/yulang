# C436 / I-79: 分類・辞書・報告の同一索引チェックリスト

対象: `integration/m1-final@a6c7ed28…`。以下の定理名は設計のもの、未コンパイル。C18 の一行だけ。完了の検査は論理的な同一 State 内の有限な選択から導き、execution time や declaration/order 推測ではない。

## import seam の実際の source edges

`FixedGoal402 (8ebefffe…)` → `MixedQualification401 (d398c545…)` → `CertifiedWhereInputs401 (c2b8a212…)` → `PreparedMixedWhere401 (681f2433…)` → `SingleStoredFrame401 (466c0ed2…)` → `B6MixedLexical401 (7db6d0b9…)`。全矢印は同一 integration pin の各ファイル先頭の実 import。新 `CompletedLowerPayload436` は最後の語彙だけへ向かう。新 high module は `CompletedLowerPayload436` と既存 `FixedGoal402` / C406 / R17 を import できるが、旧ファイルまたは low payload がそこへ向かう矢印を足さない。

## 3 引数の検査と同じ外形

- `Classifies R18 s q r = I72.Classifies R17 s q r ∨ (∃ leaf : Leaf s q, Summarizes leaf.tree r)`。ただの「既存の受理＋同じ報告」という循環ではない。新 `Leaf` は consumer の実 head test args, visible declaration, original ordinal, rawSafe, upper/source provenance, exact retained row と actual typed receipt、同じ scoped finite producer の実 derivation、postselection の actual capture、元の where/output が空、を要求する。どのモデルも checker result も前提にしない。
- `DictionaryEvidence.previous` は旧 `I72.DictionaryEvidence` を同じ s/m/q/d に挿入。`DictionaryEvidence.completed` は同じ leaf, exact lower receipt value, `CompletedInvocationMeaning406 leaf.event m`（同じ capture/interval、typed comparison/body/fixed targets）および同じ producer の旧辞書証拠。C406 の `ScopedEvidence406` を代わりの任意の値として挿入しない。producer proof は derived dependency、それ自体を新しい dictionary child として追加しない。
- `dictionary_sound_R18 : ∀ s q d, Classifies R18 s q (.selected d) → ∀ m, Fits s m → DictionaryEvidence s m q d`。旧枝は `PendingAssociated434.dictionary_sound_R17`。新枝は `CommonRoleOutermostResolver.classification_exact` (blob `b05658f0…`) を同じ leaf.tree の `Summarizes` に二度適用し、`Result.selected.inj` で requested d と leaf.dict を literal に一致させる。producer と consumer の全ての意味はこの**同じ** m と `Fits s m` から作る。特に producer の rhs value を使うため `fixed_value_code_same_model403` と exact `getElem?` の保持行を同じ receipt に掛ける。
- `Witness.previous (w : PendingAssociated434.Witness)`、`completedNative (data : Wire)`、必要なら `unsupported`。旧枝の関数はどんな r/w でも branch equation が `rfl`。`verified_R17_result_classifies_in_same_State434` から旧報告の actual classification も別に取り出せる。`Wire` には proof、辞書、完了フラグ、任意に typed RHS を挿せない。
- `check` 新枝は `Option ReadBack` が成功したときだけ `Check408.matchesNoWrites r leaf.tree (.selected leaf.dict)`。readback が作った**同じ** leaf を `ClassifiedAs` と `ReportEvidence` に使い、`matchesNoWrites_exact408` が `r = leaf.report` を与える。供給された report を leaf のデータとして使わない。 `check_sound` は旧 C434 (blob `56c210d9…`) と同じ P/r/w/Bool/∀ m の外形。extended `ClassifiedAs` と `ReportEvidence` は旧枝を丸ごと残す。
- 全 raw root K2 に対し、`Classifies R18 … .rejected` は旧 inclusion で存在し、`Classifies R18 … (.selected d)` は旧根優先 lemma または leaf.rawSafe に矛盾。新 witness は checked readback が rawSafe を持つため raw 根で true になれない。C17 pending の Bool は `previous` として変えない。pending/undefined を拒否に読み替えない。

## 最初の公開前に通す 4 つの短い lemma

1. `retained_literal_typed_output_means_same_lower436`: 低い payload の raw row locator と同じ B6 typed code を、そのモデルの exact `actualEquation` と `Equivalent (m.assignment L).1 v` へ。 `nativeSyntax L` を使わない。nativeSyntax と普通値の間に State が持たない関係は導かない。`Bounds` が必要なら raw atom から元の argument (L,C,U) や captured payload (P,M,Y) に別に証明し、どちらの区間かを区別する。
2. `no_legacy_selected_for_completed_leaf436`: actual no authored L の下で C407 の全 named theorem。さらに旧 endpoint は `OriginalProjectedLeaf426.onlyOutput` (blob `74112b1e…`) が同じ q の length=1 を要求し、新 leaf の q.outputs=[] と矛盾（C435 の一般 record/head inversion よりこの試験片では強く簡潔）。旧 `check` も `verified_R17_result_classifies_in_same_State434` から exact selected report に true とならない。
3. `no_inherited_local_other436`: 別紙の old rule inventory、実 args 1、実 singleton unary variable child、要求/where が空。raw `RootCycle` はこの補題の前提にしない。古い選択や診断を意図的に選べないよう先に旧 checker を実行して結果を negative guard にしない。
4. `check_previous_eq436` は全入力に `rfl`。`check_sound` は旧枝と新枝のみの実 classification/evidence を組む。C18 の closure は実 data-only reader が true/false 独立試験を通ったのち。全 production を確認してから `lean/Yulang.lean` 末尾にのみ import 追加、I‑78 の frozen IDs 不変、新 Audit は Yulang modules only の空 cwd、4.35.0 `--trust=0 -DwarningAsError=true`。NoFalseRejection、Rust、solver の一般停止は対象外。
