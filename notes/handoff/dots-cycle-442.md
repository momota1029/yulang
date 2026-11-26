この周に閉じた C の行: なし（C22 の元 RHS 再現と固定先の反例を検証。R22 は未実装）

# cycle 442 — 関連型 RHS の row 引数を平坦化しない

実開始 2026-11-26T13:30:55.980Z。I‑74 の C22 のみ、I‑78 append-only、I‑79 現行。C441 は開始時の正本 `integration/m1-final@fbbf227b2023e0da5d18d8f5c3826545f6b79e28`（Lean `f9471c73c28ed615317a4de8ff847af8b093e97d`）に exact 採用されていた。§6.1/6.3 の関連型本文・固定先等式と §4.6 の元の row/value 順序を組み合わせ、既存の直接複合例は未確認。使用量の枠は不明。

## できた範囲

- **実 source replay と型付き RHS**: where 無し、可視候補一つ、関連出力一個の `type out = ref 'e 'a` 実宣言。元入力の `ref` の宣言 scope/候補順/raw K2 を `replay442` で照合し、元の request／候補の unfilter した宣言番号／同じ lexical frame と body lookup／元の B6 atlas を保った Event を得る。input-only 投影を使うのは既存の入力 head/capture 読みだけで、出力を消した結果を元要求の分類として流用しない。fixture の B6 atlas は元の typed annotation input を表し、B6 全体の elaboration 完成を主張しない。
- `Replay.readOwnRefOutput` は実 plan の `ref` と順序付き row/value の cap を同じ head の元の両 binder から読む。`original_ref_encoded_output_nonflattened442`、`original_replayed_ref_equates_same_event_output442`、`exact_ref_output_uses_original_head_centers442`。元の occurrence・宣言/出力 ordinal・本文・要求先から出た reporting wire は row tag 11 と value tag 10、元の cap triple を別々に保持する。実 fixture でも exact 対照。既存 R21 の `.reference` は nonempty write を受理しないことも確認（言語の拒否とは別）。新しい判定分岐はない。
- **固定先の all-fit 境界**: `original_fixed_targets_can_fail_after_real_source_replay442`。元の一つの actual Event と同じ `I72.State` に対し二適合モデル。元入力の signed row `(56,[1,-2])`、元 B6 の評価、nativeSyntax、typed Seen、他の slot と全 `.2` が同一。fixed target 21 の type 内の row だけ signed / empty と異なり、後者で `FixedTargets` が偽。これは RHS が欠けるのではなく、元の固定先に**等式が保持されているとは言えない**という反例。
- 任意の元 typed tree の `fixedValueCode403` は row read footprint に触れれば none（`legacy_fixed_value_emission_iff_original_typed_footprint`）。さらに、全旧 value assignment が同じで元 row center だけを動かせる二適合モデルの間では `independently_varying_original_effect_excludes_any_old_denotation442` により、alias/composite を含む任意の単一旧 Expr を元の RHS の意味にはできない。別の変数が真正に混合値を持つなら旧 alias は同値を中継できるが、観測や別名だけではその意味を作れない。

## 独立保持の候補と限界

実在の別 carrier `GeneralNominalState.Descriptor/Denotes` は rowSource、value source と target assignment の同値を保持できる。`existing_mixed_descriptor_point_exact442` は exact point descriptor の意味を同じ assignment で述べ、位置・実保持・typed original RHS が一致するなら `actual_mixed_replay_with_existing_typed_companion_is_dictionary442` が元の `DictionaryEvidence.node` を返す。実 fixture の good model では実 descriptor + 旧辞書、bad model では元 `Fits` のみを物理 Audit で確認。別 companion の `Models` が現行の全 `Fits` から出る、とはしていない。別 writer/retention の provenance と完成／release は独立。

[fresh と制約済み target の実 QA](../design/dots-cycle-442-c22-fresh-versus-constrained.md): fresh target では他の全名と全 `.2` を変えずに target type だけを設定して旧モデルを拡張できる。一方、同じ fixed target 21 に既存の Int 制約がある actual State は元は適合し source replay も成功するが、どの適合モデルも mixed `FixedTargets` を満たさない。上書きによる修理は旧等式に違反するため、将来の保持 writer は実の制約と連言で扱う。新規の言語診断・拒否・選択は出していない。

次の作業は [exact retention の設計](../design/dots-cycle-442-c22-retention-next.md) の、canonical current state に **元の B6 producer と exact occurrence・declaration ordinal・output ordinal・body・既出の fixed target** を結び付けた typed retained equality を入れる許可された経路。現在の `Fits`／古い証拠・規則・checker は無変更。保持、局所 R22、実 public branch、I‑65 固定外形の check_sound は完了として数えない。質問ノートなし。旧 Yulang2 oracle X21 の exact runtime 例は未再現のまま。一般完全性・NoFalseRejection、停止性、Rust、Rank2 や他行は扱わない。

## 検証・公開

- 科学 pin `ca663ec06b47c9acdbfce2ad4e449e4284956551`（Lean `54677fdcb38877f141f5065ea342fd362471afdd`）。公式 Lean 4.35.0 `--trust=0 -DwarningAsError=true` により、6 production、7 standalone Audit を実 Git bytes から個別に独立物理再検証し、全 exit 0、39 宣言は標準公理のみ。4,088 / 4,088 focused prior source provenance 一致。担当側も production-only `--stdin` で 7 本の immutable Audit を再実行。Audit の import: `Yulang.*` 以外 0 件。[exact blobs と全 axiom 出力](../design/dots-cycle-442-c22-verification.md)。追試 copy を公開ノートから再構成して hash 同一、追加 QA 全体 31 標準のみ（公開 39 に加算しない）。全体 `lake build` / `tools/verify-lean.sh` / Rust は実行なし。
- 計 **23 paths**（6 production、7 Audit、barrel、6 今周 design notes、coverage、canonical report、heartbeat）。以前の Lean/Audit/補助項目はすべて byte ID 不変。凍結 `Audit.lean` / `README.md` は metadata IDs のみ。元 barrel の 376,321 bytes を保持して 6 import append。既存 notes/spec 編集なし。期待 head に nonforce `work/dots-main` のみ、canonical report と完了 HB を同じ commit で exact 再照合し writer release。

最終照合の正本 `integration/m1-final@fbbf227b2023e0da5d18d8f5c3826545f6b79e28`（Lean `f9471c73c28ed615317a4de8ff847af8b093e97d`）に C442 の Lean tree の exact 採用はまだ確認していない。今回の証明・対照は `work/dots-main` 上。監督役の全体検証は別。

**C の残り: scoped 一覧の 1 行（C22）。** [coverage](../design/dots-cycle-442-c-coverage.md)
