# M1 モデルの忠実性の監査 (2026-11-08)

対象: `integration/m1-final`、開始 commit `030a29c3bd9710d04df85cd984e612d361822a76`。
依頼の「作業 0」。証明の追加より先に、定義と規範を照合した。
以下の「不一致」は既存 Lean 定理の反証ではなく、その定義を現在の Yulang のモデルとして使う際の不一致である。
元の statement と証明は保存し、表の局所結果を B1〜B5 の E1/E2 に昇格させない。

## 1. 規範と判定方法

最初に次の旧文書を全文読んだ。

- `notes/reference/2026-06-02-role-system-yulang2.md`: 中心なしの上下境界、同一実引数の併合と交差制約、全出現の簡約、role residual の向き・level。
- `notes/reference/2026-06-06-invariant-type-sandwich-yulang2.md`: 同一 slot の原因に基づく再 collect、constructor/effect family/role の bounds、sandwich と中心非保存。

現行の `spec/06-roles.md` 6.3〜6.5、`spec/04-types.md` 4.3・4.6、case/effect の規則を優先する。
旧文書の全 nominal 引数を不変とする読み、upper だけからの解決、確定後の曖昧候補の保留は、最新の宣言別 variance・lower-head 遅延・複数候補拒否の代用にしない。
`notes/design/2026-11-08-b4r8-interval-model.md` と `2026-11-08-b5-interval-invariance.md` は訂正の設計であり、全体 E1 の statement を変更する承認ではない。

定義を読んで、次の区別を保った。

- **一致（局所）**: 明記した入力・範囲について規則を表している。全 source への橋は別。
- **不一致**: そのまま現行の機能全体の定義として使うと、確定規則と食い違う。
- **不明／未接続**: ユーザー判断待ち、または source と局所モデルの橋がない。

## 2. 機能別の照合表

| Lean の定義 | 照らした規範 | 判定 | 影響する定理・残る接続 |
| --- | --- | --- | --- |
| `CommonRoleActualEvidence.Matches/Unique/Dictionary`、`CommonRoleInspectedSemantics.Matches` などの `∃ assignment, head[assignment] ≈ goal` | role-system の raw bounds・再帰的解決、現 spec 6.3・6.4 | **不一致**: 実 role の候補発見を任意の点代入存在に置き換えている | 旧 `dictionary_iff_special`、各 matcher/candidate/Plan exactness、停止不能還元は元点モデル内だけ。区間制約の生成・伝播・遅延・選択の全体 theorem は未接続 |
| `CommonRoleIntervals.Interval/Fits/merge/checks`、`CommonRoleIntervalGeneration.generate` | 旧二文書の中心非保存、`loA ≤ upB` / `loB ≤ upA`、現 spec 6.5 | **一致（局所）** | `fits_merge`、`valid_merge_exact`、`generate_exact`、`compile_append_exact` は任意 Common endpoint の区間代数と実 ordinary 制約生成として再利用可。候補を選ぶ手続きではない |
| `CommonRoleDeferredBounds.interval/lowerHeads/observe` | spec 6.4、B4r8 設計 3.3 の lower-head 遅延 | **一致（局所）／未接続** | `pending_exact`、`upper_only_pending`、`lower_arrives` は固定 snapshot の事実。head projection は引数のままで、全 head decoder、candidate 伝播、where 生成の停止は未証明 |
| `CommonRoleIntervalCongruence.identify` と全構文合同性 | role-system の区間由来変数等式と通常 sandwich の区別 | **一致（局所）** | `global_formula_from_generated` は生成交差制約から type 成分の同値置換を保存。具体型を他の出現から消すこと、全出現 sandwich、level 保護を証明したとはしない |
| `CommonNominalHeads.Subtype`、`CommonNominalFullDemand.ProducerLe`、`CommonNominalFullCarrier.Subtype` | spec 6.5 の宣言時 variance: `box` 共変、無限に入れ子の引数は不変 | **不一致**: nominal の全 slot を両方向観測する | `nominal_head_invariant_exact`、`nominal_finite_invariant_exact`、`nominal_regular_invariant_exact`、`fitsCommonGround.nominalInvariant` は全 slot が不変な旧部分モデルの定理として保持。現 `box` へ適用しない |
| `CommonDeclaredNominalVariance.Subtype/Variance.Rel/modeAt` | spec 6.5、B5 interval 設計 2・7 | **一致（局所）／未接続** | `nominal_head_variance_exact` は与えられた表の方向を正しく読む。実宣言 ID・arity・kind の照合がなく、欠けた表の要素は `.unused` になる。宣言表の検査と、宣言本体から表を導く算法は別の不足 |
| `CommonInvariantIntervals`、`CommonNominalIntervalReconciliation`、`CommonGroundIntervalSolver` | 旧二文書の同一実引数と交差条件、現 spec 6.5 | **一致（局所）** | 不変 slot の型・行 bounds の併合と scalar endpoint 求解に再利用可。共変 constructor の branch 合流、一般 nominal source、再帰的な carrier の全 solver ではない |
| `NominalConstructions`、`CommonNominalSiteGeneration` などの全引数の保留境界 | spec 6.5 末尾の box 訂正と「要確認」 | **不明／旧一般化は不一致** | construction-site exactness は与えた旧 site 表の事実。不変以外にも保留境界を付ける現在の source 規則とはしない。適用範囲の未回答を決めない |
| `CommonRoleCanonicalRows.capture`、`CommonRoleStableRecordResidual` | spec 4.3 と 6.3 の具体化まで遅延した record 引き算 | **一致（局所）／未接続** | `capture_no_hidden`、`checked_residual_decreases` は具体的な first-field-wins row の正準残余に有効。非退化区間の両境界、未知 tail の保留、実 generated graph との橋は別 |
| `CommonRecordInspection`、`CommonRecordTailProfiles` の masked requirement | spec 4.3: 先頭の field の要求だけを残りから取り除く | **一致（局所）** | `record_target_split`、`tail_profiles_exact` 等は意味論の部品として保持。これらの意味上の比較から、任意の tail 代入を候補として選ぶ手続きを導かない |
| `CommonEffectRequestGeneration.Declaration` の `key : Nat`、value-kind `locals`、既存 signed rows | spec 5.1 の引数付き effect family、旧 sandwich の `CompactRow.items` | **不一致／未接続**: 解決済み instance の opaque key としてはよいが、family 引数の bounds を保存・照合しない | `generate_recursive_effect_exact` と source solver の exactness は、その解決済み key・value-local 宣言に対しての定理。引数付き family の一般 theorem ではない |
| `CommonEffectInvariantIntervals.Interval/Value/EffectRow/ValueTerms` | 旧 sandwich の family 同一 slot の交差制約 | **一致（局所）／未接続** | `merge_check_exact` と interval family theorem は再利用可。row endpoint の有限制約構文、実 family/argument slot の保存・合流と dispatch は不足 |
| `CommonEffectKindedFormula`、`CommonEffectKindedGeneration.FieldScheme/constructCheckedField/useCheckedField` | spec 4.6: 作成時 rigid、使用ごとに具体化。`ref.run` の row-local `'f` | **一致（局所）／未接続** | `construct_checked_field_exact`、`use_checked_field_exact` は kind 付き束縛子の骨格に一致。有限 field 表の保存・projection、source 宣言 lowering、captured kind、構築式の effect は不足 |
| `CommonNominalFieldTemplates.Template/Body`、`CommonNominalFieldGeneration.FieldsTyping` | spec 4.6 の一般 struct field rank 2 | **不一致**: field 本体に全称束縛子がなく、nominal 引数と共有した単相 field だけ | nominal field generation exactness は旧単相 template の theorem。kinded field scheme の作成・取り出しを接続する必要がある。`∀` field の部分型・一般化・role 相互作用は仕様自体が未決 |
| `CommonEffectKindedHandler.generateCheckedHandler` と子の旧宣言表 | spec 5 の operation-local 全称 handler と kind 規則 | **一致（局所）／未接続** | 外側の存在量化→型・行 locals の全称→arm の存在量化を保持。再帰的な全 mixed-kind operation 表への統合・全 family solver は未完 |
| `CommonAlignedPatternTyping.RawTyping`、`CommonAlignedPatternGeneration.generatePattern`、`CommonPatternComputations.run` | spec 3b.3 の whole-record rest と first-field-wins、4.3・6.5 の構造的共変 payload | **一致（局所）** | pair、record/default、or の名前共有と評価順は保持。pattern の残りが全 record を見る規則と、role/type tail の引き算を混同しない |
| 同 pattern grammar の `.nil/.cons/.snoc/.nominal` と `Empty` float | spec 3b.1 と 6.5 の nominal 引数 | **未接続**: 生成は該当 branch で `.bot`、typing rule なし | 局所 `generatePattern_exact` は正しいが、全構文 `common_pattern_environment_exact` / `generate_common_case_exact` の E1 ではない |
| ordinary `Common.variant` と `Common.Ty.union` を複数 tag の source row として使うこと | spec 4.5・3b.4 の合流済み polyvariant row | **不一致** | `CommonPatternVariantRowBoundary.distinct_tag_union_payload_erased`、`no_old_upper_bound_payload_safety` は旧 ordinary carrier の情報欠落を示す。B2 全体の E2 ではない。実 row carrier への橋を残し、単一 tag・record・pair の局所結果と区別する |
| `RawTyping.defaultField` の `OptionalPayload` | spec 3b.3 の required field に default を付けると拒否する規則 | **不一致（全 source typing として）** | `CommonDefaultRequired.optionalPayload_record_same` により required 入力も意味上は通る。別の `CasePresenceValidation.required_default_rejected` を source 生成へ接続する義務が残る |
| required field の optional 入力、全 arm の静的 effect cap | B2 未回答二問、`CommonCaseCoreBoundedGeneration` | **不明（ユーザー判断待ち）** | optional field の成功 branch の扱いと到達不能 arm の静的 effect 行は決めない。有限 prefix の安全性は明記された `EvaluationSound` と cap の下での局所 theorem |

## 3. 旧 B4 E2 と補題の再利用範囲

引き継ぎにいう「4 つ」は障害の種類であり、再帰型の root-only 拒否を独立に数えると次の五行になる。

| 旧障害 theorem | 現規則との関係 | 判定 |
| --- | --- | --- |
| `CommonRoleRegularResolutionObstruction.amended_registry_undecidable` | 再帰 clock の root が現 K2 の拒否位置になる。interval lowering の還元も未証明 | 旧点モデルの結果。現 B4 の E2 には数えない |
| `CommonRoleReachedRootObstruction.reached_root_registry_undecidable` | root だけでなく非変数 head が再帰 constructor を inspect するときにも拒否する現 K2 を欠く | 同上 |
| `CommonRoleFiniteShadowObstruction.finite_tree_registry_undecidable` | 隠れた field を数える旧 checker。現規則は first-field-wins 後に数える | 算術・旧反例は保持。現 E2 への橋なし |
| `CommonRoleFiniteTailObstruction.normalized_registry_undecidable` | 任意の tail 代入が隠れた field を戻す。実残余は引き算で決まる | **source モデルと食い違う**。現 E2 の根拠に使わない |
| `CommonRoleMergedObstruction.canonical_merged_registry_undecidable` | 冪等な同 tag payload で旧 size を膨らませる。現規則は縮約後・捕捉後安定性を検査 | 旧反例は保持。現 E2 への橋なし |

既存 CommonRole 補題の名前単位の A/P/B 分類は、B4r8 設計メモ 5 節と末尾の全 module 索引を利用する。
再利用の判定は次の通りで、旧定理を削除・弱化しない。

| 範囲 | 再利用 | 必要な橋 |
| --- | --- | --- |
| Common 順序・合同性、有限構文、正準 record 残余、有限表 lookup | A: 元の範囲でそのまま | 実 interval endpoint / fresh slot 生成から呼ばれること |
| `Matches`、candidate、`Unique`、dictionary/Plan、停止不能 iff | P: 点モデルについて保持 | 区間の実制約生成・伝播・選択との一致。現在はない |
| `CommonRoleStablePaterson.check_sound`、head determination、shared payload の下降 | B: 算術と有限 component を利用可 | 現 variance・正規化・実 capture 後の全 where 子の下降 |
| `CommonRoleNominalCoverBoundary.box_invariant` | 旧不変 ID の局所 theorem のみ | 現仕様の共変 `box` には適用不可 |

**遅延だけでは停止根拠にならない。** すべての子の lower head が既知である増大鎖を遅延で止めることはできない。
`impl R 'a where (list 'a): R` はこの例であり、現仕様の宣言時下降検査で拒否する。
一般の interval resolver に対する実下降 measure の構成は残っている。

## 4. この後の作業の境界

監査で確認した入力を持つ局所部品から進める。親 theorem の量化子・前提・完了判定は変更しない。

- B5/B1: 実宣言 ID・arity・kind を検査して各 slot の方向を読む有限 inspector。不変 slot だけの区間生成を区別する。
- B3: 型・行 bounds の有限保存と交差制約、全称 field scheme の有限表と使用ごとの具体化。
- B2: 既存の coverage と実 computation の有限終了 prefix を接続し、全 arm が miss する終了を除外する。
- B4: 中心なし区間の正準 record 残余と共有 graph への制約生成、既存 finite cause/worklist と遅延の橋を進める。

全 B4 と declaration-aware B5/B1 の statement の訂正案は `notes/questions/2026-11-08-m1-interval-statement-alignment.md` に分離する。
未承認案を E1/E2 の目標として採用しない。B6 はこの表の不一致が解消するまで開始しない。A2 の契約は変更しない。

## 5. 初期検証

開始 commit のソースに変更を加えず、Lean 4.35.0 で次を実行した。

```text
cd lean
lake build --wfail
Build completed successfully (1009 jobs).
lake env lean --trust=0 Audit.lean
exit 0
```

実行環境の PATH に Lean が無かったため、指定 toolchain の配布物を取得した。
また、この executor では数値 PID の `/proc/<pid>/exe` と現在プロセスの namespace が一致しないため、
**自分自身の実行ファイルパスの参照だけ**を同じプロセスを指す `/proc/self/exe` に読み替える環境補助を使った。
Lean の配布バイナリ・ソース・kernel・trust 値は変更していない。この補助はリポジトリの変更ではない。
