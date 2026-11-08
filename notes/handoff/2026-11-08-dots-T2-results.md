# dots T2 結果: optional field の source 統合 (2026-11-08)

状態: 作業者側の T2 受け入れ条件を達成、監督役の統合検証待ち（needs-verify）。
公開先は **work/dots-T2 のみ**。integration/m1-final / yulang3 / main への書き込みなし。

## 結論

**X22: PROVED（新しい source structural entry において）。**

- 既存の `optionalSource 0 int = exactEmpty | required 0 int` を入力にして、default なしの `{port: p}` を新しい再帰的な主 pattern 生成器で受理する。
- optional 規則は root の特例ではなく、pair・field・defaultField・variant・or・as の子へ再帰的に適用される。
- Q4 の scope、Q7 の名前検査、or の名前順整列、同じ binder slots の guard/body への供給を保持する。
- `CommonSourceArmsSolved.principal / infer` が、`{port:p} -> p; _ -> 80` の **両 arm の環境・body をまとめて生成**し、同じ optional 入力の実際の有限返却 scheme instance を持つ。
- 変更していない `ScopedCaseDataProgram.eval` で、空 record は first arm の miss を経て second arm で 80 を返すことを trace ごと証明した。すべての整数 port について、存在時はその整数を返す。
- 旧 `CommonOptionalFieldBoundary.strict_rejects` 等は保存。旧入口の rejection と、新しい入口での acceptance は異なる judgment についての定理で、矛盾しない。
- **全体 B2、B6、Core.infer が完成したとは主張しない。** 旧 `SpecExamples.lean` の歴史的状態欄も変更していない。T4 の一覧統合は別タスク。

## 実行と時刻

- 開始: 2026-11-08T06:45:54+00:00（15:45:54 JST）。
- clone で固定した base: `8663e3a021585622c3feae5b3ab8d676a69f5ca7`（短縮 `8663e3a02`）。途中で base を動かしていない。
- 検証したローカル commit: `fb65a79f968f470617f7524a0a2f6ce57b2ac56c`。
- 最終検証開始: 2026-11-08T06:56:37.358594+00:00。
- 最終検証終了: 2026-11-08T06:57:16.291642+00:00。
- 最終 verify の所要: **38.933 秒**（incremental build。fresh build の時間ではない）。
- この報告の作成時点: 2026-11-08T07:00:20.711206+00:00。開始から **866.7 秒（約 14.4 分）**。公開通信・fetch 照合の最終終了はチャットの最終報告で補足する。
- 使用量の枠と消費量: 確認用の実績データが無いため不明。今回の継続時間を製品の実行上限とは扱わない。

実行した主なコマンド:

```sh
git clone --branch integration/m1-final --single-branch https://github.com/momota1029/yulang.git yulang-dots-T2
git switch -c work/dots-T2
# 前回の elan を再利用。Lean v4.35.0。
export ELAN_HOME=/workspace/scratch/1d0b4aaa3394/dots-probe-elan
export PATH="$ELAN_HOME/bin:$PATH"
bash tools/verify-lean.sh . origin/integration/m1-final
cd lean && lake build Yulang.CommonSourceOptionalX22
cd lean && lake build --wfail
bash tools/verify-lean.sh . origin/integration/m1-final
```

baseline は 1108 jobs / Audit exit 0 / 5956 printed declarations /
AXIOM-GATE-PASS 81212 declarations / verify PASS。新しいモジュールが root import に
入る前の既存コードを検証した。その間に新規ファイルを作ったが、baseline の判定は
新規コードの検証とは数えていない。

focused X22 は 241 jobs、exit 0。12 個の新規モジュールは、依存順に一つずつ
`Yulang.lean` の import と `Audit.lean` の主要定理登録を追記し、
`lake build --wfail` を通してから個別 commit した（1109〜1120 jobs、いずれも exit 0）。
README は別 commit。差分は追記のみ。最後の全体検証の出力全文は以下。

```text
verify-lean: . @ fb65a79f9 (base origin/integration/m1-final)
ok: lake build --wfail (Build completed successfully (1120 jobs).)
ok: Audit.lean exit 0
ok: axioms only propext/Classical.choice/Quot.sound over 5996 printed declarations
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended
ok: AXIOM-GATE-PASS: 81482 declarations
verify-lean: PASS
```

終了コード: **0**。FAIL / REVIEW 行は最終検証では 0 件。

## 追加定理の日本語での主張

以下の量化はすべて普遍量化。`∃` は記述した結果の存在量化である。
未記載の「solver が成功する」「実行が返る」「任意の callback が正しい」などを
暗黙の前提にはしていない。各 statement の正確な型は末尾に Lean の `#check @…`
による全 74 公開定理の出力を載せた（暗黙引数も表示）。

### 1. CommonSourcePatternTyping

- `RawTyping.binding_names`: 任意の default 関係、環境、pattern、入力型、出力 bindings に対し、新 RawTyping の導出があれば、pattern の名前列は bindings の名前列と等しい。
- `required_optional`: 任意の入力型 input、payload 型、field 名 name について、`input ≤ required name payload` なら `OptionalPayload name input payload`。
- `legacy_preserved`: 任意の default 関係・環境・pattern・input・bindings に対し、旧 aligned RawTyping が成り立つなら、同じ引数の新 RawTyping が成り立つ。旧定理を弱めたものではなく、新規の埋め込み定理。

### 2. CommonSourcePatternInversion

すべて、任意の default 関係、既存環境、入力型、出力 bindings について。
- `Root.typing`: root 規則の導出から新 RawTyping を得る。
- `typing_root_exact`: RawTyping と、ある original 型が存在して `input ≤ original` かつその original で Root が成り立つことは同値。
- `wildcard_iff`: wildcard の導出と bindings が空であることは同値。
- `bind_iff`: 名前 name の束縛の導出と、ある result 型について bindings が `[(name,result)]` かつ `input ≤ result` は同値。
- `literal_iff`: literal の導出と、bindings が空で input が literal の base 型以下であることは同値。
- `range_iff`: range の導出と、bindings が空・input ≤ int・上下どちらかの端点があることは同値。
- `pair_iff`: pair の導出と、ある a,b,left,right について bindings=left++right、input≤pair a b、最初の子が types で a から left を作り、次の子が left++types で b から right を作ることは同値。
- `recordEnd_iff`: recordEnd の導出と、bindings が空かつ input≤emptyRecord は同値。
- `field_iff`: field name p rest の導出と、ある original,payload,left,right について bindings=left++right、input≤original、OptionalPayload name original payload、p が types で payload から left、rest が left++types で original から right を作ることは同値。presence の全値保証は前提にない。
- `defaultField_iff`: さらに fallbackType が存在し、default 関係が types/fallback/fallbackType に成り立ち、p の入力が payload|fallbackType であること。他の前提・出力は field の上記の形。これは既存 default 規則を保存するもので declared-required 禁止の追加ではない。
- `variant_iff`: ある payload について input≤variant tag payload、子の導出が同じ bindings を返すことと同値。
- `or_iff`: 両枝が同じ input で導出でき、右枝の出力は右枝の名前順で reorder した bindings であることと同値。
- `as_iff`: ある original/rest について出力が (name,original)::rest、input≤original、子が original から rest を作ることと同値。

### 3. CommonSourcePatternGeneration / Allocation

全スロット型 α、代入 ρ、symbolic/semantic 環境について `EnvRel Common.model ρ symbolic semantic` を前提とし、任意の pattern、累積 prior bindings、input term、出力 binding terms に対して:
- `generatePattern_exact`: 生成式が ρ で成り立つ iff、評価済み prior/input/bindings に対する独立の新 RawTyping が成り立つ。
- `constraints_exact`: 任意の同時 binder 値 `Fin pattern.names.length → Comp` に対して、allocator の式が ambient ρ をその値で延長した代入で成り立つ iff、その bindingValues を返す新 RawTyping。
- `generateAllocatedPattern_exact`: close 済み式の成立 iff、ある bindings を返す新 RawTyping が存在。
- `allocated_bindings_exact`: 任意に指定した bindings に対し、その bindings に等しくなる slot 値を生成式のモデルとして得られる iff、その bindings に対する RawTyping。
- `withPattern_exact`: 任意の consumer 式について、pattern と consumer を同じ binder scope で close した式の成立 iff、ある同時 binder 値において RawTyping と consumer 成立の両方が成り立つ。
- `generateCheckedPattern_exact`: 実際の名前検査を含む生成式の成立 iff、ある bindings に対する新 Typing（NamesValid ∧ RawTyping）が存在。
- `evalTypes_reorder`: 全代入・名前列・binding terms に対し評価と名前順 reorder は可換。
- `nilBindings_exact`: 全 bindings/formula/ρ に対し nilBindings の成立 iff、評価 bindings が空かつ formula 成立。
- `Examples.reversed_or_typable` / `reversed_or_generated`: 閉じた具体例 `(x,y)|(y,x)` を int×int に適用すると、同じ名前に同じ型を与える整列済み新判断が成り立ち、checked 生成式も成立。

### 4. CommonSourcePatternGenerationProvenance

- `bindings_reorder`: 全 GoodBindings な列・名前列に対し、reorder 後も GoodBindings。
- `safe_generatePattern`: 任意の pattern/α/環境/prior/input/bindings について、環境が SafeEnvironment、prior と bindings が GoodBindings、input が Input を満たすなら生成式は SafeFormula。
- `bindingSlots_good`: 任意の α と名前列について allocator の bindingSlots は GoodBindings。
- `safe_close`: 任意 n と Slots α n 上の SafeFormula について close n 後も SafeFormula。
- `safe_constraints` / `safe_allocated`: 任意の pattern/α/環境/prior/input に対し、それぞれ SafeEnvironment/GoodBindings/Input の前提のもと、allocator の constraints/closed 式は SafeFormula。
- `principal_safe`: 任意 pattern の principalPattern は SafeFormula（入力 var none、空環境・空 prior。追加前提なし）。
- `generated_invariants`: 任意 pattern、principal の正規化結果に属する任意 clause の pack は GoodAtoms（endpoint）、GoodAtoms（row support）、WidthAtoms の三条件を満たす。

### 5. CommonSourcePatternElaboration

任意の source/Core 環境・semantic 環境について `Core.CommonSyntax.EnvRel` を前提とする。
- `preserved`: 任意の default 付き source pattern、累積 types、input、bindings に対して、source の新 RawTyping があれば source coverage check が true で、既存の実 Q4 lowering 後の新 RawTyping が同じ input/bindings に成り立つ。
- `reflected`: lowered 側の新 RawTyping、source の coverage check=true、およびその source の lowering が当該 lowered pattern と等しいことから、元の source の新 RawTyping を得る。
- `raw_typing_exact` / `source_typing_exact`: 任意の pattern/types/input/bindings について、新 RawTyping（または NamesValid を含む Typing）と、coverage check=true かつ lowering 後の同じ判断は同値。
- `generateSourcePattern_exact`: 任意の source pattern、outer names、α、代入、symbolic/semantic/Core 環境、prior binding terms、input term に対して、Core EnvRel と symbolic EnvRel の両方があれば、実 source 生成式成立 iff、評価済み prior/input に対してある bindings を返す source Typing が存在。

### 6. CommonSourceArmGeneration / ArmSolved / ArmsSolved

- `CommonSourceArmGeneration.generateEnvironments_exact`: 任意の source pattern/guard/body、outer names、α、代入、symbolic/semantic/Core 環境、input term、guard row term、result comp term に対して、両 EnvRel を前提とし、生成式成立 iff、同じ評価入力/行/結果について独立の EnvironmentTyping が成り立つ。独立判断は pattern に加え、同じ純粋 monomorphic bindings による guard と body の型付けを要求する。
- `CommonSourceArmsSolved.generateAll_exact`: 同じ環境関係を前提とし、任意の有限 arm 列について generateAll 成立 iff、その列のすべての arm が同じ評価済み input/guardRow/result で EnvironmentTyping を満たす。実行順に全 arm を実行するという主張ではない。
- `safe_generateEnvironments` / `safe_generateAll`: 任意の source arm（列）と symbolic 環境/input/guardRow/result に対して、SafeEnvironment、Input input、simpleRow guardRow=true、BinderType result.ty、simpleRow result.row=true を前提に生成式の SafeFormula。
- 両 Solved namespace の `principal_safe`: 任意の outer names と source arm（列）、空環境と3つの根 var で作る principal は SafeFormula。
- 両 namespace の `principal_exact`: 任意の outer names、arm（列）、全 `Fin 3 → Comp` 代入について、principal の成立 iff、代入0の型・代入1の行・代入2の計算を使う EnvironmentTyping（列では全 arm）。
- 両 namespace の `all_parameter_environments`: 任意の outer names、arm（列）、実際の infer の返却リストに含まれる scheme、**その scheme の任意の Parameters** について、instantiate した3根で EnvironmentTyping（列では全 arm）が成り立つ。パラメータへの residual 条件なし。
- 両 namespace の `environments_instances_exact`: 任意の outer names、arm（列）、全3根代入について、独立 EnvironmentTyping（列では全 arm） iff、実返却リストに scheme が存在し、その Parameters が存在して instantiate と元代入が AssignmentEquivalent。
- 両 namespace の `environments_rejected_exact`: 任意の outer names、arm（列）について infer=[] iff、EnvironmentTyping（列では全 arm）を満たす3根代入が存在しない。
- `CommonSourceArmsSolved.returned_scheme_actual_partial`: 任意の outer names、arm 列、実際に返却された scheme、任意パラメータ、floatCheck、default/guard/body callback、value/index に対し、default の DefaultPartialSound、default/guard/body の名前不変性、body の BodyPartialSound、および instantiate した入力型の valueAt を前提とすると、変更していない実 runArms の結果は PartialResult。これは「成功して返れば結果型を持つ」であり、error/miss/停止を除外しない。

### 7. CommonSourcePatternPartialSafety / CommonSourceCasePartial

- `bindingTypes_reorder`: 任意の名前列と NamedTypes について bindingTypes と reorder は可換。
- `partial_alignResult`: 任意の型列・観測・名前列について元の観測が PartialHolds なら、整列後の観測は整列後の型列の PartialHolds。
- `typing_matches_partial`: 任意の default 型関係、floatCheck、default evaluator、型付け済み新 RawTyping に対し、DefaultPartialSound、NamesValid、累積環境が bindingTypes を満たすこと、実値が input の valueAt を満たすことを前提に、aligned matcher の結果は出力 bindings の PartialHolds。
- `testArm_partial`: 任意の型付き source arm、floatCheck/default/guard callbacks、value/index に対し、DefaultPartialSound、新 Typing、input の valueAt を前提に、空累積環境の aligned testArm の結果は bindings の PartialHolds。
- `runArms_partial`: 任意の source arm 列、環境、input/result、callbacks/value/index に対し、DefaultPartialSound、BodyPartialSound、各 arm がある guardRow で EnvironmentTyping を満たすこと、valueAt input value を前提に、aligned runArms の結果は PartialResult result.ty。
- `actual_runArms_partial`: 上の全前提に default/guard/body の名前不変性を加えると、変更していない ScopedCaseEvaluation.runArms にも同じ PartialResult が成り立つ。

### 8. CommonSourceOptionalX22

ここで固定している input は既存 optionalSource 0 int、first arm は `{port:p}->p`、second arm は `_ -> 80`。環境・outer names は空。
- `pattern_typed`: この pattern は新 Typing において bindings=[(0,int)] を返す（名前検査を含む）。
- `x22_source_generated`: 入力根を optional subject にした代入に対して実 source pattern 生成式が成立。
- `first_arm_typed` / `last_arm_typed`: 各固定 arm が optional subject、guardRow empty、純粋 int 結果の EnvironmentTyping を持つ。
- `arms_typed`: この2 arm 列のすべての要素について、assignment（0=optional subject、1=pure unit、2=pure int）で EnvironmentTyping。
- `x22_case_generated`: 同 assignment が実 arm-list principal 生成式のモデル。
- `x22_real_scheme_instance`: 実 arm-list infer の結果に scheme が存在し、そのパラメータが存在して assignment と同値になる。
- `x22_missing_field_misses`: 空 record に対する実 matcher の観測は、空 trace の ok none と等しい。
- `x22_absent_case_result`: 空 record を source とする実 case 全体の観測は、trace `[scrutinee, source emptyRecord, arm 0, arm 1, body 1, source fallback]` と ok(some 80) の組に等しい。前提なし。
- `x22_present_case_result`: **すべての整数 port** について、source record が field 0 にその整数を持つ実 case の結果は ok(some port)。前提なし。
- `x22_any_absent_field_misses`: **すべての record fields と外側 environment** について、lookup 0 fields=none なら実 matcher の観測は空 trace の ok none。
- `nested_pattern_typed`: 外側 required field 1 の中にこの optional subject/pattern を置いた具体例も新 Typing で同じ [(0,int)] を返す。
- `nested_source_generated`: 同じ入れ子例の source 生成式も対応する入力根代入で成立。
- `x22_proved`: 同 case principal の成立、空 record 実行結果80、および全整数portの実行結果portの3つの連言。成功 callback、coverage oracle、未証明の frontier、fuel を前提にしない。

非公開の証明用補題2本も新規: Generation の `binding_split` は任意の型付け済み子と bindings=left++right に対し、その子の名前数で take/drop した評価 bindings が left/right に等しいこと。PartialSafety の `andThen_partial` は最初の観測の PartialHolds と、任意の成功 bindings に対する後続観測の PartialHolds を前提に、連結観測が left++right の PartialHolds を持つこと。これらは外部入口ではない。

## 確かめていないこと・制限・中断

- 既存の Lean ファイルは `Yulang.lean`、`Audit.lean`、`README.md` に追記しただけ。spec/ は変更していない。新しい公理、証明の穴、カーネルを迂回する決定手続きは追加していない。
- Lists/nominals の pattern、full B2 の一般 source prefix adequacy・coverage・停止性・aggregate effects、公開 Core.infer は未統合。今回の新入口は旧 structural entry の後継である。
- defaultField に対する declared-required 禁止は、旧来の source presence metadata 検査の課題を残す。OptionalPayload 単独ではその禁止を表さず、今回その規則を拡大も変更もしていない。
- 一般の partial safety は callback の成功時 soundness/name invariance を明示前提に持つ。X22 の具体的な source 実行等式にはそれらの仮定はない。
- semantic な設計判断が必要な新しい未決事項には当たらなかった。今回の変更は既に承認された推奨案1の実装。新規質問ノートは0本。
- 計画表の運用に従い running を記録する試みは、GitHub アプリの auto-review に「既存 plan 更新の明示許可がない」と拒否された。回避せず、ローカルの自分の plan 編集も打ち消し commit で元に戻した。公開 plan は base のまま。実装・報告公開は許可され成功した。
- baseline build と focused build を同時に走らせた最初の focused 試行は、既存 `CommonGeneratedChildClosure.olean` の no such file or directory で exit1。並行実行を避けて再試行したら成功した。根本原因を独立診断したわけではなく、既存ソースを修正してはいない。セッション消失・環境再作成・時間切れは起きていない。
- 最初の全体最終検証は PASS with 1 REVIEW: 新規ファイルの説明コメントの `syntax premises...` 行を検査スクリプトが syntax 宣言と誤検出した。コメントを `syntactic premises...` に変え、再検証した最終結果が上記の REVIEW なし PASS。
- 補助の型一覧作成は最初 `pp.width` オプションが不明で exit1。その不要なオプションを外して `lake env lean --trust=0 /tmp/T2Types.lean` を再実行し exit0。付録はその成功出力。
- CLI push は今回試していない。前回と同じ GitHub アプリで作成・更新。ローカル commit と GitHub contents API の commit SHA は異なるので、公開内容を fetch し、tree の差分ゼロで同一性を確認する。
- 対象ブランチ以外への公開、統合、PR 作成はしていない。CI や他環境での再検証は未確認。

## 公開ファイル

コード・README・Audit の **15 ファイルは公開済み**（初回一式の commit `e15e03224071405b19acac8def163710629b0373`、コメント修正後 `1752cb50d0b2f33753bd5387cea8343d82865df4`）。
fetch 後の初回 tree 比較は差分ゼロ。最終公開はこの報告1本を加えた **16 ファイル**。
公開は開始から30分以内に行ったため、30〜40分の周期より前に最終成果へ到達している。

- `lean/Audit.lean`
- `lean/README.md`
- `lean/Yulang.lean`
- `lean/Yulang/CommonSourceArmGeneration.lean`
- `lean/Yulang/CommonSourceArmSolved.lean`
- `lean/Yulang/CommonSourceArmsSolved.lean`
- `lean/Yulang/CommonSourceCasePartial.lean`
- `lean/Yulang/CommonSourceOptionalX22.lean`
- `lean/Yulang/CommonSourcePatternAllocation.lean`
- `lean/Yulang/CommonSourcePatternElaboration.lean`
- `lean/Yulang/CommonSourcePatternGeneration.lean`
- `lean/Yulang/CommonSourcePatternGenerationProvenance.lean`
- `lean/Yulang/CommonSourcePatternInversion.lean`
- `lean/Yulang/CommonSourcePatternPartialSafety.lean`
- `lean/Yulang/CommonSourcePatternTyping.lean`
- `notes/handoff/2026-11-08-dots-T2-results.md`

## 付録: 74 公開定理の実際の型

`lake env lean --trust=0 /tmp/T2Types.lean`（各定理に `#check @完全修飾名`）の出力全文。
全暗黙引数・環境関係・callback 契約もここで明示される。上の日本語の範囲はこの型を越えない。

```text
@Yulang.CommonSourceArmGeneration.generateEnvironments_exact : ∀ {α : Type}
  (pattern : Yulang.CasePatterns.Pattern Empty (Yulang.CaseDataTerms.Expr Empty)) (outerNames : List Nat)
  (ρ : α → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model)
  (symbolic : Yulang.Core.PresenceGeneration.SchemeEnv α)
  (environment : List (Yulang.Core.CommonSyntax.Binding Yulang.Common.model))
  (semantic : List (Yulang.Core.PresenceGeneration.Binding Yulang.Common.model)),
  Yulang.Core.CommonSyntax.EnvRel Yulang.Common.model environment semantic →
    Yulang.Core.PresenceGeneration.EnvRel Yulang.Common.model ρ symbolic semantic →
      ∀ (guard : Option (Yulang.CaseDataTerms.Expr Empty)) (body : Yulang.CaseDataTerms.Expr Empty)
        (input : Yulang.Core.PresenceGeneration.TyTerm α) (guardRow : Yulang.Core.PresenceGeneration.RowTerm α)
        (result : Yulang.Core.PresenceGeneration.CompTerm α),
        Yulang.Core.PresenceGeneration.Formula.Holds Yulang.Common.model ρ
            (Yulang.CommonSourceArmGeneration.generateEnvironments outerNames symbolic pattern guard body input guardRow
              result) ↔
          Yulang.CommonSourceArmGeneration.EnvironmentTyping outerNames environment pattern guard body
            (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model ρ input)
            (Yulang.Core.PresenceGeneration.RowTerm.eval Yulang.Common.model ρ guardRow)
            (Yulang.Core.PresenceGeneration.CompTerm.eval Yulang.Common.model ρ result)
@Yulang.CommonSourceArmSolved.safe_generateEnvironments : ∀ {α : Type} (outerNames : List Nat)
  (environment : Yulang.Core.PresenceGeneration.SchemeEnv α),
  Yulang.CommonPatternGenerationProvenance.SafeEnvironment environment →
    ∀ (pattern : Yulang.CasePatterns.Pattern Empty (Yulang.CaseDataTerms.Expr Empty))
      (guard : Option (Yulang.CaseDataTerms.Expr Empty)) (body : Yulang.CaseDataTerms.Expr Empty)
      (input : Yulang.Core.PresenceGeneration.TyTerm α),
      Yulang.CommonPatternGenerationProvenance.Input input →
        ∀ (guardRow : Yulang.Core.PresenceGeneration.RowTerm α),
          Yulang.PresenceSourceConstraintSupport.simpleRow guardRow = true →
            ∀ (result : Yulang.Core.PresenceGeneration.CompTerm α),
              Yulang.CommonPatternGenerationProvenance.BinderType result.ty →
                Yulang.PresenceSourceConstraintSupport.simpleRow result.row = true →
                  Yulang.CommonPatternGenerationProvenance.SafeFormula
                    (Yulang.CommonSourceArmGeneration.generateEnvironments outerNames environment pattern guard body
                      input guardRow result)
Yulang.CommonSourceArmSolved.principal_safe : ∀ (outerNames : List Nat)
  (pattern : Yulang.CasePatterns.Pattern Empty (Yulang.CaseDataTerms.Expr Empty))
  (guard : Option (Yulang.CaseDataTerms.Expr Empty)) (body : Yulang.CaseDataTerms.Expr Empty),
  Yulang.CommonPatternGenerationProvenance.SafeFormula
    (Yulang.CommonSourceArmSolved.principal outerNames pattern guard body)
Yulang.CommonSourceArmSolved.principal_exact : ∀ (outerNames : List Nat)
  (pattern : Yulang.CasePatterns.Pattern Empty (Yulang.CaseDataTerms.Expr Empty))
  (guard : Option (Yulang.CaseDataTerms.Expr Empty)) (body : Yulang.CaseDataTerms.Expr Empty)
  (assignment : Fin 3 → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model),
  Yulang.Core.PresenceGeneration.Formula.Holds Yulang.Common.model assignment
      (Yulang.CommonSourceArmSolved.principal outerNames pattern guard body) ↔
    Yulang.CommonSourceArmGeneration.EnvironmentTyping outerNames [] pattern guard body (assignment 0).fst
      (assignment 1).snd (assignment 2)
Yulang.CommonSourceArmSolved.all_parameter_environments : ∀ (outerNames : List Nat)
  (pattern : Yulang.CasePatterns.Pattern Empty (Yulang.CaseDataTerms.Expr Empty))
  (guard : Option (Yulang.CaseDataTerms.Expr Empty)) (body : Yulang.CaseDataTerms.Expr Empty)
  (scheme : Yulang.CommonPatternFiniteSchemes.Scheme 3),
  scheme ∈ Yulang.CommonSourceArmSolved.infer outerNames pattern guard body →
    ∀ (parameters : scheme.Parameters),
      Yulang.CommonSourceArmGeneration.EnvironmentTyping outerNames [] pattern guard body
        (scheme.instantiate parameters 0).fst (scheme.instantiate parameters 1).snd (scheme.instantiate parameters 2)
Yulang.CommonSourceArmSolved.environments_instances_exact : ∀ (outerNames : List Nat)
  (pattern : Yulang.CasePatterns.Pattern Empty (Yulang.CaseDataTerms.Expr Empty))
  (guard : Option (Yulang.CaseDataTerms.Expr Empty)) (body : Yulang.CaseDataTerms.Expr Empty)
  (assignment : Fin 3 → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model),
  Yulang.CommonSourceArmGeneration.EnvironmentTyping outerNames [] pattern guard body (assignment 0).fst
      (assignment 1).snd (assignment 2) ↔
    ∃ scheme,
      scheme ∈ Yulang.CommonSourceArmSolved.infer outerNames pattern guard body ∧
        ∃ parameters,
          Yulang.CommonPatternFormulaEquivalence.AssignmentEquivalent (scheme.instantiate parameters) assignment
Yulang.CommonSourceArmSolved.environments_rejected_exact : ∀ (outerNames : List Nat)
  (pattern : Yulang.CasePatterns.Pattern Empty (Yulang.CaseDataTerms.Expr Empty))
  (guard : Option (Yulang.CaseDataTerms.Expr Empty)) (body : Yulang.CaseDataTerms.Expr Empty),
  Yulang.CommonSourceArmSolved.infer outerNames pattern guard body = [] ↔
    ¬∃ assignment,
        Yulang.CommonSourceArmGeneration.EnvironmentTyping outerNames [] pattern guard body (assignment 0).fst
          (assignment 1).snd (assignment 2)
@Yulang.CommonSourceArmsSolved.generateAll_exact : ∀ {α : Type} (outerNames : List Nat)
  (arms : List Yulang.CommonSourceArmsSolved.SourceArm)
  (ρ : α → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model)
  (symbolic : Yulang.Core.PresenceGeneration.SchemeEnv α)
  (environment : List (Yulang.Core.CommonSyntax.Binding Yulang.Common.model))
  (semantic : List (Yulang.Core.PresenceGeneration.Binding Yulang.Common.model)),
  Yulang.Core.CommonSyntax.EnvRel Yulang.Common.model environment semantic →
    Yulang.Core.PresenceGeneration.EnvRel Yulang.Common.model ρ symbolic semantic →
      ∀ (input : Yulang.Core.PresenceGeneration.TyTerm α) (guardRow : Yulang.Core.PresenceGeneration.RowTerm α)
        (result : Yulang.Core.PresenceGeneration.CompTerm α),
        Yulang.Core.PresenceGeneration.Formula.Holds Yulang.Common.model ρ
            (Yulang.CommonSourceArmsSolved.generateAll outerNames symbolic input guardRow result arms) ↔
          ∀ (arm : Yulang.CommonSourceArmsSolved.SourceArm),
            arm ∈ arms →
              Yulang.CommonSourceArmGeneration.EnvironmentTyping outerNames environment arm.pattern arm.guard arm.body
                (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model ρ input)
                (Yulang.Core.PresenceGeneration.RowTerm.eval Yulang.Common.model ρ guardRow)
                (Yulang.Core.PresenceGeneration.CompTerm.eval Yulang.Common.model ρ result)
@Yulang.CommonSourceArmsSolved.safe_generateAll : ∀ {α : Type} (outerNames : List Nat)
  (arms : List Yulang.CommonSourceArmsSolved.SourceArm) (environment : Yulang.Core.PresenceGeneration.SchemeEnv α),
  Yulang.CommonPatternGenerationProvenance.SafeEnvironment environment →
    ∀ (input : Yulang.Core.PresenceGeneration.TyTerm α),
      Yulang.CommonPatternGenerationProvenance.Input input →
        ∀ (guardRow : Yulang.Core.PresenceGeneration.RowTerm α),
          Yulang.PresenceSourceConstraintSupport.simpleRow guardRow = true →
            ∀ (result : Yulang.Core.PresenceGeneration.CompTerm α),
              Yulang.CommonPatternGenerationProvenance.BinderType result.ty →
                Yulang.PresenceSourceConstraintSupport.simpleRow result.row = true →
                  Yulang.CommonPatternGenerationProvenance.SafeFormula
                    (Yulang.CommonSourceArmsSolved.generateAll outerNames environment input guardRow result arms)
Yulang.CommonSourceArmsSolved.principal_safe : ∀ (outerNames : List Nat)
  (arms : List Yulang.CommonSourceArmsSolved.SourceArm),
  Yulang.CommonPatternGenerationProvenance.SafeFormula (Yulang.CommonSourceArmsSolved.principal outerNames arms)
Yulang.CommonSourceArmsSolved.principal_exact : ∀ (outerNames : List Nat)
  (arms : List Yulang.CommonSourceArmsSolved.SourceArm)
  (assignment : Fin 3 → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model),
  Yulang.Core.PresenceGeneration.Formula.Holds Yulang.Common.model assignment
      (Yulang.CommonSourceArmsSolved.principal outerNames arms) ↔
    ∀ (arm : Yulang.CommonSourceArmsSolved.SourceArm),
      arm ∈ arms →
        Yulang.CommonSourceArmGeneration.EnvironmentTyping outerNames [] arm.pattern arm.guard arm.body
          (assignment 0).fst (assignment 1).snd (assignment 2)
Yulang.CommonSourceArmsSolved.all_parameter_environments : ∀ (outerNames : List Nat)
  (arms : List Yulang.CommonSourceArmsSolved.SourceArm) (scheme : Yulang.CommonPatternFiniteSchemes.Scheme 3),
  scheme ∈ Yulang.CommonSourceArmsSolved.infer outerNames arms →
    ∀ (parameters : scheme.Parameters) (arm : Yulang.CommonSourceArmsSolved.SourceArm),
      arm ∈ arms →
        Yulang.CommonSourceArmGeneration.EnvironmentTyping outerNames [] arm.pattern arm.guard arm.body
          (scheme.instantiate parameters 0).fst (scheme.instantiate parameters 1).snd (scheme.instantiate parameters 2)
Yulang.CommonSourceArmsSolved.environments_instances_exact : ∀ (outerNames : List Nat)
  (arms : List Yulang.CommonSourceArmsSolved.SourceArm)
  (assignment : Fin 3 → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model),
  (∀ (arm : Yulang.CommonSourceArmsSolved.SourceArm),
      arm ∈ arms →
        Yulang.CommonSourceArmGeneration.EnvironmentTyping outerNames [] arm.pattern arm.guard arm.body
          (assignment 0).fst (assignment 1).snd (assignment 2)) ↔
    ∃ scheme,
      scheme ∈ Yulang.CommonSourceArmsSolved.infer outerNames arms ∧
        ∃ parameters,
          Yulang.CommonPatternFormulaEquivalence.AssignmentEquivalent (scheme.instantiate parameters) assignment
Yulang.CommonSourceArmsSolved.environments_rejected_exact : ∀ (outerNames : List Nat)
  (arms : List Yulang.CommonSourceArmsSolved.SourceArm),
  Yulang.CommonSourceArmsSolved.infer outerNames arms = [] ↔
    ¬∃ assignment,
        ∀ (arm : Yulang.CommonSourceArmsSolved.SourceArm),
          arm ∈ arms →
            Yulang.CommonSourceArmGeneration.EnvironmentTyping outerNames [] arm.pattern arm.guard arm.body
              (assignment 0).fst (assignment 1).snd (assignment 2)
@Yulang.CommonSourceArmsSolved.returned_scheme_actual_partial : ∀ {E R : Type} (outerNames : List Nat)
  (arms : List Yulang.CommonSourceArmsSolved.SourceArm) (scheme : Yulang.CommonPatternFiniteSchemes.Scheme 3),
  scheme ∈ Yulang.CommonSourceArmsSolved.infer outerNames arms →
    ∀ (parameters : scheme.Parameters) (floatCheck : Empty → Empty → Bool)
      (defaultEval :
        Yulang.CaseValues.Bindings →
          Yulang.CaseDataTerms.Expr Empty →
            Yulang.EvaluationTrace.Logged (Yulang.CaseEvaluation.Event E) R Yulang.CaseValues.Value),
      Yulang.CommonPatternPartialSafety.DefaultPartialSound
          (Yulang.CommonPatternSourceElaboration.DefaultTyped outerNames []) defaultEval →
        Yulang.CommonPatternAlignedMatcher.DefaultInvariant defaultEval →
          ∀
            (guardEval :
              Yulang.CaseDataTerms.Expr Empty →
                Yulang.CaseValues.Bindings → Yulang.EvaluationTrace.Logged (Yulang.CaseEvaluation.Event E) R Bool),
            Yulang.CommonAlignedCaseEvaluation.NamedInvariant guardEval →
              ∀
                (bodyEval :
                  Yulang.CaseDataTerms.Expr Empty →
                    Yulang.CaseValues.Bindings →
                      Yulang.EvaluationTrace.Logged (Yulang.CaseEvaluation.Event E) R Yulang.CaseValues.Value),
                Yulang.CommonSourceCasePartial.BodyPartialSound outerNames [] bodyEval →
                  Yulang.CommonAlignedCaseEvaluation.NamedInvariant bodyEval →
                    ∀ (value : Yulang.CaseValues.Value),
                      Yulang.CommonPatternTyping.valueAt (scheme.instantiate parameters 0).fst value →
                        ∀ (index : Nat),
                          Yulang.CommonSourceCasePartial.PartialResult (scheme.instantiate parameters 2).fst
                            (Yulang.ScopedCaseEvaluation.runArms floatCheck defaultEval [] guardEval bodyEval value
                                index arms).result
@Yulang.CommonSourceCasePartial.testArm_partial : ∀ {D E R G B : Type} {input : Yulang.Common.Ty}
  {bindings : Yulang.CommonPatternEnvironment.NamedTypes} (floatCheck : Empty → Empty → Bool)
  {patternDefaults : Yulang.CommonPatternEnvironment.NamedTypes → D → Yulang.Common.Ty → Prop}
  (defaultEval :
    Yulang.CaseValues.Bindings →
      D → Yulang.EvaluationTrace.Logged (Yulang.CaseEvaluation.Event E) R Yulang.CaseValues.Value),
  Yulang.CommonPatternPartialSafety.DefaultPartialSound patternDefaults defaultEval →
    ∀
      (guardEval :
        G → Yulang.CaseValues.Bindings → Yulang.EvaluationTrace.Logged (Yulang.CaseEvaluation.Event E) R Bool)
      (arm : Yulang.CaseEvaluation.Arm Empty D G B),
      Yulang.CommonSourcePatternTyping.Typing patternDefaults [] arm.pattern input bindings →
        ∀ (value : Yulang.CaseValues.Value),
          Yulang.CommonPatternTyping.valueAt input value →
            ∀ (index : Nat),
              Yulang.CommonPatternPartialSafety.PartialHolds bindings
                (Yulang.CommonAlignedCaseEvaluation.testArm floatCheck defaultEval [] guardEval index arm value).result
@Yulang.CommonSourceCasePartial.runArms_partial : ∀ {E R : Type} {outerNames : List Nat}
  {environment : List (Yulang.Core.CommonSyntax.Binding Yulang.Common.model)} {input : Yulang.Common.Ty}
  {result : Yulang.Core.PresenceGeneration.Comp Yulang.Common.model} (floatCheck : Empty → Empty → Bool)
  (defaultEval :
    Yulang.CaseValues.Bindings →
      Yulang.CaseDataTerms.Expr Empty →
        Yulang.EvaluationTrace.Logged (Yulang.CaseEvaluation.Event E) R Yulang.CaseValues.Value),
  Yulang.CommonPatternPartialSafety.DefaultPartialSound
      (Yulang.CommonPatternSourceElaboration.DefaultTyped outerNames environment) defaultEval →
    ∀
      (guardEval :
        Yulang.CaseDataTerms.Expr Empty →
          Yulang.CaseValues.Bindings → Yulang.EvaluationTrace.Logged (Yulang.CaseEvaluation.Event E) R Bool)
      (bodyEval :
        Yulang.CaseDataTerms.Expr Empty →
          Yulang.CaseValues.Bindings →
            Yulang.EvaluationTrace.Logged (Yulang.CaseEvaluation.Event E) R Yulang.CaseValues.Value),
      Yulang.CommonSourceCasePartial.BodyPartialSound outerNames environment bodyEval →
        ∀
          (arms :
            List
              (Yulang.CaseEvaluation.Arm Empty (Yulang.CaseDataTerms.Expr Empty) (Yulang.CaseDataTerms.Expr Empty)
                (Yulang.CaseDataTerms.Expr Empty))),
          (∀
              (arm :
                Yulang.CaseEvaluation.Arm Empty (Yulang.CaseDataTerms.Expr Empty) (Yulang.CaseDataTerms.Expr Empty)
                  (Yulang.CaseDataTerms.Expr Empty)),
              arm ∈ arms →
                ∃ guardRow,
                  Yulang.CommonSourceArmGeneration.EnvironmentTyping outerNames environment arm.pattern arm.guard
                    arm.body input guardRow result) →
            ∀ (value : Yulang.CaseValues.Value),
              Yulang.CommonPatternTyping.valueAt input value →
                ∀ (index : Nat),
                  Yulang.CommonSourceCasePartial.PartialResult result.fst
                    (Yulang.CommonAlignedCaseEvaluation.runArms floatCheck defaultEval [] guardEval bodyEval value index
                        arms).result
@Yulang.CommonSourceCasePartial.actual_runArms_partial : ∀ {E R : Type} {outerNames : List Nat}
  {environment : List (Yulang.Core.CommonSyntax.Binding Yulang.Common.model)} {input : Yulang.Common.Ty}
  {result : Yulang.Core.PresenceGeneration.Comp Yulang.Common.model} (floatCheck : Empty → Empty → Bool)
  (defaultEval :
    Yulang.CaseValues.Bindings →
      Yulang.CaseDataTerms.Expr Empty →
        Yulang.EvaluationTrace.Logged (Yulang.CaseEvaluation.Event E) R Yulang.CaseValues.Value),
  Yulang.CommonPatternPartialSafety.DefaultPartialSound
      (Yulang.CommonPatternSourceElaboration.DefaultTyped outerNames environment) defaultEval →
    Yulang.CommonPatternAlignedMatcher.DefaultInvariant defaultEval →
      ∀
        (guardEval :
          Yulang.CaseDataTerms.Expr Empty →
            Yulang.CaseValues.Bindings → Yulang.EvaluationTrace.Logged (Yulang.CaseEvaluation.Event E) R Bool),
        Yulang.CommonAlignedCaseEvaluation.NamedInvariant guardEval →
          ∀
            (bodyEval :
              Yulang.CaseDataTerms.Expr Empty →
                Yulang.CaseValues.Bindings →
                  Yulang.EvaluationTrace.Logged (Yulang.CaseEvaluation.Event E) R Yulang.CaseValues.Value),
            Yulang.CommonSourceCasePartial.BodyPartialSound outerNames environment bodyEval →
              Yulang.CommonAlignedCaseEvaluation.NamedInvariant bodyEval →
                ∀
                  (arms :
                    List
                      (Yulang.CaseEvaluation.Arm Empty (Yulang.CaseDataTerms.Expr Empty)
                        (Yulang.CaseDataTerms.Expr Empty) (Yulang.CaseDataTerms.Expr Empty))),
                  (∀
                      (arm :
                        Yulang.CaseEvaluation.Arm Empty (Yulang.CaseDataTerms.Expr Empty)
                          (Yulang.CaseDataTerms.Expr Empty) (Yulang.CaseDataTerms.Expr Empty)),
                      arm ∈ arms →
                        ∃ guardRow,
                          Yulang.CommonSourceArmGeneration.EnvironmentTyping outerNames environment arm.pattern
                            arm.guard arm.body input guardRow result) →
                    ∀ (value : Yulang.CaseValues.Value),
                      Yulang.CommonPatternTyping.valueAt input value →
                        ∀ (index : Nat),
                          Yulang.CommonSourceCasePartial.PartialResult result.fst
                            (Yulang.ScopedCaseEvaluation.runArms floatCheck defaultEval [] guardEval bodyEval value
                                index arms).result
Yulang.CommonSourceOptionalX22.pattern_typed : Yulang.CommonSourcePatternTyping.Typing
  (Yulang.CommonPatternSourceElaboration.DefaultTyped [] []) [] Yulang.CommonSourceOptionalX22.pattern
  Yulang.CommonSourceOptionalX22.subject [(0, Yulang.CommonSyntax.Layer.base Yulang.Inference.Base.int)]
Yulang.CommonSourceOptionalX22.x22_source_generated : Yulang.Core.PresenceGeneration.Formula.Holds Yulang.Common.model
  (fun x => Yulang.Core.PresenceGeneration.Comp.pure Yulang.Common.model Yulang.CommonSourceOptionalX22.subject)
  (Yulang.CommonSourcePatternElaboration.generateSourcePattern [] [] [] Yulang.CommonSourceOptionalX22.pattern
    (Yulang.Core.PresenceGeneration.TyTerm.var 0))
Yulang.CommonSourceOptionalX22.first_arm_typed : Yulang.CommonSourceArmGeneration.EnvironmentTyping [] []
  Yulang.CommonSourceOptionalX22.firstArm.pattern Yulang.CommonSourceOptionalX22.firstArm.guard
  Yulang.CommonSourceOptionalX22.firstArm.body Yulang.CommonSourceOptionalX22.subject Yulang.Common.rowEmpty
  (Yulang.Core.PresenceGeneration.Comp.pure Yulang.Common.model
    (Yulang.CommonSyntax.Layer.base Yulang.Inference.Base.int))
Yulang.CommonSourceOptionalX22.last_arm_typed : Yulang.CommonSourceArmGeneration.EnvironmentTyping [] []
  Yulang.CommonSourceOptionalX22.lastArm.pattern Yulang.CommonSourceOptionalX22.lastArm.guard
  Yulang.CommonSourceOptionalX22.lastArm.body Yulang.CommonSourceOptionalX22.subject Yulang.Common.rowEmpty
  (Yulang.Core.PresenceGeneration.Comp.pure Yulang.Common.model
    (Yulang.CommonSyntax.Layer.base Yulang.Inference.Base.int))
Yulang.CommonSourceOptionalX22.arms_typed : ∀ (arm : Yulang.CommonSourceArmsSolved.SourceArm),
  arm ∈ Yulang.CommonSourceOptionalX22.arms →
    Yulang.CommonSourceArmGeneration.EnvironmentTyping [] [] arm.pattern arm.guard arm.body
      (Yulang.CommonSourceOptionalX22.assignment 0).fst (Yulang.CommonSourceOptionalX22.assignment 1).snd
      (Yulang.CommonSourceOptionalX22.assignment 2)
Yulang.CommonSourceOptionalX22.x22_case_generated : Yulang.Core.PresenceGeneration.Formula.Holds Yulang.Common.model
  Yulang.CommonSourceOptionalX22.assignment
  (Yulang.CommonSourceArmsSolved.principal [] Yulang.CommonSourceOptionalX22.arms)
Yulang.CommonSourceOptionalX22.x22_real_scheme_instance : ∃ scheme,
  scheme ∈ Yulang.CommonSourceArmsSolved.infer [] Yulang.CommonSourceOptionalX22.arms ∧
    ∃ parameters,
      Yulang.CommonPatternFormulaEquivalence.AssignmentEquivalent (scheme.instantiate parameters)
        Yulang.CommonSourceOptionalX22.assignment
Yulang.CommonSourceOptionalX22.x22_missing_field_misses : Yulang.ScopedCasePatterns.run Empty.elim
    Yulang.CaseDataTerms.defaultEval [] Yulang.CommonSourceOptionalX22.pattern
    (Yulang.CaseValues.Value.record Empty []) =
  Yulang.EvaluationTrace.Logged.ofResult (Except.ok none)
Yulang.CommonSourceOptionalX22.x22_absent_case_result : Yulang.ScopedCaseDataProgram.eval Empty.elim []
    Yulang.CommonSourceOptionalX22.absentProgram =
  {
    trace :=
      [Yulang.CaseEvaluation.Event.scrutinee, Yulang.CaseEvaluation.Event.source Yulang.CaseDataTerms.Expr.emptyRecord,
        Yulang.CaseEvaluation.Event.arm 0, Yulang.CaseEvaluation.Event.arm 1, Yulang.CaseEvaluation.Event.body 1,
        Yulang.CaseEvaluation.Event.source Yulang.CommonSourceOptionalX22.fallback],
    result := Except.ok (some (Yulang.CaseValues.Value.literal Empty (Yulang.LiteralValues.Literal.int Empty 80))) }
Yulang.CommonSourceOptionalX22.x22_present_case_result : ∀ (port : Int),
  (Yulang.ScopedCaseDataProgram.eval Empty.elim [] (Yulang.CommonSourceOptionalX22.presentProgram port)).result =
    Except.ok (some (Yulang.CaseValues.Value.literal Empty (Yulang.LiteralValues.Literal.int Empty port)))
Yulang.CommonSourceOptionalX22.x22_any_absent_field_misses : ∀ (fields environment : Yulang.CaseValues.Bindings),
  Yulang.CaseValues.lookup 0 fields = none →
    Yulang.ScopedCasePatterns.run Empty.elim Yulang.CaseDataTerms.defaultEval environment
        Yulang.CommonSourceOptionalX22.pattern (Yulang.CaseValues.Value.record Empty fields) =
      Yulang.EvaluationTrace.Logged.ofResult (Except.ok none)
Yulang.CommonSourceOptionalX22.nested_pattern_typed : Yulang.CommonSourcePatternTyping.Typing
  (Yulang.CommonPatternSourceElaboration.DefaultTyped [] []) [] Yulang.CommonSourceOptionalX22.nestedPattern
  (Yulang.Common.required 1 Yulang.CommonSourceOptionalX22.subject)
  [(0, Yulang.CommonSyntax.Layer.base Yulang.Inference.Base.int)]
Yulang.CommonSourceOptionalX22.nested_source_generated : Yulang.Core.PresenceGeneration.Formula.Holds
  Yulang.Common.model
  (fun x =>
    Yulang.Core.PresenceGeneration.Comp.pure Yulang.Common.model
      (Yulang.Common.required 1 Yulang.CommonSourceOptionalX22.subject))
  (Yulang.CommonSourcePatternElaboration.generateSourcePattern [] [] [] Yulang.CommonSourceOptionalX22.nestedPattern
    (Yulang.Core.PresenceGeneration.TyTerm.var 0))
Yulang.CommonSourceOptionalX22.x22_proved : Yulang.Core.PresenceGeneration.Formula.Holds Yulang.Common.model
    Yulang.CommonSourceOptionalX22.assignment
    (Yulang.CommonSourceArmsSolved.principal [] Yulang.CommonSourceOptionalX22.arms) ∧
  (Yulang.ScopedCaseDataProgram.eval Empty.elim [] Yulang.CommonSourceOptionalX22.absentProgram).result =
      Except.ok (some (Yulang.CaseValues.Value.literal Empty (Yulang.LiteralValues.Literal.int Empty 80))) ∧
    ∀ (port : Int),
      (Yulang.ScopedCaseDataProgram.eval Empty.elim [] (Yulang.CommonSourceOptionalX22.presentProgram port)).result =
        Except.ok (some (Yulang.CaseValues.Value.literal Empty (Yulang.LiteralValues.Literal.int Empty port)))
@Yulang.CommonSourcePatternAllocation.constraints_exact : ∀ {α : Type}
  (pattern : Yulang.CasePatterns.Pattern Empty Yulang.Inference.Expr)
  (ρ : α → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model)
  (symbolic : Yulang.Core.PresenceGeneration.SchemeEnv α)
  (semantic : List (Yulang.Core.PresenceGeneration.Binding Yulang.Common.model)),
  Yulang.Core.PresenceGeneration.EnvRel Yulang.Common.model ρ symbolic semantic →
    ∀ (priorBindings : Yulang.CommonPatternEnvironment.NamedTerms α) (input : Yulang.Core.PresenceGeneration.TyTerm α)
      (values : Fin pattern.names.length → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model),
      Yulang.Core.PresenceGeneration.Formula.Holds Yulang.Common.model
          (Yulang.CommonPatternAllocation.assignment ρ values)
          (Yulang.CommonSourcePatternAllocation.constraints pattern symbolic priorBindings input) ↔
        Yulang.CommonSourcePatternTyping.RawTyping (Yulang.CommonPatternGeneration.DefaultTyping semantic)
          (Yulang.CommonPatternEnvironment.evalTypes ρ priorBindings) pattern
          (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model ρ input)
          (Yulang.CommonPatternAllocation.bindingValues pattern.names values)
@Yulang.CommonSourcePatternAllocation.generateAllocatedPattern_exact : ∀ {α : Type}
  (pattern : Yulang.CasePatterns.Pattern Empty Yulang.Inference.Expr)
  (ρ : α → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model)
  (symbolic : Yulang.Core.PresenceGeneration.SchemeEnv α)
  (semantic : List (Yulang.Core.PresenceGeneration.Binding Yulang.Common.model)),
  Yulang.Core.PresenceGeneration.EnvRel Yulang.Common.model ρ symbolic semantic →
    ∀ (priorBindings : Yulang.CommonPatternEnvironment.NamedTerms α) (input : Yulang.Core.PresenceGeneration.TyTerm α),
      Yulang.Core.PresenceGeneration.Formula.Holds Yulang.Common.model ρ
          (Yulang.CommonSourcePatternAllocation.generateAllocatedPattern pattern symbolic priorBindings input) ↔
        ∃ bindings,
          Yulang.CommonSourcePatternTyping.RawTyping (Yulang.CommonPatternGeneration.DefaultTyping semantic)
            (Yulang.CommonPatternEnvironment.evalTypes ρ priorBindings) pattern
            (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model ρ input) bindings
@Yulang.CommonSourcePatternAllocation.allocated_bindings_exact : ∀ {α : Type}
  (pattern : Yulang.CasePatterns.Pattern Empty Yulang.Inference.Expr)
  (ρ : α → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model)
  (symbolic : Yulang.Core.PresenceGeneration.SchemeEnv α)
  (semantic : List (Yulang.Core.PresenceGeneration.Binding Yulang.Common.model)),
  Yulang.Core.PresenceGeneration.EnvRel Yulang.Common.model ρ symbolic semantic →
    ∀ (priorBindings : Yulang.CommonPatternEnvironment.NamedTerms α) (input : Yulang.Core.PresenceGeneration.TyTerm α)
      (bindings : Yulang.CommonPatternEnvironment.NamedTypes),
      (∃ values,
          Yulang.Core.PresenceGeneration.Formula.Holds Yulang.Common.model
              (Yulang.CommonPatternAllocation.assignment ρ values)
              (Yulang.CommonSourcePatternAllocation.constraints pattern symbolic priorBindings input) ∧
            Yulang.CommonPatternAllocation.bindingValues pattern.names values = bindings) ↔
        Yulang.CommonSourcePatternTyping.RawTyping (Yulang.CommonPatternGeneration.DefaultTyping semantic)
          (Yulang.CommonPatternEnvironment.evalTypes ρ priorBindings) pattern
          (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model ρ input) bindings
@Yulang.CommonSourcePatternAllocation.withPattern_exact : ∀ {α : Type}
  (pattern : Yulang.CasePatterns.Pattern Empty Yulang.Inference.Expr)
  (ρ : α → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model)
  (symbolic : Yulang.Core.PresenceGeneration.SchemeEnv α)
  (semantic : List (Yulang.Core.PresenceGeneration.Binding Yulang.Common.model)),
  Yulang.Core.PresenceGeneration.EnvRel Yulang.Common.model ρ symbolic semantic →
    ∀ (priorBindings : Yulang.CommonPatternEnvironment.NamedTerms α) (input : Yulang.Core.PresenceGeneration.TyTerm α)
      (consumer : Yulang.Core.PresenceGeneration.Formula (Yulang.CommonPatternAllocation.Slots α pattern.names.length)),
      Yulang.Core.PresenceGeneration.Formula.Holds Yulang.Common.model ρ
          (Yulang.CommonSourcePatternAllocation.withPattern pattern symbolic priorBindings input consumer) ↔
        ∃ values,
          Yulang.CommonSourcePatternTyping.RawTyping (Yulang.CommonPatternGeneration.DefaultTyping semantic)
              (Yulang.CommonPatternEnvironment.evalTypes ρ priorBindings) pattern
              (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model ρ input)
              (Yulang.CommonPatternAllocation.bindingValues pattern.names values) ∧
            Yulang.Core.PresenceGeneration.Formula.Holds Yulang.Common.model
              (Yulang.CommonPatternAllocation.assignment ρ values) consumer
@Yulang.CommonSourcePatternAllocation.generateCheckedPattern_exact : ∀ {α : Type}
  (pattern : Yulang.CasePatterns.Pattern Empty Yulang.Inference.Expr)
  (ρ : α → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model)
  (symbolic : Yulang.Core.PresenceGeneration.SchemeEnv α)
  (semantic : List (Yulang.Core.PresenceGeneration.Binding Yulang.Common.model)),
  Yulang.Core.PresenceGeneration.EnvRel Yulang.Common.model ρ symbolic semantic →
    ∀ (priorBindings : Yulang.CommonPatternEnvironment.NamedTerms α) (input : Yulang.Core.PresenceGeneration.TyTerm α),
      Yulang.Core.PresenceGeneration.Formula.Holds Yulang.Common.model ρ
          (Yulang.CommonSourcePatternAllocation.generateCheckedPattern pattern symbolic priorBindings input) ↔
        ∃ bindings,
          Yulang.CommonSourcePatternTyping.Typing (Yulang.CommonPatternGeneration.DefaultTyping semantic)
            (Yulang.CommonPatternEnvironment.evalTypes ρ priorBindings) pattern
            (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model ρ input) bindings
Yulang.CommonSourcePatternAllocation.Examples.reversed_or_typable : Yulang.CommonSourcePatternTyping.Typing
  (Yulang.CommonPatternGeneration.DefaultTyping []) [] Yulang.CommonSourcePatternAllocation.Examples.reversedOr
  (Yulang.Common.pair (Yulang.CommonSyntax.Layer.base Yulang.Inference.Base.int)
    (Yulang.CommonSyntax.Layer.base Yulang.Inference.Base.int))
  [(0, Yulang.CommonSyntax.Layer.base Yulang.Inference.Base.int),
    (1, Yulang.CommonSyntax.Layer.base Yulang.Inference.Base.int)]
Yulang.CommonSourcePatternAllocation.Examples.reversed_or_generated : Yulang.Core.PresenceGeneration.Formula.Holds
  Yulang.Common.model Empty.elim
  (Yulang.CommonSourcePatternAllocation.generateCheckedPattern Yulang.CommonSourcePatternAllocation.Examples.reversedOr
    [] []
    ((Yulang.Core.PresenceGeneration.TyTerm.base Yulang.Inference.Base.int).pair
      (Yulang.Core.PresenceGeneration.TyTerm.base Yulang.Inference.Base.int)))
@Yulang.CommonSourcePatternElaboration.preserved : ∀
  {environment : List (Yulang.Core.CommonSyntax.Binding Yulang.Common.model)}
  {outer : List (Yulang.Core.PresenceGeneration.Binding Yulang.Common.model)} {outerNames : List Nat}
  {types : Yulang.CommonPatternEnvironment.NamedTypes}
  {pattern : Yulang.CasePatterns.Pattern Empty (Yulang.CaseDataTerms.Expr Empty)} {input : Yulang.Common.Ty}
  {bindings : Yulang.CommonPatternEnvironment.NamedTypes},
  Yulang.Core.CommonSyntax.EnvRel Yulang.Common.model environment outer →
    Yulang.CommonSourcePatternTyping.RawTyping
        (Yulang.CommonPatternSourceElaboration.DefaultTyped outerNames environment) types pattern input bindings →
      Yulang.CommonPatternSourceElaboration.covered (List.map Prod.fst types ++ outerNames) pattern = true ∧
        Yulang.CommonSourcePatternTyping.RawTyping (Yulang.CommonPatternGeneration.DefaultTyping outer) types
          (Yulang.CommonPatternSourceElaboration.elaborate (List.map Prod.fst types ++ outerNames) pattern) input
          bindings
@Yulang.CommonSourcePatternElaboration.reflected : ∀
  {environment : List (Yulang.Core.CommonSyntax.Binding Yulang.Common.model)}
  {outer : List (Yulang.Core.PresenceGeneration.Binding Yulang.Common.model)}
  {types : Yulang.CommonPatternEnvironment.NamedTypes}
  {pattern : Yulang.CasePatterns.Pattern Empty Yulang.Inference.Expr} {input : Yulang.Common.Ty}
  {bindings : Yulang.CommonPatternEnvironment.NamedTypes} {outerNames : List Nat},
  Yulang.Core.CommonSyntax.EnvRel Yulang.Common.model environment outer →
    Yulang.CommonSourcePatternTyping.RawTyping (Yulang.CommonPatternGeneration.DefaultTyping outer) types pattern input
        bindings →
      ∀ (source : Yulang.CasePatterns.Pattern Empty (Yulang.CaseDataTerms.Expr Empty)),
        Yulang.CommonPatternSourceElaboration.covered (List.map Prod.fst types ++ outerNames) source = true →
          Yulang.CommonPatternSourceElaboration.elaborate (List.map Prod.fst types ++ outerNames) source = pattern →
            Yulang.CommonSourcePatternTyping.RawTyping
              (Yulang.CommonPatternSourceElaboration.DefaultTyped outerNames environment) types source input bindings
@Yulang.CommonSourcePatternElaboration.raw_typing_exact : ∀
  {environment : List (Yulang.Core.CommonSyntax.Binding Yulang.Common.model)}
  {outer : List (Yulang.Core.PresenceGeneration.Binding Yulang.Common.model)} {outerNames : List Nat},
  Yulang.Core.CommonSyntax.EnvRel Yulang.Common.model environment outer →
    ∀ (pattern : Yulang.CasePatterns.Pattern Empty (Yulang.CaseDataTerms.Expr Empty))
      (types : Yulang.CommonPatternEnvironment.NamedTypes) (input : Yulang.Common.Ty)
      (bindings : Yulang.CommonPatternEnvironment.NamedTypes),
      Yulang.CommonSourcePatternTyping.RawTyping
          (Yulang.CommonPatternSourceElaboration.DefaultTyped outerNames environment) types pattern input bindings ↔
        Yulang.CommonPatternSourceElaboration.covered (List.map Prod.fst types ++ outerNames) pattern = true ∧
          Yulang.CommonSourcePatternTyping.RawTyping (Yulang.CommonPatternGeneration.DefaultTyping outer) types
            (Yulang.CommonPatternSourceElaboration.elaborate (List.map Prod.fst types ++ outerNames) pattern) input
            bindings
@Yulang.CommonSourcePatternElaboration.source_typing_exact : ∀
  {environment : List (Yulang.Core.CommonSyntax.Binding Yulang.Common.model)}
  {outer : List (Yulang.Core.PresenceGeneration.Binding Yulang.Common.model)} {outerNames : List Nat},
  Yulang.Core.CommonSyntax.EnvRel Yulang.Common.model environment outer →
    ∀ (pattern : Yulang.CasePatterns.Pattern Empty (Yulang.CaseDataTerms.Expr Empty))
      (types : Yulang.CommonPatternEnvironment.NamedTypes) (input : Yulang.Common.Ty)
      (bindings : Yulang.CommonPatternEnvironment.NamedTypes),
      Yulang.CommonSourcePatternTyping.Typing
          (Yulang.CommonPatternSourceElaboration.DefaultTyped outerNames environment) types pattern input bindings ↔
        Yulang.CommonPatternSourceElaboration.covered (List.map Prod.fst types ++ outerNames) pattern = true ∧
          Yulang.CommonSourcePatternTyping.Typing (Yulang.CommonPatternGeneration.DefaultTyping outer) types
            (Yulang.CommonPatternSourceElaboration.elaborate (List.map Prod.fst types ++ outerNames) pattern) input
            bindings
@Yulang.CommonSourcePatternElaboration.generateSourcePattern_exact : ∀ {α : Type}
  (pattern : Yulang.CasePatterns.Pattern Empty (Yulang.CaseDataTerms.Expr Empty)) (outerNames : List Nat)
  (assignment : α → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model)
  (symbolic : Yulang.Core.PresenceGeneration.SchemeEnv α)
  (environment : List (Yulang.Core.CommonSyntax.Binding Yulang.Common.model))
  (semantic : List (Yulang.Core.PresenceGeneration.Binding Yulang.Common.model)),
  Yulang.Core.CommonSyntax.EnvRel Yulang.Common.model environment semantic →
    Yulang.Core.PresenceGeneration.EnvRel Yulang.Common.model assignment symbolic semantic →
      ∀ (priorBindings : Yulang.CommonPatternEnvironment.NamedTerms α)
        (input : Yulang.Core.PresenceGeneration.TyTerm α),
        Yulang.Core.PresenceGeneration.Formula.Holds Yulang.Common.model assignment
            (Yulang.CommonSourcePatternElaboration.generateSourcePattern outerNames symbolic priorBindings pattern
              input) ↔
          ∃ bindings,
            Yulang.CommonSourcePatternTyping.Typing
              (Yulang.CommonPatternSourceElaboration.DefaultTyped outerNames environment)
              (Yulang.CommonPatternEnvironment.evalTypes assignment priorBindings) pattern
              (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model assignment input) bindings
@Yulang.CommonSourcePatternGeneration.evalTypes_reorder : ∀ {α : Type}
  (ρ : α → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model) (names : List Nat)
  (bindings : Yulang.CommonPatternEnvironment.NamedTerms α),
  Yulang.CommonPatternEnvironment.evalTypes ρ (Yulang.CommonPatternBindingAlignment.reorder names bindings) =
    Yulang.CommonPatternBindingAlignment.reorder names (Yulang.CommonPatternEnvironment.evalTypes ρ bindings)
@Yulang.CommonSourcePatternGeneration.nilBindings_exact : ∀ {α : Type}
  (bindings : Yulang.CommonPatternEnvironment.NamedTerms α) (formula : Yulang.Core.PresenceGeneration.Formula α)
  (ρ : α → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model),
  Yulang.Core.PresenceGeneration.Formula.Holds Yulang.Common.model ρ
      (Yulang.CommonPatternGeneration.nilBindings bindings formula) ↔
    Yulang.CommonPatternEnvironment.evalTypes ρ bindings = [] ∧
      Yulang.Core.PresenceGeneration.Formula.Holds Yulang.Common.model ρ formula
@Yulang.CommonSourcePatternGeneration.generatePattern_exact : ∀ {α : Type}
  (pattern : Yulang.CasePatterns.Pattern Empty Yulang.Inference.Expr)
  (ρ : α → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model)
  (symbolic : Yulang.Core.PresenceGeneration.SchemeEnv α)
  (semantic : List (Yulang.Core.PresenceGeneration.Binding Yulang.Common.model)),
  Yulang.Core.PresenceGeneration.EnvRel Yulang.Common.model ρ symbolic semantic →
    ∀ (priorBindings : Yulang.CommonPatternEnvironment.NamedTerms α) (input : Yulang.Core.PresenceGeneration.TyTerm α)
      (bindings : Yulang.CommonPatternEnvironment.NamedTerms α),
      Yulang.Core.PresenceGeneration.Formula.Holds Yulang.Common.model ρ
          (Yulang.CommonSourcePatternGeneration.generatePattern pattern symbolic priorBindings input bindings) ↔
        Yulang.CommonSourcePatternTyping.RawTyping (Yulang.CommonPatternGeneration.DefaultTyping semantic)
          (Yulang.CommonPatternEnvironment.evalTypes ρ priorBindings) pattern
          (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model ρ input)
          (Yulang.CommonPatternEnvironment.evalTypes ρ bindings)
@Yulang.CommonSourcePatternGenerationProvenance.bindings_reorder : ∀ {α : Type}
  {bindings : Yulang.CommonPatternEnvironment.NamedTerms α},
  Yulang.CommonPatternGenerationProvenance.GoodBindings bindings →
    ∀ (names : List Nat),
      Yulang.CommonPatternGenerationProvenance.GoodBindings
        (Yulang.CommonPatternBindingAlignment.reorder names bindings)
@Yulang.CommonSourcePatternGenerationProvenance.safe_generatePattern : ∀ {α : Type}
  (pattern : Yulang.CasePatterns.Pattern Empty Yulang.Inference.Expr)
  (environment : Yulang.Core.PresenceGeneration.SchemeEnv α),
  Yulang.CommonPatternGenerationProvenance.SafeEnvironment environment →
    ∀ (priorBindings : Yulang.CommonPatternEnvironment.NamedTerms α),
      Yulang.CommonPatternGenerationProvenance.GoodBindings priorBindings →
        ∀ (input : Yulang.Core.PresenceGeneration.TyTerm α),
          Yulang.CommonPatternGenerationProvenance.Input input →
            ∀ (bindings : Yulang.CommonPatternEnvironment.NamedTerms α),
              Yulang.CommonPatternGenerationProvenance.GoodBindings bindings →
                Yulang.CommonPatternGenerationProvenance.SafeFormula
                  (Yulang.CommonSourcePatternGeneration.generatePattern pattern environment priorBindings input
                    bindings)
@Yulang.CommonSourcePatternGenerationProvenance.bindingSlots_good : ∀ {α : Type} (names : List Nat),
  Yulang.CommonPatternGenerationProvenance.GoodBindings (Yulang.CommonPatternAllocation.bindingSlots names)
@Yulang.CommonSourcePatternGenerationProvenance.safe_close : ∀ {α : Type} (n : Nat)
  (formula : Yulang.Core.PresenceGeneration.Formula (Yulang.CommonPatternAllocation.Slots α n)),
  Yulang.CommonPatternGenerationProvenance.SafeFormula formula →
    Yulang.CommonPatternGenerationProvenance.SafeFormula (Yulang.CommonPatternAllocation.close n formula)
@Yulang.CommonSourcePatternGenerationProvenance.safe_constraints : ∀ {α : Type}
  (pattern : Yulang.CasePatterns.Pattern Empty Yulang.Inference.Expr)
  (environment : Yulang.Core.PresenceGeneration.SchemeEnv α),
  Yulang.CommonPatternGenerationProvenance.SafeEnvironment environment →
    ∀ (priorBindings : Yulang.CommonPatternEnvironment.NamedTerms α),
      Yulang.CommonPatternGenerationProvenance.GoodBindings priorBindings →
        ∀ (input : Yulang.Core.PresenceGeneration.TyTerm α),
          Yulang.CommonPatternGenerationProvenance.Input input →
            Yulang.CommonPatternGenerationProvenance.SafeFormula
              (Yulang.CommonSourcePatternAllocation.constraints pattern environment priorBindings input)
@Yulang.CommonSourcePatternGenerationProvenance.safe_allocated : ∀ {α : Type}
  (pattern : Yulang.CasePatterns.Pattern Empty Yulang.Inference.Expr)
  (environment : Yulang.Core.PresenceGeneration.SchemeEnv α),
  Yulang.CommonPatternGenerationProvenance.SafeEnvironment environment →
    ∀ (priorBindings : Yulang.CommonPatternEnvironment.NamedTerms α),
      Yulang.CommonPatternGenerationProvenance.GoodBindings priorBindings →
        ∀ (input : Yulang.Core.PresenceGeneration.TyTerm α),
          Yulang.CommonPatternGenerationProvenance.Input input →
            Yulang.CommonPatternGenerationProvenance.SafeFormula
              (Yulang.CommonSourcePatternAllocation.generateAllocatedPattern pattern environment priorBindings input)
Yulang.CommonSourcePatternGenerationProvenance.principal_safe : ∀
  (pattern : Yulang.CasePatterns.Pattern Empty Yulang.Inference.Expr),
  Yulang.CommonPatternGenerationProvenance.SafeFormula
    (Yulang.CommonSourcePatternGenerationProvenance.principalPattern pattern)
Yulang.CommonSourcePatternGenerationProvenance.generated_invariants : ∀
  (pattern : Yulang.CasePatterns.Pattern Empty Yulang.Inference.Expr)
  (clause : Yulang.PresenceNormalForm.Clause (Option Empty)),
  clause ∈
      Yulang.PresenceNormalForm.normalise (Yulang.CommonSourcePatternGenerationProvenance.principalPattern pattern) →
    Yulang.CommonPatternConstraintGrammar.GoodAtoms clause.pack ∧
      Yulang.PresenceSourceConstraintSupport.GoodAtoms clause.pack ∧
        Yulang.PresenceGeneratedWidth.WidthAtoms clause.pack
@Yulang.CommonSourcePatternInversion.Root.typing : ∀ {Default : Type}
  {defaults : Yulang.CommonPatternEnvironment.NamedTypes → Default → Yulang.Common.Ty → Prop}
  {types : Yulang.CommonPatternEnvironment.NamedTypes} {pattern : Yulang.CasePatterns.Pattern Empty Default}
  {input : Yulang.Common.Ty} {bindings : Yulang.CommonPatternEnvironment.NamedTypes},
  Yulang.CommonSourcePatternInversion.Root defaults types pattern input bindings →
    Yulang.CommonSourcePatternTyping.RawTyping defaults types pattern input bindings
@Yulang.CommonSourcePatternInversion.typing_root_exact : ∀ {D : Type}
  (defaults : Yulang.CommonPatternEnvironment.NamedTypes → D → Yulang.Common.Ty → Prop)
  (types : Yulang.CommonPatternEnvironment.NamedTypes) (pattern : Yulang.CasePatterns.Pattern Empty D)
  (input : Yulang.Common.Ty) (bindings : Yulang.CommonPatternEnvironment.NamedTypes),
  Yulang.CommonSourcePatternTyping.RawTyping defaults types pattern input bindings ↔
    ∃ original,
      Yulang.Common.Subtype input original ∧
        Yulang.CommonSourcePatternInversion.Root defaults types pattern original bindings
@Yulang.CommonSourcePatternInversion.wildcard_iff : ∀ {D : Type}
  {defaults : Yulang.CommonPatternEnvironment.NamedTypes → D → Yulang.Common.Ty → Prop}
  {types bindings : Yulang.CommonPatternEnvironment.NamedTypes} {input : Yulang.Common.Ty},
  Yulang.CommonSourcePatternTyping.RawTyping defaults types Yulang.CasePatterns.Pattern.wildcard input bindings ↔
    bindings = []
@Yulang.CommonSourcePatternInversion.bind_iff : ∀ {D : Type}
  {defaults : Yulang.CommonPatternEnvironment.NamedTypes → D → Yulang.Common.Ty → Prop}
  {types bindings : Yulang.CommonPatternEnvironment.NamedTypes} {input : Yulang.Common.Ty} {name : Nat},
  Yulang.CommonSourcePatternTyping.RawTyping defaults types (Yulang.CasePatterns.Pattern.bind name) input bindings ↔
    ∃ result, bindings = [(name, result)] ∧ Yulang.Common.Subtype input result
@Yulang.CommonSourcePatternInversion.literal_iff : ∀ {D : Type}
  {defaults : Yulang.CommonPatternEnvironment.NamedTypes → D → Yulang.Common.Ty → Prop}
  {types bindings : Yulang.CommonPatternEnvironment.NamedTypes} {input : Yulang.Common.Ty}
  {expected : Yulang.LiteralValues.Literal},
  Yulang.CommonSourcePatternTyping.RawTyping defaults types (Yulang.CasePatterns.Pattern.literal expected) input
      bindings ↔
    bindings = [] ∧
      Yulang.Common.Subtype input (Yulang.CommonSyntax.Layer.base (Yulang.Core.CommonData.literalBase expected))
@Yulang.CommonSourcePatternInversion.range_iff : ∀ {D : Type}
  {defaults : Yulang.CommonPatternEnvironment.NamedTypes → D → Yulang.Common.Ty → Prop}
  {types bindings : Yulang.CommonPatternEnvironment.NamedTypes} {input : Yulang.Common.Ty} {lower upper : Option Int},
  Yulang.CommonSourcePatternTyping.RawTyping defaults types (Yulang.CasePatterns.Pattern.intRange lower upper) input
      bindings ↔
    bindings = [] ∧
      Yulang.Common.Subtype input (Yulang.CommonSyntax.Layer.base Yulang.Inference.Base.int) ∧
        (lower.isSome = true ∨ upper.isSome = true)
@Yulang.CommonSourcePatternInversion.pair_iff : ∀ {D : Type}
  {defaults : Yulang.CommonPatternEnvironment.NamedTypes → D → Yulang.Common.Ty → Prop}
  {types bindings : Yulang.CommonPatternEnvironment.NamedTypes} {input : Yulang.Common.Ty}
  {p q : Yulang.CasePatterns.Pattern Empty D},
  Yulang.CommonSourcePatternTyping.RawTyping defaults types (p.pair q) input bindings ↔
    ∃ a b left right,
      bindings = left ++ right ∧
        Yulang.Common.Subtype input (Yulang.Common.pair a b) ∧
          Yulang.CommonSourcePatternTyping.RawTyping defaults types p a left ∧
            Yulang.CommonSourcePatternTyping.RawTyping defaults (left ++ types) q b right
@Yulang.CommonSourcePatternInversion.recordEnd_iff : ∀ {D : Type}
  {defaults : Yulang.CommonPatternEnvironment.NamedTypes → D → Yulang.Common.Ty → Prop}
  {types bindings : Yulang.CommonPatternEnvironment.NamedTypes} {input : Yulang.Common.Ty},
  Yulang.CommonSourcePatternTyping.RawTyping defaults types Yulang.CasePatterns.Pattern.recordEnd input bindings ↔
    bindings = [] ∧ Yulang.Common.Subtype input Yulang.Common.emptyRecord
@Yulang.CommonSourcePatternInversion.field_iff : ∀ {D : Type}
  {defaults : Yulang.CommonPatternEnvironment.NamedTypes → D → Yulang.Common.Ty → Prop}
  {types bindings : Yulang.CommonPatternEnvironment.NamedTypes} {input : Yulang.Common.Ty} {name : Nat}
  {p rest : Yulang.CasePatterns.Pattern Empty D},
  Yulang.CommonSourcePatternTyping.RawTyping defaults types (Yulang.CasePatterns.Pattern.field name p rest) input
      bindings ↔
    ∃ original payload left right,
      bindings = left ++ right ∧
        Yulang.Common.Subtype input original ∧
          Yulang.CommonDefaultRequired.OptionalPayload name original payload ∧
            Yulang.CommonSourcePatternTyping.RawTyping defaults types p payload left ∧
              Yulang.CommonSourcePatternTyping.RawTyping defaults (left ++ types) rest original right
@Yulang.CommonSourcePatternInversion.defaultField_iff : ∀ {D : Type}
  {defaults : Yulang.CommonPatternEnvironment.NamedTypes → D → Yulang.Common.Ty → Prop}
  {types bindings : Yulang.CommonPatternEnvironment.NamedTypes} {input : Yulang.Common.Ty} {name : Nat} {fallback : D}
  {p rest : Yulang.CasePatterns.Pattern Empty D},
  Yulang.CommonSourcePatternTyping.RawTyping defaults types
      (Yulang.CasePatterns.Pattern.defaultField name fallback p rest) input bindings ↔
    ∃ original payload fallbackType left right,
      bindings = left ++ right ∧
        Yulang.Common.Subtype input original ∧
          Yulang.CommonDefaultRequired.OptionalPayload name original payload ∧
            defaults types fallback fallbackType ∧
              Yulang.CommonSourcePatternTyping.RawTyping defaults types p
                  (Yulang.CommonSyntax.Layer.union payload fallbackType) left ∧
                Yulang.CommonSourcePatternTyping.RawTyping defaults (left ++ types) rest original right
@Yulang.CommonSourcePatternInversion.variant_iff : ∀ {D : Type}
  {defaults : Yulang.CommonPatternEnvironment.NamedTypes → D → Yulang.Common.Ty → Prop}
  {types bindings : Yulang.CommonPatternEnvironment.NamedTypes} {input : Yulang.Common.Ty} {tag : Nat}
  {p : Yulang.CasePatterns.Pattern Empty D},
  Yulang.CommonSourcePatternTyping.RawTyping defaults types (Yulang.CasePatterns.Pattern.variant tag p) input bindings ↔
    ∃ payload,
      Yulang.Common.Subtype input (Yulang.Common.variant tag payload) ∧
        Yulang.CommonSourcePatternTyping.RawTyping defaults types p payload bindings
@Yulang.CommonSourcePatternInversion.or_iff : ∀ {D : Type}
  {defaults : Yulang.CommonPatternEnvironment.NamedTypes → D → Yulang.Common.Ty → Prop}
  {types bindings : Yulang.CommonPatternEnvironment.NamedTypes} {input : Yulang.Common.Ty}
  {p q : Yulang.CasePatterns.Pattern Empty D},
  Yulang.CommonSourcePatternTyping.RawTyping defaults types (p.or q) input bindings ↔
    Yulang.CommonSourcePatternTyping.RawTyping defaults types p input bindings ∧
      Yulang.CommonSourcePatternTyping.RawTyping defaults types q input
        (Yulang.CommonPatternBindingAlignment.reorder q.names bindings)
@Yulang.CommonSourcePatternInversion.as_iff : ∀ {D : Type}
  {defaults : Yulang.CommonPatternEnvironment.NamedTypes → D → Yulang.Common.Ty → Prop}
  {types bindings : Yulang.CommonPatternEnvironment.NamedTypes} {input : Yulang.Common.Ty}
  {p : Yulang.CasePatterns.Pattern Empty D} {name : Nat},
  Yulang.CommonSourcePatternTyping.RawTyping defaults types (p.as name) input bindings ↔
    ∃ original rest,
      bindings = (name, original) :: rest ∧
        Yulang.Common.Subtype input original ∧ Yulang.CommonSourcePatternTyping.RawTyping defaults types p original rest
Yulang.CommonSourcePatternPartialSafety.bindingTypes_reorder : ∀ (names : List Nat)
  (bindings : Yulang.CommonPatternEnvironment.NamedTypes),
  Yulang.CommonPatternTyping.bindingTypes (Yulang.CommonPatternBindingAlignment.reorder names bindings) =
    Yulang.CommonPatternBindingAlignment.reorder names (Yulang.CommonPatternTyping.bindingTypes bindings)
@Yulang.CommonSourcePatternPartialSafety.partial_alignResult : ∀ {E R : Type}
  {types : Yulang.CommonPatternEnvironment.NamedTypes} (names : List Nat)
  (observed : Yulang.CasePatterns.Observation Empty E R),
  Yulang.CommonPatternPartialSafety.PartialHolds types observed.result →
    Yulang.CommonPatternPartialSafety.PartialHolds (Yulang.CommonPatternBindingAlignment.reorder names types)
      (Yulang.CommonPatternAlignedObservations.alignResult names observed).result
@Yulang.CommonSourcePatternPartialSafety.typing_matches_partial : ∀ {D E R : Type}
  {DefaultTyped : Yulang.CommonPatternEnvironment.NamedTypes → D → Yulang.Common.Ty → Prop}
  {types : Yulang.CommonPatternEnvironment.NamedTypes} {pattern : Yulang.CasePatterns.Pattern Empty D}
  {input : Yulang.Common.Ty} {bindings : Yulang.CommonPatternEnvironment.NamedTypes} (floatCheck : Empty → Empty → Bool)
  (defaultEval : Yulang.CaseValues.Bindings → D → Yulang.EvaluationTrace.Logged E R Yulang.Core.CommonData.Value),
  Yulang.CommonPatternPartialSafety.DefaultPartialSound DefaultTyped defaultEval →
    Yulang.CommonSourcePatternTyping.RawTyping DefaultTyped types pattern input bindings →
      Yulang.PatternBindingChecks.NamesValid pattern →
        ∀ (environment : Yulang.CaseValues.Bindings),
          Yulang.CaseValues.BindingsHold (Yulang.CommonPatternTyping.bindingTypes types) environment →
            ∀ (value : Yulang.CaseValues.Value),
              Yulang.CommonPatternTyping.valueAt input value →
                Yulang.CommonPatternPartialSafety.PartialHolds bindings
                  (Yulang.CommonPatternAlignedMatcher.run floatCheck defaultEval environment pattern value).result
@Yulang.CommonSourcePatternTyping.RawTyping.binding_names : ∀ {Default : Type}
  {DefaultTyped : Yulang.CommonPatternEnvironment.NamedTypes → Default → Yulang.Common.Ty → Prop}
  {types : Yulang.CommonPatternEnvironment.NamedTypes} {pattern : Yulang.CasePatterns.Pattern Empty Default}
  {input : Yulang.Common.Ty} {bindings : Yulang.CommonPatternEnvironment.NamedTypes},
  Yulang.CommonSourcePatternTyping.RawTyping DefaultTyped types pattern input bindings →
    pattern.names = List.map Prod.fst bindings
@Yulang.CommonSourcePatternTyping.required_optional : ∀ {input payload : Yulang.Common.Ty} {name : Nat},
  Yulang.Common.Subtype input (Yulang.Common.required name payload) →
    Yulang.CommonDefaultRequired.OptionalPayload name input payload
@Yulang.CommonSourcePatternTyping.legacy_preserved : ∀ {Default : Type}
  {defaults : Yulang.CommonPatternEnvironment.NamedTypes → Default → Yulang.Common.Ty → Prop}
  {types : Yulang.CommonPatternEnvironment.NamedTypes} {pattern : Yulang.CasePatterns.Pattern Empty Default}
  {input : Yulang.Common.Ty} {bindings : Yulang.CommonPatternEnvironment.NamedTypes},
  Yulang.CommonAlignedPatternTyping.RawTyping defaults types pattern input bindings →
    Yulang.CommonSourcePatternTyping.RawTyping defaults types pattern input bindings
```
