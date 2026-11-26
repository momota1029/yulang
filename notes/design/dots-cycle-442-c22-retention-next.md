# C22 — 本当に欠けている固定出力の保持

正本 `integration/m1-final@fbbf227b2023e0da5d18d8f5c3826545f6b79e28` と比較。規則は §6.1 L6–17・§6.3 L78–95（選択したとき固定の関連型変数に等式を加える）および §4.6 L221–235（nominal に row/value の別がある）。既存の直接 spec fixture は未確認。以下はその狭い組合せを元の typed B6 tree で検査するもので、入力・型判断の新しい言語上の判断を決めるものではない。

## 現在の exact cut

`replay442` は実 original candidate tape と K2、unfiltered registry ordinal、元の where-free・出力一個の要求と本文 lookup、B6 plan と lexical slot が一致するところまで。`Replay.readOwnRefOutput` はその同じ Event を元の row と value の binder/center と関連付ける。`actual_mixed_replay_with_retention_is_original_dictionary442` は、**同じ適合モデルで exact fixed target equality が別に成立するときだけ**、既存 `DictionaryEvidence.node` を作る。新規 Classifies、R22、public check case のいずれでもない。

`I72.State` は core (`current/ordinary/visible`、mode、origin、route) と B6 atlas のみ。`Checker408.Problem` は State と root のみ。 `FixedTargets` が必要とするのは「要求に既にある target の assignment が、元の evaluated RHS と同値」で、`Check408.encodedEventWrites` の exact typed write と出力先番号ではない。 `Current.ModelsCurrent` は typed `Seen`、`Fits` はさらに nativeSyntax を加えるが、両観測は target の assignment を固定しない。 `GeneralDeclarativeI65I72TypedTargetRows403.fixedValueCode403` は任意の元 RHS の row footprint を明示的に落とす。この旧形式を flatten して仮造しない。

## 他の実在する経路の調査

- `GeneralDeclarativeI65I74StructuralWhereOutputRead432`、`GeneralDeclarativeI65I74CompletedLowerRetained437` は exact listed `GeneralDeclarativeHead320.Equation` の Expr 代表を必要とする。関連式が row を含むと元 plan にその代表はない。 `GeneralDeclarativeI65I75ProjectedCoreRetention426` は ordinary `TyTerm.required` の actual field 行を双方向に読む個別経路で、mixed nominal の row projection ではない。
- `GeneralNominalState.nominals/Denotes/Models` は rowSource と value source を別に読み、**対象 slot の assignment を含む**本物の heterogeneous retention。 `ExistingMixedCompanion` の位置照合には target/source、rowSource、value/source、ctor 原名、kind 順序と実 slot 記録が必要。 `actual_mixed_replay_with_existing_typed_companion_is_dictionary442` で同一 assignment・同一原 Event に既存 dictionary を得る。別 graph Models を witness から主張するのではない。現行 `Fits` 全体からその graph Models を得ることは同一元 State の反例で否定される。占有行は元の B6 producer または完成/release の provenance を単独では与えない。
- `CommonNominalGuardedRowSolver.Problem.Models` も nominal 内に row を保持できるが、独立の有限 constructor graph と node/row assignments が対象。元の B6 occurrence・fixed output をここから readback する現 canonical bridge は確認できていない。 `GeneralMixedEqualityExact307` の raw merge は既に意味のある二 source の .1 同値を保持する。旧 alias の対称等式は exact mixed denotation の仲介にはできるが、それだけで混合値の原意味を構築しない。

## 次の差分（設計のみ）

第一案は I‑65 / R21 をそのままにして **C22 を保留**。次に運用側が許可するなら、元の B6 compiler が選択した出力から独立した canonical typed retained equation を実 State に保持する。そのレコードは **元の request occurrence、declaration ordinal、output ordinal、元 authored body ID、要求既出の fixed target、順序付き row/value capture origins** を確認し、data-only replay は一致しない行を受け取らない。原 typed point descriptor を再利用する場合、target と rowSource/value source の mapping ＋同じ State の全 Fits に対する semantic transport をこの canonical producer から導出する。別 graph を添付するだけ、registry mode や typed view をもう一度読むだけ、出力値を見て新しい target を決めるだけでは足りない。

旧データの観測や state の投影、旧 witness Bool は無変更に保つ。仮に mixed semantic facts を検査器の State に供給する追加経路が必要になっても、現行 `I72.Fits` の定義置換や証明済みの外形の無断変更は行わない。出力が保持されたことと、後の別需要がそれを完成済みの根拠にできることは別責務（I‑79）。追加 authority の要否は監督役の次指示に回す。言語上の受理・拒否の変更や一般完全性／停止性は今回の範囲外。
