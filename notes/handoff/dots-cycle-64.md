# Cycle64: actual where expansion preserves source models and endpoint origin

## Result and boundary

**部分目標は閉じた。** 任意有限の実 candidate capture から where 子を生成するとき、元の親 head を満たす一つの source valuation が、全ての元 where-template を、その実生成した両 endpoint の間で同時に満たすことを証明した。さらに、生成した子 endpoint の各名前は必ず元の親 endpoint に現れることを、モデルの存在を仮定せず証明した。

既存の実 `inspect`・`total`・`child`・`expand` を使う。複数の binder、pair/tick の capture、pair/tick/join を持つ子 template、正規化、重複する where と元の順序を含む一般定理。実行版は区間の中央の型を選ばない。有限な名前の検査から、total lookup の fallback が子で観測されないことを導く。前回の元宣言 head の意味から、今回は **実際に生成した全 where endpoint の意味と起源** まで進めた。

公開入口 `run_exact` は capture 成功やモデル整合性を外部前提にしない。実 inspector の return と生成 atoms の全モデル iff、独立 `Accepts` 境界・同じ出力・旧 source 需要と元 head と全 where-template を共有 valuation が満たすこと。`returned_sources` は実 return だけから全子 endpoint の元名前を保証するので、入力区間が矛盾しても成立する。

境界は明記する。これは child の型が生成区間に入ることの証明であり、その role の impl や辞書が存在することではない。associated child が新しい絞り込みを返す再帰解決・ordinary graph inspection による state-dependent materialization・source map の構築は未接続。source identity map と ambient endpoint slot map は引き続き明示入力。元 endpoint 名の provenance を証明しただけで、child の local binder と canonical source root の対応を構築したとは言わない。

`run` は一つの宣言の既存有限 inspector を呼ぶ局所 wrapper で、registry 全体の選択、Paterson validity 検査、再帰 driver ではない。head は既存の linear structural grammar のまま。repeated head binder と join head は outside、未束縛 where 名も outside。role mismatch の既存 no-candidate return を、言語全体の rejected と読み替えない。仕様上の新しい拒否範囲を決めず、既存定理も弱めていない。X13〜X16 の全外側入口、一般 `resolve_exact`、M1 三つ組は未達。

## Theorems and direction

新規 module `lean/Yulang/CommonRoleWhereSourceModels.lean`。17公開定理を Audit に登録し、Yulang から import した。以下の健全性・完全性は局所生成境界のもので、全M1の主型性ではない。

1. `form_mono`（補助・健全性）: 任意の有限 Form と2 valuation に対し、その Form に現れる全名前で前者 ≤ 後者なら、Form の解釈も前者 ≤ 後者。
2. `normalized_fits`（補助・健全性/完全性）: 任意の ambient valuation、元 endpoint 対、型について、正規化後の両 endpoint の間に入る iff 元の間に入る。
3. `normalized_heads`（補助・健全性/完全性）: 任意の ambient/local valuation、有限 head 列、元引数列について、正規化した引数の HeadFits iff 元の HeadFits。長さが不一致の場合も含む。
4. `lookup_member`（補助）: 任意の有限 bindings、名前、引数について、実 lookup が返した対は元の bindings の要素。
5. `instantiated_fits`（健全性）: 任意の ambient/local valuation、全 binding が適合する有限 table、有限 Form に対し、その Form の全使用名が lookup にあるなら、同じ local valuation の Form 解釈は実代入・正規化した両 endpoint の間に入る。
6. `instantiated_heads`（健全性）: 同じ任意の valuation/table と有限 Form 列について、全使用名が束縛されていれば、その実 instantiate の全引数が元 Form 列の解釈に適合する。
7. `accepted_where_fits`（健全性）: 任意の2 valuation、宣言、元 goal、bindings について、独立 Accepts と元親 HeadFits があれば、元の全 where-template が同じ valuation で実子 endpoint に適合する。子成功は前提でない。
8. `expanded_member_fits`（健全性・補助）: 同じ任意入力と任意の実 expand の要素について、それに対応する元 requirement が存在し、role が一致し、同じ valuation がその元 template を生成引数内で満たす。
9. `normalize_sources`（補助）: 任意の Form と名前について、正規化後に現れるなら元 Form に現れる。
10. `subst_sources`（補助）: 任意の Form、構文代入、結果に現れる名前について、元 Form に現れる binder が存在し、その代入像に結果の名前が現れる。
11. `capture_sources`（補助）: 任意の独立 Capture derivation、捕捉した binding、binding endpoint の名前について、その名前は元 argument のどちらかの endpoint に現れる。繰り返し binder の Capture も含む。
12. `capture_arguments_sources`（補助）: 任意の独立 CaptureArguments derivation、捕捉 binding と endpoint 名について、その名前は元引数列の endpoint に現れる。
13. `normalized_goal_sources`（補助）: 任意有限引数列と名前について、正規化後の endpoint に現れるなら元列の endpoint に現れる。
14. `accepted_child_sources`（補助・source provenance）: 任意の宣言、goal、bindings、独立 Accepts と元 requirement の要素について、実生成した子の全 endpoint 名は元親 endpoint 名に含まれる。モデル存在は不要。
15. `generated_models_exact`（局所健全性/完全性）: 任意の slot map、ambient assignment、旧 source 需要、宣言、goal、source map、bindings と独立 Accepts について、実増分生成 atoms の全成立 iff、一つの source valuation が旧需要・元親 head・全元 where-template を同時に満たす。where 条件で親モデルを失わない。
16. `run_exact`（局所健全性/完全性）: 任意の同入力と出力 Result について、実 return と出力 atoms の成立 iff、独立 Accepts の bindings と計算通りの同じ出力、旧需要・元 head・全 where の共有モデルが存在する。成功や意味的不変量を外部前提にしない。
17. `returned_sources`（補助・source provenance）: 任意の slot map、旧需要、宣言、goal、source map、Result について、実 positive return があれば、全出力 child の全 endpoint 名は元親 endpoint に現れる。モデル存在、child 成功、追加 allocator の前提なし。

## Verification

検証済み local source commit: `4972a2bdaf30021025f8838bc181c80e7e64d1cd`。source 公開後は exact SHA を merge し、6成果パスの公開との差分が空であることを再確認した。

1. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake build --wfail Yulang.CommonRoleWhereSourceModels` — exit 0。最終ソースのログ全文:

```text
✔ [168/168] Built Yulang.CommonRoleWhereSourceModels (583ms)
Build completed successfully (168 jobs).
```

2. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 /tmp/cycle64-audit.lean` — exit 0。17定理の公理監査と6実行回帰。全文:

```text
'Yulang.CommonRoleWhereSourceModels.form_mono' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleWhereSourceModels.normalized_fits' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleWhereSourceModels.normalized_heads' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleWhereSourceModels.lookup_member' depends on axioms: [propext]
'Yulang.CommonRoleWhereSourceModels.instantiated_fits' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleWhereSourceModels.instantiated_heads' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleWhereSourceModels.accepted_where_fits' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleWhereSourceModels.expanded_member_fits' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleWhereSourceModels.normalize_sources' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleWhereSourceModels.subst_sources' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleWhereSourceModels.capture_sources' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleWhereSourceModels.capture_arguments_sources' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleWhereSourceModels.normalized_goal_sources' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleWhereSourceModels.accepted_child_sources' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleWhereSourceModels.generated_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleWhereSourceModels.run_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleWhereSourceModels.returned_sources' depends on axioms: [propext, Quot.sound]
```

許容された propext / Classical.choice / Quot.sound のみ。Classical.choice は共有 valuation の数学的存在で、実行版が区間中心を選ぶものではない。

3. `bash tools/verify-lean.sh . origin/integration/m1-final --no-build` — exit 0。全文:

```text
verify-lean: . @ 4972a2bdaf (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

4. `git diff --check` — exit 0。

focused build は120秒の上限つき background process と親 shell wait で実行し、長い前景操作は行っていない。最初の実装では rewrite の透明性、normalize の型推論、同名パターン束縛による proof elaboration errors があった。明示的な式・補題適用・変数名を直し、定理の型を弱めずに最終版を再検証した。

**全体 lake build、全 Audit、広域 AxiomGate、全 verify はローカルで実行していない。** 上の PASS は diff checks only。exact 公開source のCIは後述。

### Reproducible executable regressions

上記 import と17本の `#print axioms` の後に以下を実行した。

```lean
open Yulang Yulang.CommonRoleWhereSourceModels
open Yulang.CommonRoleCaptureNormalization (Form)
open Yulang.CommonRoleStablePaterson (Declaration)
open Yulang.CommonRoleIntervalPaterson (Goal)

def declaration : Declaration := ⟨1, 0, [.pair (.var 0) (.tick (.var 1))],
  [(2, [.join (.var 0) (.var 0)]), (3, [.pair (.var 1) (.var 0)]),
   (2, [.join (.var 0) (.var 0)])]⟩
def goal : Goal := ⟨1, [(.pair (.var 7) (.tick .int), .pair (.var 8) (.tick .int))]⟩

-- Distinct binders, original endpoints, normalization, and duplicate child order.
example : (((run id [] declaration goal id).bind id).map (fun r => r.children)) = some
    [⟨2, [(.var 7, .var 8)]⟩, ⟨3, [(.pair .int (.var 7), .pair .int (.var 8))]⟩,
     ⟨2, [(.var 7, .var 8)]⟩] := rfl
-- Every endpoint dependency is computed from the actual original parent terms.
example : (((run id [] declaration goal id).bind id).map
    (fun r => r.children.flatMap (fun g => goalSources g.arguments))) =
    some [7,8,7,8,7,8] := rfl
-- An unbound where variable remains outside rather than invoking lookup fallback.
example : run id [] ({ declaration with requirements := [(2, [.var 99])] }) goal id = none := rfl
-- A role mismatch stays the existing definite no-candidate return.
example : (run id [] declaration { goal with role := 9 } id).map Option.isSome = some false := rfl
-- Repeated head variables remain outside the existing inspector grammar.
example : run id [] ⟨1,0,[.pair (.var 0) (.var 0)],[]⟩
    ⟨1,[(.pair .int .int,.pair .int .int)]⟩ id = none := rfl
-- Inconsistent endpoints still have a positive structural return, no false dictionary claim.
example : (run id [] ⟨1,0,[.var 0],[(2,[.var 0])]⟩
    ⟨1,[(.int,.pair .int .int)]⟩ id).map Option.isSome = some true := rfl
```

## Publication, preservation and recovery

最初に integration/m1-final を fetch し、standing orders と inbox をGitHubから再読。I-4 ACTIVE、上限なし、I-11 の25分上限を確認。開始時の integration と live work/dots-main はともに `503b0cf35ae23c440901384b521c0f50a8ea1dcb`。前回 cycle63 は completed と報告が揃い、残った作業場は clean だった。復旧対象なし。integration を取り込み済みと確認した。

開始心拍 `9ae12468105e34e28958ee17f5186c19741aa523` を公開後、exact SHA を fetch/merge。source は7変更パス（6成果+running心拍）を、GitHub AppのblobとSHA-only treeに準備し、一回のnon-force/expected-head ref更新で公開した。blob はローカルの hash と逐一一致確認した。大きな既存文書は exact remote base と今回の追記を結合し、既存内容を保存した。拒否や結果不明、応答停止は無かった。

検証済み source commit: `668ba0179d708c645899a08f4b10aa57320a9fa7`。
source tree: `c56736716da5782b4c90bb91c9a1fdec7ff9e0a7`。

公開後にlive headと完全recursive treeを取得。7変更blob の path/mode/hash 一致、対象外2155blob 保持、全2162blob、truncationなしを確認。ローカルにもexact source SHAをfetch/mergeし、6成果の差分ゼロを確認した。他ブランチには書き込んでいない。

本報告と completed 心拍は続けて公開し、最終treeも照合する。cycle全体の対象は8パス。最終SHA・照合は完了後に親へ伝え、この時点では先取りしない。

## Yulang2 comparison and remaining B4 bridges

実装前に work/dots-audit を fetch し、x-oracle の X13〜X16、C3-PARENT / C3-PARENT-NEG を読んだ。共有 source・where の由来を確かめる材料であり、任意有限の Lean 定理の実機証明としない。今回新しいYulang2実行はしていない。spec 6.3 の既存方向と既存 interval/capture 定義を保ち、新しい意味論の選択・質問ノートはない。

B4 に残る主要橋は **5本のまま**:
`source_boundary_adequate`、`generated_work_closed`、`saturate_terminates_and_closes`、`saturated_frontier_exact`、`resolve_dictionary_order_sound`。
今回閉じたのは最初の2橋の中の「実parent captureから全where子の共有モデルと元endpoint起源」部分。有限仕事領域への一般source登録全体を閉じたとは言わない。

次の候補:
1. 今回計算した endpoint の起源から、実 child occurrence の source identity map と canonical graph root を構成する。local binder の綴りによる alias で代用しない。
2. child 解決が返す associated equality と ordinary state update を、親の再captureと全source共有モデルに接続する。現行 linear head scanner と repeated-binder interval reconciliation の違いを隠さない。
3. その再生成driverを有限仕事領域・Paterson/K2の停止と意味的飽和へ接続する。

## Time and limits

予定開始2026-11-10T02:57:19Z、締切03:22:19Z。最初の環境dateは02:58:48Z、開始心拍に復元時刻03:00:14Zを記録し、03:00 UTC台に公開した。source心拍は03:06:02Z、03:06 UTC台に公開し、開始約10分時点を越える前に確認した。初回心拍が復元・読み取りの後になった遅れは記録する。

開始時とsource公開後の空きは48G（全63G、使用13G）。一つの作業場と既存cacheを再利用し、worktreeやcacheコピーは増やしていない。使用量枠は不明。I-11の部分目標が閉じた後、時間埋めの補題は足していない。

## Exact source CI

03:07:35Z時点で source `668ba0179d708c645899a08f4b10aa57320a9fa7` の core は success、proof は in_progress。最終確認を次に追記する。
- core: https://github.com/momota1029/yulang/actions/runs/42747281137/job/129602290681
- proof: https://github.com/momota1029/yulang/actions/runs/42747280823/job/129602285550

2026-11-10T03:09:01Zに再確認し、exact source commitの **proof/coreともcompleted / success** を確認した。以後の変更は報告と心拍のみで、Lean sourceは変えていない。ローカル全体検証を行ったという意味ではない。

報告・完了心拍準備時刻03:09:01Z、予定開始から約11.7分。公開と最終tree照合を含めて終了する。
