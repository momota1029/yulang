# C427 のみを再検証・取り込む手順（I-76 / C429）

対象は **C427 の元の追加 + C429 の I-76 で指定された監査3件の修復**。C428 の Lean 差分や C429 の心拍を含めない。下の表は C429 の独立再検証に使った正確な Git blob。選択元は `794194e76370c26d2a967d8f535b7661e2e8a162`（`work/dots-main`）。基準 `integration/m1-final` は `34ece1698e5b8369f08e8d22e028a78d900e1594`、Lean tree `efac6836b560e3180f253b5fc37b92ebbfafe9bd`。書き込み・統合は行っていない。作業ブランチを丸ごと取り込むと C428 の未修復監査が来るので、そのままの cherry-pick や全取り込みではなく、以下の exact path projection が必要。

1. 監督役の別 checkout/scratch で基準の上から始める（元 branch には書き込まない）。基準が進んだ場合は対象 path の重複・内容と基準 barrel を再照合し、異なれば自動上書きしない。
2. 下の **21ファイルのみ**を `git show 794194e76370c26d2a967d8f535b7661e2e8a162:<path>` から取得し、書き込む前後で `git hash-object --stdin` / `git hash-object <path>` が表の blob と合うことを確認する。C427の旧報告は保存済みだがこの範囲に不要。凍結 Audit.lean / README.md は path 対象に一切含めない。
3. 基準の `lean/Yulang.lean`（blob `a332d22d0641b5ed130aa10662fa9dcf43f09687`）の末尾に以下 **14行のみ**を順に追記。投影後の期待 blob は `a5a850d5805f7453b0d5063d203d5983b9310deb`。作業ブランチの barrel は C428 import も含むのでコピーしない。
4. 新しい production olean のみの単一 `LEAN_PATH` で当該14モジュールを順に compile する。各 Audit は新しい空作業ディレクトリにそのファイルのみを置き、`lean --trust=0 -DwarningAsError=true input.lean` を別プロセスで実行。Audit olean を一切生成・配置・探索させない。Lean 4.35.0 で 14 production と全7 Audit が exit 0、50件の公理集合は標準のみ。既存 production `Main.olean`（B4Skeleton の推移的依存）が必要だが、Audit の olean とは別。
5. 取り込み後に `git diff --name-only <base> <projection>` が表21ファイルと barrel だけになることを確認する。C427 の監査3件は基準に未収録で、新規の path として入る。全体の検査・統合は監督役の作業。今回 R15 や C の閉鎖はない。

```lean
import Yulang.GeneralDeclarativeI65I74StructuralWhereSource427
import Yulang.GeneralDeclarativeI65I74StructuralWhereRead427
import Yulang.GeneralDeclarativeI65I74StructuralWherePositive427
import Yulang.GeneralDeclarativeI65I74StructuralWhereChildRead427
import Yulang.GeneralDeclarativeI65I74StructuralWhereOrdered427
import Yulang.GeneralDeclarativeI65I74StructuralWhereParent427
import Yulang.GeneralDeclarativeI65I74StructuralWhereRigid427
import Yulang.GeneralDeclarativeI65I74StructuralWhereRivalRead427
import Yulang.GeneralDeclarativeI65I74StructuralWherePair427
import Yulang.GeneralDeclarativeI65I74StructuralWhereHeadRead427
import Yulang.GeneralDeclarativeI65I74StructuralWherePairRead427
import Yulang.GeneralDeclarativeI65I74StructuralWhereVisit427
import Yulang.GeneralDeclarativeI65I74StructuralWhereForest427
import Yulang.GeneralDeclarativeI65I74StructuralWhereAuditSupport429
```

| path | immutable blob |
|---|---|
| `lean/Audit/Cycle427I74StructuralWhereCore.lean` | `d2f1f08cd5b30344e05337cffbe5a43fa0abfa07` |
| `lean/Audit/Cycle427I74StructuralWhereForest.lean` | `2dbcf01d527204a2213063e61888f8991cda9f01` |
| `lean/Audit/Cycle427I74StructuralWhereOrdered.lean` | `a99235de100ec2bedce4d3faea424823314daf9c` |
| `lean/Audit/Cycle427I74StructuralWhereReadback.lean` | `2df10e2bf081112a7bbf9b027836275e14829d25` |
| `lean/Audit/Cycle427I74StructuralWhereSameRole.lean` | `401ae6ad802432b9483d96e287a6c3b37dc39c22` |
| `lean/Audit/Cycle427I74StructuralWhereSpec.lean` | `249b3f61749ce9977a00f2e5139b423a93aa089c` |
| `lean/Audit/Cycle427I74StructuralWhereVisits.lean` | `dee6b1cd03cdac8d1d11c637a140782d1d9b098d` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereAuditSupport429.lean` | `0c18bde888d552a44880a4afe34b31ac92cc359e` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereChildRead427.lean` | `abb93a26e8d3b141d366920954440428ef3a4dbc` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereForest427.lean` | `23b74a2458b6bf919f131283301c1cef90df66da` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereHeadRead427.lean` | `a006dddbb51c56e2a81c8a6dcbc7bac2cad43c6b` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereOrdered427.lean` | `4aabcb1ed4dc3fc9cbdf1035d9f197382cb63c95` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWherePair427.lean` | `8c06606978834aa4cca766d9c0bd95b14e292250` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWherePairRead427.lean` | `49efacf73ad99438c046d8a1f3bf4a454ddc8233` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereParent427.lean` | `981bb8e1d11b663d59327b8425e6ed52c3b4e909` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWherePositive427.lean` | `21a255a14fa91fa029020aa34137e5d0f038d79a` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereRead427.lean` | `7cf9a20f2ee15e640d0d81e3d0de385ee1752ce0` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereRigid427.lean` | `d5c13dc30a662d031bc04102c697f9ae48610283` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereRivalRead427.lean` | `95074cb1ea6d347c98efdf23b02d8fc078e61abd` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereSource427.lean` | `ea5b21321e1dc57fb779397d1ff3b3fa29da416d` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereVisit427.lean` | `806026c066f7797de6d6ef6e039ae26e72c24090` |

## 監査 import の静的検査（監督役の候補）

Lean 自身の header parser を使用する。暗黙の Init を除き、実際の Name の最初の成分が Yulang であるものだけを許す。文字列検索でないので再引用・コメント・meta/public で別名を通さない。これは単独の strict 実行と組み合わせる（例: 非構文の `as Foo` は header 後の本文側で拒否）。

```lean
import Lean

open Lean Lean.Elab Lean.Parser

def explicitAuditImports (file : String) : IO (Array Import) := do
  let input ← IO.FS.readFile file
  let (header, _, messages) ← parseHeader (mkInputContext input file)
  if messages.hasErrors then
    throw <| IO.userError s!"invalid Lean header: {file}"
  return HeaderSyntax.imports header false

def main (files : List String) : IO UInt32 := do
  let mut bad := false
  for file in files do
    let imports ← explicitAuditImports file
    for i in imports do
      if i.module == `Yulang || i.module.getRoot != `Yulang then
        IO.eprintln s!"{file}: non-production explicit import {i.module}"
        bad := true
  return if bad then 1 else 0
```

上記を別ディレクトリの一時ファイルとして `lean --trust=0 -DwarningAsError=true --run CheckAuditHeader.lean <audits...>` で試した。修復済み C427 の全7件は通過。旧 C427 の3件、C428の7件、裸・quoted・`Audit.*`・明示 `Init`・quoted `«Yulang.fake»` は拒否。正しい引用付き `Yulang` と、コメント内の偽 import を含む正しい入力は通過した。リポジトリの supervisor tool 自体は変更していない。
