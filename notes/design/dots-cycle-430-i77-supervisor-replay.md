# I-77 / C427〜C430 の統合用 exact replay

基準 `integration/m1-final` `af0cb4481578bdf76d7ae35ef06c5165216b643b`（Lean tree `efac6836b560e3180f253b5fc37b92ebbfafe9bd`）、候補 blob の出典 `5812d3bd90559aa723223674b4718e81d6ea5a4a`。基準から **41 paths (A40/M1) の Lean-only 投影**を作る。元の work履歴を巻き戻さない、別 branch を公開しない。既存のその他の変更や heartbeat を統合しない。統合する操作は未実行。

1. 基準と一致する独立 scratch で、[表の40ファイル](#immutable-paths) だけを `git show 5812d3bd90559aa723223674b4718e81d6ea5a4a:<path>` から取得。ディスクに書く前後で同じ Git blob ID を確認。各 path は［固定基準］には未存在。監督役の基準が変わった場合は重複/競合と関連前提を照合し、盲目的に上書きしない。
2. 基準の `lean/Yulang.lean` (blob `a332d22d0641b5ed130aa10662fa9dcf43f09687`) の正確な末尾に次の24 import を順に追加する。期待 blob `eb6efc13e38a80bba415c8860dfb93fb80a75538`。既存 Audit.lean と README.md は対象外。
3. 期待 root tree `737989c8b146516bf93c58ae3f7f56ff101a0442`、Lean tree `881d83f60dd5ca7064e241f8a7f71f0a5f7efee1`、Audit subtree `2d79c76fa96169854fe209a16ad4c3deb2ebd4d3`、Yulang subtree `abbe50dff208cb1a74302d3bc65ee408bc47a3e1`。metadata から Git object を組み立て、独立した scratch の `git mktree --missing` と `git diff-tree --no-renames -r --name-status` で A40/M1 と照合済み。Lean tree は実作業ブランチの exact Lean tree と一致。
4. 本番 olean だけを含む単一 `LEAN_PATH` で関係 production 24 本を対象ビルド。C427/428 の Audit 全16本を、一件ごとに空の cwd に置いて `lean --trust=0 -DwarningAsError=true input.lean`（Lean 4.35.0）。Audit olean を生成しない/見せない。監督の全体検査や統合は別。import の判定は [C429 の parser 版](dots-cycle-429-i76-supervisor-replay.md) と strict 実行を併用。

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
import Yulang.GeneralDeclarativeI65I74StructuralWhereTrace428
import Yulang.GeneralDeclarativeI65I74StructuralWhereFold428
import Yulang.GeneralDeclarativeI65I74StructuralWhereIdentity428
import Yulang.GeneralDeclarativeI65I74StructuralWhereMixedPosition428
import Yulang.GeneralDeclarativeI65I74StructuralWhereEmbed428
import Yulang.GeneralDeclarativeI65I74StructuralWhereSupportLookup428
import Yulang.GeneralDeclarativeI65I74StructuralWhereBodyReplay428
import Yulang.GeneralDeclarativeI65I74StructuralWhereAuditSupport429
import Yulang.GeneralDeclarativeI65I74StructuralWhereMixedAuditSupport430
import Yulang.GeneralDeclarativeI65I74StructuralWhereReplayAuditSupport430
import Yulang.GeneralDeclarativeI65I74StructuralWhereForestAuditSupport430
```

## Immutable paths

| path | Git blob |
|---|---|
| `lean/Audit/Cycle427I74StructuralWhereCore.lean` | `d2f1f08cd5b30344e05337cffbe5a43fa0abfa07` |
| `lean/Audit/Cycle427I74StructuralWhereForest.lean` | `2dbcf01d527204a2213063e61888f8991cda9f01` |
| `lean/Audit/Cycle427I74StructuralWhereOrdered.lean` | `a99235de100ec2bedce4d3faea424823314daf9c` |
| `lean/Audit/Cycle427I74StructuralWhereReadback.lean` | `2df10e2bf081112a7bbf9b027836275e14829d25` |
| `lean/Audit/Cycle427I74StructuralWhereSameRole.lean` | `401ae6ad802432b9483d96e287a6c3b37dc39c22` |
| `lean/Audit/Cycle427I74StructuralWhereSpec.lean` | `249b3f61749ce9977a00f2e5139b423a93aa089c` |
| `lean/Audit/Cycle427I74StructuralWhereVisits.lean` | `dee6b1cd03cdac8d1d11c637a140782d1d9b098d` |
| `lean/Audit/Cycle428I74StructuralWhereBodyReplay.lean` | `bfcb5318f0c7b0c7936c5f12fa71cbb6e8ea1022` |
| `lean/Audit/Cycle428I74StructuralWhereIntegratedLegacy.lean` | `8639d9b621a9335eebdc0bb008ead7e56397584c` |
| `lean/Audit/Cycle428I74StructuralWhereLegacyTrace.lean` | `9529840b67b8423bcce89f0d94ab557c14aaddf2` |
| `lean/Audit/Cycle428I74StructuralWhereMixedSibling.lean` | `141df1d560468fa68d7674c4c7c532abae88830b` |
| `lean/Audit/Cycle428I74StructuralWhereRootFrame.lean` | `270f758841653d8685075d0ab4eddde7598c780e` |
| `lean/Audit/Cycle428I74StructuralWhereSingletonTape.lean` | `b2d74f85dd815761ad62b91be5ce4ac9a76f1964` |
| `lean/Audit/Cycle428I74StructuralWhereSupportLookup.lean` | `c4c860f0cc2e65dc6e047eff40b8976593ed1c39` |
| `lean/Audit/Cycle428I74StructuralWhereTapeBoundary.lean` | `9b2b0278fa70774e46085c735a4529bd9032ce6b` |
| `lean/Audit/Cycle428I74StructuralWhereTrace.lean` | `72a1f0ccacf83554a943b7c04b93ceb9b159d0ce` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereAuditSupport429.lean` | `0c18bde888d552a44880a4afe34b31ac92cc359e` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereBodyReplay428.lean` | `c6d5d78a04cc93ef3b791019c122cf67f64e5a9a` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereChildRead427.lean` | `abb93a26e8d3b141d366920954440428ef3a4dbc` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereEmbed428.lean` | `95c19bdd007c2efc638e42787d8744b197a15cee` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereFold428.lean` | `1131fce69797d6c47ed5d59c4f937accf03d4287` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereForest427.lean` | `23b74a2458b6bf919f131283301c1cef90df66da` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereForestAuditSupport430.lean` | `92b141b722458e73c4374eae781950c035b8c17b` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereHeadRead427.lean` | `a006dddbb51c56e2a81c8a6dcbc7bac2cad43c6b` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereIdentity428.lean` | `1b009b369990c0e7ac64be234d7108e934e78c86` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereMixedAuditSupport430.lean` | `c999dfce8296feca1fd95ab7f3620a9090ba6444` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereMixedPosition428.lean` | `a09ffef98acef11fa21dc10b0a292866068d0fef` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereOrdered427.lean` | `4aabcb1ed4dc3fc9cbdf1035d9f197382cb63c95` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWherePair427.lean` | `8c06606978834aa4cca766d9c0bd95b14e292250` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWherePairRead427.lean` | `49efacf73ad99438c046d8a1f3bf4a454ddc8233` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereParent427.lean` | `981bb8e1d11b663d59327b8425e6ed52c3b4e909` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWherePositive427.lean` | `21a255a14fa91fa029020aa34137e5d0f038d79a` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereRead427.lean` | `7cf9a20f2ee15e640d0d81e3d0de385ee1752ce0` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereReplayAuditSupport430.lean` | `fb375092eb6428fc83bbe1c5ee8baeeefc84a4e4` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereRigid427.lean` | `d5c13dc30a662d031bc04102c697f9ae48610283` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereRivalRead427.lean` | `95074cb1ea6d347c98efdf23b02d8fc078e61abd` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereSource427.lean` | `ea5b21321e1dc57fb779397d1ff3b3fa29da416d` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereSupportLookup428.lean` | `c954c4fa5d18ea123f5b7ccddb6f1d4a5212af37` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereTrace428.lean` | `736e093c655976e58402356c740fbd80cc64043a` |
| `lean/Yulang/GeneralDeclarativeI65I74StructuralWhereVisit427.lean` | `806026c066f7797de6d6ef6e039ae26e72c24090` |

## 監査数の対象

新規・変更された C427–430 の16 Audit の明示 import に対する件数。統合史全体の件数ではない。固定基準の Audit 2,005 件のうちローカルに存在し Git blob ID まで一致した1,630件を、追加の読み取り専用対照として調べると、明示 `import Lean` 281件と `import Yulang` 3件が既存だった（この部分集合に Audit→Audit は検出されなかった）。したがって I-76/77 の厳密な prefix 判定を既存全体へ無条件に適用したとは報告しない。新規／変更された Audit は厳密に選び、監督役の歴史的 peer-Audit 検査は分ける。

原版7件は同じ clean cache で全て予想どおり exit 1 (`unknown module prefix`)、修復版7件は exit 0。C428の旧依存順回帰との照合で公理表示43件の宣言名・各公理集合も一致。24 import を一緒に読み込む focused test exit 0。
