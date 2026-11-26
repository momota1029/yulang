# C433 監督用: exact C16 Lean 差分の独立再検証

読み取った同期済み基準は `33cb37dfda2963da3b2a2e88c1887e8b864b21ac` の Lean tree `69b7cc04f527c7e4da13cf176132355885e250cc`。独立に再取得して検証した作業 pin は `c4eef8d3cd681e76eb576dfbfa3597806727062c`、Lean tree `e1c4d8d4485c52ea378acd2098f822e00f84e858`。公開一子入口の技術 pin は `eb15dba50001bc46a740cb1f378fd8746c84d80f`。

1. 旧 `lean/Yulang.lean` は全 byte を維持し、今回の追加 module を依存順に末尾へ追記した。旧 Audit/README は blob ID のみ照合。既存の他ファイルは置換しない。
2. 変更した 11 production module と 10 Audit を各 pin から再取得し、各 source file を `git hash-object` でその blob SHA に照合。既存の exact production cache に今回の各 module を別 cache に生成。各 Audit は別の空ディレクトリへ一ファイルだけ持ち込み、他 Audit の olean なし、Yulang production-only `LEAN_PATH` で実行。各ヘッダーは別 Audit の import がないことも解析した。
3. Lean 4.35.0 `lean --trust=0 -DwarningAsError=true`、exit 0。今回の 10 Audit、65 件の標準公理チェック。次の列は独立の累積 replay の実出力。C431 の実構造 where／legacy endpoint の既存監査も、それぞれ別の空 cwd で exit 0。全体 verify-lean は監督側で行う。

```text
build PASS Yulang/GeneralDeclarativeI65I74StructuralWhereOutputRead432
build PASS Yulang/GeneralDeclarativeI65I74StructuralWhereRootRead432
build PASS Yulang/GeneralDeclarativeI65I74StructuralWhereAssociatedRead432
build PASS Yulang/GeneralDeclarativeI65I74StructuralWhereAssociatedEntry432
build PASS Yulang/GeneralDeclarativeI65I74StructuralWhereReceiptRefinement433
build PASS Yulang/GeneralDeclarativeI65I74StructuralWhereSiblingReceipts433
build PASS Yulang/GeneralDeclarativeI65I74StructuralWhereSiblingPermutation433
build PASS Yulang/GeneralDeclarativeI65I74StructuralWherePairRead433
build PASS Yulang/GeneralDeclarativeI65I74StructuralWherePairTrace433
build PASS Yulang/GeneralDeclarativeI65I74StructuralWherePairBindings433
build PASS Yulang/GeneralDeclarativeI65I74StructuralWhereOriginalInput433
standalone PASS Audit/Cycle432I74StructuralWhereAssociatedEntry.lean
standalone PASS Audit/Cycle433I74StructuralWhereMovedReceipts.lean
standalone PASS Audit/Cycle433I74StructuralWhereOriginalInput.lean
standalone PASS Audit/Cycle433I74StructuralWherePairBindings.lean
standalone PASS Audit/Cycle433I74StructuralWherePairRead.lean
standalone PASS Audit/Cycle433I74StructuralWhereRawGuard.lean
standalone PASS Audit/Cycle433I74StructuralWhereReceiptRefinement.lean
standalone PASS Audit/Cycle433I74StructuralWhereSiblingPermutation.lean
standalone PASS Audit/Cycle433I74StructuralWhereSiblingReceipts.lean
standalone PASS Audit/Cycle433I74StructuralWhereTypedAliasGuard.lean
C433 combined: 10 standalone audits, 65 standard-only reports.
```

注意: `where` の順は source/report の順序のみ。二子読取器は隔離した補助で、公開 R16 の分岐に登録していない。通常の solver 進捗、停止性、未確定入力一般の診断は今回の対象外。
