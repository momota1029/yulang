# Yulang cycle 388

この周に閉じた補題: S13ba（aligned_same_event_semantics）

I-68 の先頭一件だけ。任意の `ReplayJudgment`、状態 `s`、同じ lowered 木、任意の節の意味 `P : LiteralEvent s → Prop` を量化する。渡された `CanonicalDictionaryReplay replay` と `TreeMeaningOver P lowered` から、**同じ replay** の全 event、canonical 木の親と子の順・本数、元の receipt 列と、全出現の `P` を同一 ledger に保持する。forest と tree の相互帰納は exact `LoweredEventLedger` に従い、出力なしの出現も含む。別の event を `d/q/written` の一致や proof irrelevance から復元しない。新しい明示仮定はない。

## 検証と公開

- [実装](https://github.com/momota1029/yulang/blob/c9d7b2a82f6620b2fcb42878eb19b199c85cb88e/lean/Yulang/GeneralDeclarativeI65SameEventSemantics388.lean) と [独立監査](https://github.com/momota1029/yulang/blob/c9d7b2a82f6620b2fcb42878eb19b199c85cb88e/lean/Audit/Cycle388SameEventSemantics.lean)。元の checklist と定理の型が一致することを照合した。既存モジュールは変更せず、`lean/Yulang.lean` は元の全 bytes に当該 import 一行だけを追加。
- Lean 4.35.0、proof と別ファイルから import する audit の双方に `--trust=0 -DwarningAsError=true`。proof を `.olean` へコンパイルし、独立 audit の `#check` で元の定理の全量化を検証した。
- GitHub から immutable commit の proof/audit の両ファイルを再取得。Git blob hash とファイル bytes を照合してから新しい出力ディレクトリで両コマンドを再実行した。初回・再実行とも exit 0。 `#print axioms`: `[propext, Quot.sound]`。補助の四 fold も `#print axioms`: すべて `[propext]`。全体 build、Rust、checker は実行していない。
- 再利用した exact dependency のソース照合: manifest 7,356 件の path/blob ID が今回の Git tree と一致（C386 の新規 2 件と今回の 1 件は別照合）。今回の import graph が参照する 3,805 件はローカル source blob も照合した。これは既存成果物を選ぶための照合であり、3,805 件を再コンパイルしたという意味ではない。
- 発行は expected head を指定した nonforce の `work/dots-main` のみ。新規 Lean 2 ファイル・append-only barrel・checklist・heartbeat・報告の計 6 パス。凍結の 2 ファイルは blob ID のみ。最上段の定理・組立、S13bb を含む他の S 行の内容は変更なし。質問ノートなし。使用枠は不明。

```text
lean --trust=0 -DwarningAsError=true -o built/Yulang/GeneralDeclarativeI65SameEventSemantics388.olean Yulang/GeneralDeclarativeI65SameEventSemantics388.lean
lean --trust=0 -DwarningAsError=true Audit/Cycle388SameEventSemantics.lean
```

独立 audit の出力（初回・Git 再取得時とも同じ）:

```text
fun {P} {replay} =>
  aligned_same_event_semantics : ∀ {P : LiteralEvent s → Prop} {replay : LiteralTreeFrom tree t lowered},
  CanonicalDictionaryReplay replay →
    TreeMeaningOver P lowered →
      ∃ events,
        ExactReplayEvents replay events ∧
          ExactOrderedOccurrences (dictionaryTree d) events ∧
            orderedLiteralReceipts events = written ∧ LedgerMeaning P events
'Yulang.GeneralDeclarativeI65.aligned_same_event_semantics' depends on axioms: [propext, Quot.sound]
```

## 残り

**13 = 未証明 3 件（S01・S10・S13bb）+ 一部 10 件（S02–S09・S11–S12）。** S13ba はすでに与えられた局所意味の運搬であり、選択や型付き出力の意味を生成する補題ではない。一般の同一モデルの型付き固定先を具体化して辞書証拠を作る S13bb は未証明。Step 1 は未完、Step 2・3 未着手。S1/S2 全体は閉じず、C は後回し。受理条件、停止性、旧 Local/C334 は触っていない。
- 最終照合開始 `2026-11-24T08:20:43.493Z`（50 分経過）。
