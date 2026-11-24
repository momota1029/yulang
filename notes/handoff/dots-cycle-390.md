# Yulang cycle 390

この周に閉じた補題: S13bba（exact_replay_ledger_addresses）

I‑68 の先頭一件だけ。`ExactReplayEvents replay events` から、**同じ** lowered が持つ実 `Request` と `Dictionary` の構成子を、元の ledger の event へ対応づける。元の source guard と where の子 `event.kids`、子辞書の順序と本数を相互帰納で保持する。全状態・全有限木とその forest に対するそのままの文で、新しい source 選択・同一性・モデルの前提はない。住所付き ledger から canonical 診断木の順も取り出せる。住所を持つだけでは、typed payload の意味や fixed target での保持を導かない。

## 検証

- [Lean 実装](https://github.com/momota1029/yulang/blob/698dce6805076109f40f9d60e08cec4c7989a88b/lean/Yulang/GeneralDeclarativeI65AddressedReplay390.lean) と [独立 audit](https://github.com/momota1029/yulang/blob/698dce6805076109f40f9d60e08cec4c7989a88b/lean/Audit/Cycle390AddressedReplay.lean)。C389 の実験から目的部分だけを source にした。receipt payload の入れ替え実験・親の合成実験は module に入れていない。
- Lean 4.35.0、source と別 import audit とも `--trust=0 -DwarningAsError=true`。statement は checklist の全量化と一致。再取得した immutable Git blobs の hash を照合し、別の出力ディレクトリで同じ source / audit を再実行。初回と再実行は exit 0。C386 の exact 依存出力を再利用。既存 7,356 ソースの path/blob manifest が今回の Git tree と一致し、focused 依存 3,805 ソースのローカル bytes も照合した（既存分は再コンパイルしていない）。全体 build / Rust / checker は実行なし。

```text
lean --trust=0 -DwarningAsError=true -o built/Yulang/GeneralDeclarativeI65AddressedReplay390.olean Yulang/GeneralDeclarativeI65AddressedReplay390.lean
lean --trust=0 -DwarningAsError=true Audit/Cycle390AddressedReplay.lean
```

```text
fun {replay} {events} =>
  exact_replay_ledger_addresses : ∀ {replay : LiteralTreeFrom tree t lowered} {events : LiteralEventTree},
  ExactReplayEvents replay events → AddressedDictionaryEvents s q d events
fun {events} =>
  addressed_replay_has_canonical_order : ∀ {events : LiteralEventTree},
  AddressedDictionaryEvents s q d events → ExactOrderedOccurrences (dictionaryTree d) events
'Yulang.GeneralDeclarativeI65.exact_replay_ledger_addresses' depends on axioms: [propext]
'Yulang.GeneralDeclarativeI65.addressed_replay_has_canonical_order' depends on axioms: [propext, Quot.sound]
```

- `work/dots-main` の expected-head non-force だけ。新規 Lean 2 ファイル・元 bytes に import 一行を足す barrel・checklist・heartbeat・報告の 6 パス。固定した上段・S13bbb・他の補題の内容は変更なし。凍結 2 ファイルは blob ID のみ。質問ノートなし。使用枠は不明。

## 残り

**13 = 未証明 3 件（S01・S10・S13bbb）+ 一部 10 件（S02–S09・S11–S12）。** S13bbb は同じ State の concrete 局所意味と fixed target の実モデルでの型/行・点/非点の証拠を辞書として構成する別の未証明義務。S13bb 全体、一般の選択・型付き意味を証明したとは数えない。Step 1 は未完、Step 2・3 未着手。S1/S2 全体は閉じていない。C は後回し、停止性・旧 Local/C334・fixture は触っていない。
- 最終照合開始 `2026-11-24T10:20:51.646Z`（50 分経過）。
