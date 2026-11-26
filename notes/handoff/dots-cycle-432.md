# Yulang C432 (I-74 / I-78)

この周に閉じた C の行: なし。
残り: 7（C16–C22）。
Audit の import: Yulang.* 以外 0 件

## 時間上限と検証した参照先

時間上限による引継ぎ。実開始は 2026-11-26T03:35:01.000Z。通常完了条件の50分に達するのは 04:25:01 UTC で、今回の絶対上限 04:25 UTC を超えるため、通常完了とはしない。照合を終えた時点でこの周の単独書き込みを終了。

* Live owner I-78 inbox blob `21275fefd4e9d1e11a5a88a4f0582a28472e9040`; integration at this read `8535d5de1d8334f5cc59ffe80788567a683ea135`, Lean tree `61e9ece31b2888dd90793d631cce25b6cdf21889`. C431/C15 exact integration is the baseline; this cycle does not write integration or types.
* Exact verified work tree before this report: `d4ffaa69da4369059b0a5440ea850a71206434f8`, Lean tree `69b7cc04f527c7e4da13cf176132355885e250cc`. Source scope only C16, §6.3's original `Wrap(list 'a, out = list 'b) where Container('a, item = 'b)`; here `list` is an authored invariant unary constructor, not a covariant substitution. No sibling/solver-order or termination claim.

## 確認済み成果

1. [A: original where child, lexical binder and fixed target](https://github.com/momota1029/yulang/commit/e9246b1159456c8cae9b471a846a062e6a701192). The actual selected child trace at its authored ordinal supplies the parent's same-model lexical RHS, rather than a merely equal value or a different child.
2. [B: literal authored invariant output plan and output-only boundary](https://github.com/momota1029/yulang/commit/c359f391e824b77340a567b0c61168e9a2296b01). Original syntax, B6 plan, input unchanged, fixed named output; the existing rules reject using `b` in an anonymous sibling input. The sibling control is a source scope result, not a new public acceptance claim.
3. [C: genuine Container child via previous public entry](https://github.com/momota1029/yulang/commit/0080602723edc3ccbbe3df971938b439514d5c03). Original occurrence `[72,0]`, declaration ordinal 1, original item slot 0/target 4; actual C419 branch, missing-write rejection through R15. The data uses a declared supported structural child, not a parser or live Rust run.
4. [D: actual same-State parent and child plus local dictionary law](https://github.com/momota1029/yulang/commit/04111fef42161a74b303c19b718d20fb74e19ef7). Both independently selected in a finite source trace; parent target 12 writes `list` of the child item at 4. Original request/child positions and two report write addresses in exactly source order. The law preserves dictionary meaning for every fitting model, including one concrete fitting model proved nonvacuously. This order is report observation, not solver execution.
5. 親を含む公開ディスパッチとその厳密な再検証までは完了していない。親 head と固定 B6 row の単独正負対照はローカルで標準公理のみで通ったが、独立 replay の監査完了を待てない成果は公開しない。データだけで親・元の子 request を読む結合読取器と、同じ元 receipt を比較する候補入口は手元で strict コンパイルした。元の正例・負例を通した exact replay が済むまで候補入口を公開・計上しない。C16 は未完。

Lean 4.35.0, `--trust=0 -DwarningAsError=true`. A–D: 41 standard-only axiom reports.  Each audit outside the repository source cwd, no peer Audit imports/oleans; verified exact detached Git bytes, frozen Audit.lean and README by IDs only. Existing Lean unchanged except import barrel append. No full builds, Rust, completeness, or termination tests.

Next: 元の同じ State の選択トレースを公開 R16 に接続する。元の選択・where clause 0・固定出力・全 receipt 順序を検査し、間違った子出力 row・report 順を拒否。従前入口とのすべての旧入力で Bool が一致、同じ形の `check_sound`、同じモデルの辞書を一緒に確認してからのみ C16 を計上する。
