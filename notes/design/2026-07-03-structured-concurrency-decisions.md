# Structured concurrency and cancellation decisions

決定日: 2026-07-03
状態: **決定済み（serve first slice の前提）**

この文書は `server.accept` / `net.recv` などの suspend host operation が作る
分岐の所有権、死の規則、キャンセル経路を固定する。

根拠:

- [2026-07-02-resource-lifetime-decisions.md](2026-07-02-resource-lifetime-decisions.md)
  決定1〜3: resource lifetime は handler extent / scope に属し、managed lens の
  branch drop は rollback である。
- [2026-07-02-host-act-ffi-decisions.md](2026-07-02-host-act-ffi-decisions.md)
  F6〜F9: suspend tier、scheduler queue、host から runtime への再入禁止。
- [spec/2026-07-02-io-resource-api.md](../../spec/2026-07-02-io-resource-api.md)
  §3: `accept` は suspend multi-shot tier で、respond は one-shot capability 消費。
- [notes/todo/structured-concurrency.md](../todo/structured-concurrency.md)
  の user-approved task split。

serve の実装（host act FFI 実装順 5）に入る前に、この文書を読む。
実装中にここを変えたくなった場合は、コードを進めず設計へ戻る。

## 0. 中心原理

> **host resume が作る分岐は、必ず structured な子である。**

`server.accept` が外部 event ごとに continuation を resume するとき、その resume は
匿名の detached task を作らない。resume で生じた branch は、accept を供給した
server handler extent を親に持つ子である。

帰結:

- 子 branch の寿命は親 handler extent を超えない。
- 親 handler extent が終わると、未完了の子 branch はすべて cancel/drop される。
- 子 branch が scope exit に到達しなかった場合、file managed lens の dirty buffer は
  v1 決定2どおり rollback される。
- GC 到達性を resource cleanup の意味論に使わない。

## 1. 用語

- **branch**: suspend host operation の resume により生じた continuation world。
  `undet` の branch と同じ「世界分岐」だが、所有者は host scheduler である。
- **branch id**: scheduler が割り当てる実行内識別子。record/replay、
  diagnostics、cancel queue のための実装上の id であり、最初の public API では
  user value として公開しない。
- **parent extent**: branch を作った host act handler の extent。
  `serve_with` / `connect_with` ならその resource scope、unscoped server なら
  その handler discharge 点。
- **suspended branch**: scheduler queue / token 上で止まっている branch。
- **running branch**: runtime trampoline が現在実行している branch。
- **respond slot**: request resource に含まれる one-shot capability。二重消費は
  cheap dynamic check で拒否する。

## 2. Branch ownership

host scheduler は branch tree を持つ。

```text
server handler extent
  branch 0: root action before first accept
  branch 1: request A after accept resume
  branch 2: request B after accept resume
```

規則:

1. suspend multi-shot operation が branch を resume するたびに、新しい child
   branch id を割り当てる。
2. child branch は parent extent の子として登録される。
3. branch が normal completion へ到達したら scheduler から消える。
4. branch が user-level error / unhandled effect / runtime error で終了した場合も
   scheduler から消える。adapter への報告形は host policy だが、branch は orphan
   として残さない。
5. parent extent が終わる時点で未完了 branch があれば、それらを cancel/drop する。

この規則は `accept` 専用ではない。将来の `recv` / timer / in-process test driver も
同じ branch ownership に乗せる。

## 3. Cancellation path

cancel は host から runtime への同期再入ではない。
host act FFI F9 R2 と同じく、scheduler queue へ event を積む。

```text
host observes disconnect/timeout/scope-close
  -> enqueue Cancel { branch_id, reason }
  -> runtime trampoline consumes queue
  -> scheduler drops or marks the branch
```

first slice の規則:

- suspended branch は即時 drop できる。
- running branch は preempt しない。pending-cancel として印を付け、次の suspend
  point / safe scheduler boundary で drop する。
- preemption、任意点での stack unwinding、unwind finalizer は導入しない。
- cancel は rollback を意味する。scope exit に到達していない file managed lens は
  write-back しない。

この first slice は「suspend 中の branch を cancel したら、その branch の dirty file
buffer が commit されない」ことを fixture 化できれば足りる。
running branch の協調 cancel は次 slice に回す。

## 4. Request / response one-shot rule

request response は file commit と違い、やり直し可能な write-back ではない。

規則:

1. `request.respond` は respond slot を消費する。
2. 同じ respond slot の二重消費は runtime error か typed operation failure にする。
   silent dedupe しない。
3. cancel/drop された branch は暗黙 response を送らない。
4. normal completion した branch が respond していない場合の exact adapter behavior は
   first slice の stable contract ではない。in-process driver は
   `unresponded_request` として観測可能にしてよいが、HTTP adapter などの wire behavior は
   server adapter spec で決める。

## 5. Cleanup model

cleanup は三層に分ける。

1. **semantic cleanup**: branch drop = scope exit 不到達なので managed lens は rollback。
   これは既存の file transaction 意味論で足りる。
2. **host-private cleanup**: socket close、temporary handle release、respond slot 破棄。
   host adapter 内部の資源なので Yulang の user code から観測できない。
3. **user-visible cleanup**: cancel 時に user code が何かを書く API。
   first slice では入れない。必要なら将来、cancel を effect として expose し、
   user handler が catch する形を検討する。

lock release は v1 決定3どおり first slice では handler extent 単位のまま。
branch 単位の細粒度 release は continuation-drop hook と同じ VM 工事として扱う。

## 6. Record/replay identifiers

record/replay と scheduler は同じ branch id 空間を使う。

manifest / runtime log は少なくとも次を区別できるようにする。

```text
operation_seq
parent_branch_id
child_branch_id
resume_ordinal
operation_id
host_result_or_cancel_reason
```

first slice で完全な record/replay を実装しない場合でも、branch id を後付けで
破壊的に変えなくて済むよう、scheduler の内部表現には最初から parent/child を置く。

## 7. Queue ordering and fairness

runtime 内部 queue は deterministic replay のために順序を持つ。
in-process test driver は enqueue 順に event を処理する。

ただし、real host adapter の公平性、network event ordering、backpressure policy は
first slice の stable contract ではない。adapter が観測した順序を log に残し、
replay はその log に従う、という位置づけに留める。

## 8. Multi-shot interaction

`accept` / `recv` などの suspend host operation を user-level `undet` / junction の内側で
perform した場合は、host act FFI F7 の三層契約に従う。

- 型はこれを静的に禁止しない。
- respond slot 二重消費や resume token 二重消費のように cheap に検出できるものは
  dynamic check で拒否する。
- それ以外は unspecified と明記し、Contract v1 の fixture にしない。

file は snapshot transaction なので multi-shot と共存する。
server request は one-shot response capability なので同じ扱いにしない。
この非対称は仕様である。

## 9. Implementation order

serve first slice に入る前の順序:

1. scheduler に branch id / parent id / status を持つ内部表を用意する。
2. scheduler queue に `Cancel { branch_id, reason }` を追加する。
3. suspend 中 branch の immediate drop だけを実装する。
4. in-process test driver で、request branch を suspend 中に cancel できるようにする。
5. fixture:
   - cancel された branch の file edit は rollback される。
   - parent extent 終了で suspended child branches が drop される。
   - double respond は dynamic failure になる。
   - two request events get distinct branch ids / branch-local state.
6. running branch の協調 cancel、timeout sugar、adapter-specific response policy は次 slice。

## 10. Non-goals

- preemptive cancellation。
- cancel のための unwind finalizer。
- branch cleanup を GC に任せること。
- detached task / unstructured spawn。
- public `branch_id` value surface。
- HTTP framework の先行実装。
- backpressure / timeout / fairness の stable API 化。
- multi-shot 性の静的追跡。

## Rollback conditions

次のいずれかが必要になったら、serve 実装を止めてこの文書へ戻る。

- host から runtime への同期再入。
- running branch の任意点停止。
- rollback では足りない write-back finalizer。
- orphan branch を GC で回収したことにする設計。
- respond slot の silent dedupe。
- detached branch が parent extent より長生きする設計。
