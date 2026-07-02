# File / Server 資源寿命の意味論決定

決定日: 2026-07-02
著者: Claude (Fable 5) — ユーザとの設計相談セッションにて。ユーザ承認済み。
状態: **決定済み（authoritative）**

この文書は [spec/2026-07-01-file-resource-api.md](../../spec/2026-07-01-file-resource-api.md) と
[spec/2026-07-02-server-resource-api.md](../../spec/2026-07-02-server-resource-api.md) が
曖昧にしている意味論の継ぎ目 4 箇所を確定する追補である。
spec 本文と本文書が矛盾する場合、**本文書の決定を優先し、spec 側を修正する**
（修正箇所は §7 に列挙）。

本文書の決定（特に §決定2 の commit / rollback 意味論と、それを固定するテスト期待値）を
実装の都合で変更してはいけない。変更が必要になった場合は、実装を止めてこの文書へ戻り、
ユーザの判断を仰ぐこと。**テスト期待値を実装出力に合わせて書き換えることは、
この文書に対する違反である。**

## 0. 中心の言い方

この API 設計の「Yulang だからこそ」は、close を消したことそのものではなく、
次のように言い切れることである。

> **ファイルとは、耐久性のある `&` 変数である。**

`my &text = file::text path` と書けたとき、既存の `$text` / `&text = ...` の
state sugar、lens、line view がそのまま乗る。ファイル編集はローカル `str` 変数の
編集と同じ見た目になる。そして `[fs]` を mock handler で受ければ、ディスクに
触らない純粋なテストが**構文を一切変えずに**書ける。

open/close/save/flush という状態機械が表面にないのは利便のためではなく、
この同一視を成立させるための必然である。

## 決定1: 資源の寿命は「値の生存」ではなく「handler の extent」で終わる

spec/2026-07-01-file-resource-api.md には「unscoped form はその値が生きている間
write capability を持つ」とあるが、この言い方を廃止する。

理由: Yulang は copying GC であり、「値が生きている間」は観測可能な意味論上の
点にならない。write-back のタイミングを GC 到達性に縛ると非決定的になり、
finalizer 機構を要求する。

決定:

> **資源の寿命は常に「あるスコープの終端」で終わる。
> `_with` / `do` 形のスコープはその continuation の終端。
> unscoped 形のスコープは、その資源を供給した handler の extent である。**

系:

- 「スクリプト終了まで保持」は特例ではない。デフォルトの host fs handler が
  プログラム終端で discharge される、という一般規則の帰結である。
- テスト用 mock handler の下では、`catch` を抜ける点が write-back 点になる。
- GC finalizer は永久に導入しない。資源後処理を GC に依存させない。

## 決定2（本丸）: managed lens はスナップショット・トランザクションである

Yulang には `undet` と junction があり、継続は多重 resume される。
`text_with path \&text -> body` の body が undet 領域に入っていれば、
scope exit は複数回起きる。古典的には bracket と multi-shot continuation は
両立しない（Multicore OCaml が one-shot に倒した理由の一つ）。
2026-05-15 に std::fs が「open/close を露出させない」と決めた元々の動機も
この非決定性との相性だった。

Yulang はこれを正面から解ける。state は純粋継続スレッディングで実装されて
いるため、**managed lens の buffer は undet の分岐ごとに自然にスナップショット
される**。よって次のように定義する。

> **managed lens = スナップショット・トランザクション。**
>
> - scope entry で backing file を読み、buffer を作る。
> - buffer 編集は継続の分岐ごとに独立である（純粋 state スレッディングの帰結）。
> - scope exit が commit（write-back）である。
> - 多重 resume された分岐は、それぞれ独立に commit する。commit 順は
>   scope exit への到達順であり、last-write-wins。
> - **effect による中断で scope exit に到達しなかった分岐は write-back しない。
>   すなわち abort = rollback。**

この定義により:

- bracket 問題は「バグの温床」から「意味論の帰結」に変わる。二重 close、
  closed handle への書き込み、save 済み dirty buffer という状態は
  状態機械ごと存在しない。
- abort = rollback は VM に unwind finalizer を要求しない。dirty buffer は
  捨てられるだけである。エラーで途中離脱したファイルは無傷、という
  ユーザ向けの約束にもなる。
- managed lens は「open 時スナップショット・exit 時 commit」の長い
  トランザクションである。スコープ中の外部変更は commit で上書きされる。
  live access が必要なら `raw` を使う。この一線を崩さない。

## 決定3: lock 解放の実装単位は当面 handler extent

write-back は rollback で逃げられるが、lock 解放は逃げられない
（分岐が捨てられたとき lock を握ったままにできない）。選択肢は:

- (a) evidence VM に「継続セグメント drop 時に走る hook」を足す — 正確だが VM 工事。
- (b) lock を scope ではなく **fs handler の extent** に紐付ける — 粗いが安全。
  handler discharge 時（プログラム終端 or `catch` 脱出）に全て返す。

決定: **first slice は (b)。** 単一プロセスの script 用途では handler extent の
lock で実害がない。(a) の continuation-drop hook は server の cancellation でも
必要になるため、そのとき一度だけ VM に入れ、lock 解放を scope 単位へ細粒度化する。

spec/2026-07-01-file-resource-api.md の Locking 節に
「lock release の実装単位は当面 handler extent」と追記する。

## 決定4: server の `accept` は multi-shot 領域で禁止する

spec/2026-07-02-server-resource-api.md は stored continuation の one-shot を
既に決めているが、「`accept` を undet / junction の内側で perform した場合」が
未定である。scheduler に保存された継続が複製されると one-shot 保証が壊れる。

決定: **最初は typed failure または structured diagnostic で禁止する。**
「junction × server」は将来の別 capability として明示的に閉じる。

非対称性の明文化: file 側はトランザクション意味論（決定2）で multi-shot と
共存できるが、server 側は共存できない。この非対称は設計の欠陥ではなく、
「commit をやり直せる資源」と「外部へ一度きり応答する資源」の違いに由来する。
spec に一節として書き残すこと。

## 5. 実装順（thin path）

1. **mock handler で file session。** `[fs]` を Yulang 内の pure handler で受け、
   `file::text` / `text_with` / commit / rollback の意味論をディスクなしで
   fixture 化する。決定2 の検証がそのまま regression になる。
2. **native host handler。** 既存の `std::io::file` bridge（migration-canary）の
   上に buffer + commit を実装する。lock なし。
3. **undet との交差テスト。** `text_with` の中で junction を使う fixture を作り、
   分岐ごと独立 commit を golden 化する。これが「Yulang だからこそ」の証明であり、
   公開 example にそのまま流用する。
4. lock（handler extent、決定3）、server first slice（in-process test driver、
   server spec 記載の順）はその後。

## 6. FFI との接続（次回の相談対象、方向だけ固定）

「host capability = host handler が grant する act の束」という見方をすれば、
fs / server / clock / random / FFI はすべて「handler が供給する操作」であり、
notes/todo/ffi.md の二層（host capability FFI → native ABI FFI）と矛盾しない。
決定1 の「寿命 = handler extent」により、FFI 資源の寿命規則は本文書と
同じ文で書ける。act 単位 FFI の詳細設計は次回の相談で確定する。

## 7. spec 側の修正箇所

- spec/2026-07-01-file-resource-api.md:
  - 「その値が生きている間 write capability を持つ」→ handler extent の言い方へ
    修正（決定1）。
  - Managed lens 節にトランザクション意味論（snapshot / commit / rollback、
    多重 resume の独立 commit）を追記（決定2）。
  - Locking 節に「lock release の実装単位は当面 handler extent」を追記（決定3）。
- spec/2026-07-02-server-resource-api.md:
  - `accept` の multi-shot 領域での perform を typed failure として明記（決定4）。
  - file / server の非対称性（commit をやり直せる資源 vs 一度きりの応答）を
    一節として追記。

## Non-goals

- GC finalizer / 到達性ベースの資源後処理を導入すること。
- managed lens に close / save / flush を追加すること（spec 通り）。
- unwind finalizer を write-back のために VM へ追加すること（rollback で不要）。
- managed lens に live file access を持たせること（`raw` の領分）。
- server continuation の multi-shot 対応（将来の別 capability）。
- 型推論・method resolution・effect row の意味を変えること。

## Rollback 条件

次のいずれかが起きたら、実装を進めずこの文書へ戻る。

- commit / rollback 意味論を実装都合で変えたくなった。
- 多重 resume の独立 commit が evidence VM 上で表現できないと判明した
  （その場合は state スレッディングの実装前提が崩れているので、まず病名を確定する）。
- lock の handler-extent 束縛が script 用途で実害を出した。
- fixture の期待値が実装出力と食い違い、期待値側を変えたくなった
  （**期待値はこの文書の意味論から手で導出する。実装出力から逆算しない。**）。

## Validation（fixture の骨子）

決定2 を固定する最小 fixture 群:

```text
1. text_with で編集 → scope exit → ファイル内容が更新されている（commit）。
2. text_with の中で error effect により離脱 → ファイル内容が無傷（rollback）。
3. text_with の body が junction で 2 分岐 → 各分岐が独立に編集・commit、
   最終内容は到達順の last-write-wins。
4. [fs] を mock handler で受けた場合、1〜3 が pure state として同じ観測になる。
5. unscoped の file::text をトップレベルで作成 → プログラム終端（handler
   discharge）で write-back される。
```

fixture は決定2 の文面から手計算で期待値を導出して書く。
実装が先にあってはならない。

---

*署名: この文書は Claude (Fable 5) が 2026-07-02 の設計相談セッションで
ユーザと合意した内容を固定したものである。ChatGPT / Codex が生成した文書と
本文書が矛盾する場合、本文書を優先する。変更にはユーザの明示的な承認を要する。
— Claude (Fable 5)*
