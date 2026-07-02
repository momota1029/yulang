# host act FFI の意味論決定

決定日: 2026-07-02
著者: Claude (Fable 5) — ユーザとの設計相談セッション（同日 2 回目）にて。ユーザ承認済み。
状態: **決定済み（authoritative）**

この文書は Yulang の FFI（第一層 = host capability FFI）の意味論を確定する。
[2026-07-02-resource-lifetime-decisions.md](2026-07-02-resource-lifetime-decisions.md)（以下 v1）、
[spec/2026-07-01-stable-standard-api.md](../../spec/2026-07-01-stable-standard-api.md)、
[spec/2026-07-02-server-resource-api.md](../../spec/2026-07-02-server-resource-api.md)、
notes/todo/ffi.md の続きであり、矛盾する場合は本文書と v1 を優先して spec 側を修正する。

本文書は §F7 で v1 の決定4 の enforcement 手段を修正する（ユーザ承認済み）。

テスト期待値は本文書の意味論から手で導出する。実装出力から逆算しない。
実装の都合で意味論を変えたくなったら、実装を止めてユーザに確認する。

## 0. 中心原理

> **FFI とは、「handler を host が提供してよい」と宣言された act である。**
> 境界は宣言で型付けされ、登録で経路付けされ、perform 時に名前で照合されることは決してない。

> **プログラム全体は unit を返す。**
> これは様式ではなく整合性条件である。multi-shot な host resume を認めた瞬間、
> 「プログラムの返り値」は一意に定まらなくなる（root 継続が N 回 unit に到達する）。
> 値はすべて effect でプログラムの外に出る。

> **FFI 全体は、一つの巨大な parameterized deep handler である。**
> - 登録の単位は (act, operation) ペア（Rust 関数）
> - 能力の単位は act
> - 意味論の単位は全体で一つの deep handler（return 節 = 分岐の帳簿処理、
>   handler パラメータ = host の外部状態）
> per-op 関数の合成が well-defined であることは §F8 の直交性規則が保証する。

現行実装との関係: evidence VM の escaped-effect loop（`eval_expr` 内の
`loop { Value → return / GenericRequest → handle_escaped_request }`、
runtime.rs 11890 付近）は、この deep handler の Rust 実装が既に**存在している**姿である。
本仕様は新築ではなく、文字列 if の列を registry に、暗黙の慣習を manifest に、
一直線の loop をトランポリン + scheduler に置き換える改修を指示する。

## F1. 宣言: `host act`

```yu
pub host act file:
    pub load: path -> result str io_err        -- 具体形は error 仕様確定に従う
    pub store: (path, str) -> result unit io_err
    pub meta: path -> result file_meta io_err
```

意味論:

- `host act` の操作は Yulang 内の handler で catch できる（mock / テストは従来どおり）。
- どの handler にも catch されなければ、host が登録した実装が handler として受ける。
- host が実装を登録していない場合は `EscapedEffect` クラッシュではなく
  **capability failure（構造化された失敗）**。wasm / playground の unsupported も同じ経路。

## F2. 経路: manifest + registry

- lowering は `host act` ごとに構造化 manifest を出す:
  act の stable id、各 operation の id と tier（§F6）、引数・返り値の型レイアウト
  （enum / error 型の constructor タグ表を含む）。
- host は起動時に manifest を読み、**名前ベース**で実装を登録し、名前→タグ解決を
  一度だけ行う。**Rust 側にタグ番号をハードコードしない**（コンパイラのタグ再割り当てで
  静かに壊れるため）。
- perform 時の文字列比較はゼロ。`handle_escaped_file_request` の path 文字列 if は全廃する。
- `EscapedEffect` は「host 込みで誰も供給しない効果が逃げた」という本物のエラーだけに戻す。
- console（`out::write`）も同じ機構に移設する（file 専用機構でないことの証明として）。

## F3. 失敗の二層

- **capability 層**（act が grant されない / unsupported / sandbox deny）:
  host のコードが走る前に **registry 自身が**起こす。宇宙で一つの統一語彙
  （stable-standard-api の deny / unsupported / failed 区別に対応）。
- **operation 層**（not_found / decode 失敗など）: ドメインの知識。host が manifest の
  タグ表からドメイン型（`io_err::not_found path` 等）を直接構築する。
  `?` 記法が unwrap として乗るのはこちら。
- int エラーコード（現行の 0/1/2/3 と `err_from_code`）は全廃する。

## F4. データの越境: manifest タグ表

- Yulang 側で宣言された enum / struct / error 型は、manifest の型レイアウトを介して
  Rust 側で構築・分解できる。act 内 enum を Rust 実装が使う権利はこれで担保される。
- 越境する値は常に**変換**される（§F9 R3）。

## F5. host 型（不透明型）

```yu
pub host act image:
    pub type image                    -- 綴りは仮
    pub decode: bytes -> result image img_err
    pub width: image -> int
```

- 実体は host 所有（VM: `HostValue(type_id, handle)`、native: GC が trace する opaque handle）。
- **host 型の値は Yulang から見て不変（immutable）でなければならない。**
  可変な Rust オブジェクトは multi-shot 分岐間で共有されて v1 決定2 の分岐独立性を壊す。
  加工は `blur: image -> image` のように新しい値を返す形で書く。
- **意味論的な寿命を持つ資源（file、socket、connection）を host 型にしない。**
  それは act + handler extent（v1 決定1）の領分。host 型は data に限る（Image は data、
  connection は resource）。
- host 所有メモリの回収は GC の drop hook でよい。v1 が禁じたのは「意味論的な後始末
  （write-back / unlock）を GC に依存させること」であり、観測不能なメモリ回収は抵触しない。
- act をまたぐ host 値の受け渡しは registry が type_id を照合する（安い動的検査）。

## F6. operation tier: sync / suspend one-shot / suspend multi-shot

manifest 上で operation ごとに宣言する（表面の綴りは未定、provisional）。

- **sync（既定）**: host は即座に一回 resume する（実際には Outcome::Return で値を返す）。
  継続は具象化されない。file / clock / random / image はここ。
  atomic 性は構成上得られる（runtime は接続単位で直列、host 呼び出し中に他が走らない）。
- **suspend one-shot**: 継続を scheduler に保管し、host は不透明な resume token を持つ。
  token の二重消費はランタイムの安い動的検査で弾く。
- **suspend multi-shot**: host は継続を複数回 resume してよい（`server.accept` はここ）。
  server spec の「multi-shot は別 capability」の正体はこの tier 宣言である。

multi-shot resume の帰結:

- 「接続ごとに分岐」は spawn 不要で直線コードになる:

  ```yu
  serve \&server ->
      my req = server.accept()    -- host が接続ごとに一回ずつ resume
      handle req                   -- ここが接続ごとの世界
  ```

  fork が「一回呼んで二回返る」のと同型で、undet が既にやっていることの host 版。
  state は純粋スレッディングにより分岐ごとに独立（v1 決定2 と同じ機構）。
- host に許すのは **`resume k v`（値を渡して起動する）スタイルのみ**。
  継続の中身を覗く・途中まで動かす・再入することは禁止。この制限下で host は
  意味論上「普通の deep handler の振る舞いの範囲内」にいる。
- **再入コールバック（host の Rust 関数の途中から Yulang を同期的に呼び戻す形）は
  第一層の Non-goal**。native ABI FFI（第二層）の宿題とする。

tier と実装経路の対応（実現性の根拠）:

- sync ↔ 継続を作らない direct route（VM の `DirectAbortive` / `DirectTailResumptive` 系譜、
  native では plain extern call）
- suspend 系 ↔ 継続の具象化（VM の `GenericRequest`、native では §F9 の capture）

継続具象化の税は suspend 系 operation だけが払う（意味論税の局所化）。

## F7. enforcement は三層（v1 決定4 の修正条項）

静的な multi-shot 追跡（線形型相当）は導入しない。mono→実行形態の境界に重い検査を
積まない。契約は三層:

1. **型が保証すること**: 新機構なし。effect row は capability 宣言のみ。
2. **ランタイムが安く検査すること**: token 二重消費の検出などフラグ一つで済むもの。
   debug ビルド限定でもよい。
3. **unspecified と文書化すること**: それ以外（suspend 操作を undet 領域で perform する等）。
   型では制御できないと明示して突き放す。

**v1 決定4 の修正**: 「typed failure または structured diagnostic で禁止」という
enforcement 手段を上記三層に置き換える。禁止の意図（multi-shot 領域での server accept は
サポートしない）は不変。ユーザ承認済み（2026-07-02 相談）。

## F8. 直交性規則

> **host handler の節は、兄弟 act の Yulang effect を perform してはいけない。**

- host 実装同士が Rust として直接呼び合うのは自由（Yulang から観測不能）。
- 禁止するのは Yulang の効果機構経由で別 act を起こすこと。これを許すと handler の
  合成順序に意味が生まれ、「全体で一つの deep handler」という見方が崩れる。
- この規則の下で、act 間の連携は「host 内部の private 共有状態」と
  「プログラムを通る Yulang 値」の二経路に限定され、どちらも直交性と両立する。

## F9. backend 非依存の host 契約（Cranelift 実現性の条件）

将来の Cranelift + GC 実装でも同じ host 実装が使えるために、次の三規則を契約に入れる。
**この三つを落とすと native 側で実現不能になる。**

- **R1: 継続は trait の関連型として不透明にする。** host が見るのは `type Cont: Clone` のみ。
  - VM: `Rc` の永続構造（clone は O(1)、確認済み: runtime.rs 293-297）
  - native: (i) CPS ヒープクロージャ連鎖（papers/ の Flanagan / Kelsey / Bruggeman 系譜。
    不変連鎖なら clone = 共有）または (ii) スタックセグメントコピー（Koka / OCaml 5 系譜。
    one-shot は move、multi-shot はコピー per resume）。選定は計測後。
  - tier 宣言は native 最適化の選択と一致する（Bruggeman: one-shot は copy せず move できる）。
  - host act の capture は **root まで**（プログラムの残り全部）であり、
    一般の限定継続の prompt 機構は不要。
- **R2: resume は enqueue であって、再入呼び出しではない。** host operation は
  `Return(v) / Suspended / CapabilityFailure` の Outcome を**返して戻る**。後から resume
  するときは (token, value) を scheduler の queue に積む。トランポリンは runtime が
  一つだけ持つ。host から runtime への同期的再入は存在しない
  （native のスタック規律を守る唯一の形）。
- **R3: 境界は常に変換し、GC ポインタを host に貸さない。** 越境する値は manifest の
  codec で変換される（プリミティブはコピー、host 型は slab の handle id）。
  pinning API は不要になり、copying GC は自由に動ける。

trait の骨子（正確な形は実装時に確定、§実装しないと分からないこと参照）:

```rust
pub trait HostRuntimeTypes {
    type Cont: Clone;              // backend private
    type Value;                    // manifest codec 経由でのみ構築・分解
}

pub enum HostOutcome<V> {
    Return(V),                     // sync tier
    Suspended,                     // suspend tier: host が token を保管した
    Failure(HostFailure),          // capability / operation 層は F3 に従う
}

// resume は必ず scheduler queue 経由。host からの再入呼び出しは存在しない。
```

state は純粋継続スレッディングにより継続 snapshot の中にいる（VM の `StateFrames` が現物、
native ではクロージャ連鎖内の値）。write barrier 例外も特別扱いも不要。

## F10. 局所的な公式 handler の扱い

- **禁止: ambient な召喚。** 公式 host 実装は root（embedder が置いた場所）にだけ存在し、
  プログラム内部から名指しで取得できない。許すと mock / sandbox が内側から素通しされる
  （server spec hygiene 節の「provider grant であって global ambient ではない」と同根）。
- **許可: 能力の明示的な受け渡し。** capability を持つスコープが operation の束を
  値（record / 関数群）として内側へ渡し、内側は委譲 handler で catch する。
  新機構は不要で、禁止/許可の線は「入手経路が ambient か明示的か」に引く。

## unit 強制の移行

- 現行 `run()` は roots の値を集めて返す（runtime.rs 8047、`RuntimeEvidenceRunOutput.values`）。
  script モードでは roots を unit に強制し、値の出力は effect 経由に統一する。
- `yulang run -e` のワンライナーは「式を暗黙に render / say effect で包む」脱糖で
  書き味を維持する。
- cases.toml の values 依存 case は移行する（機械的だが面数がある）。

## 実装順（thin path）

1. manifest 生成（lowering に `host act` の構造化出力）
2. registry（escaped-effect の文字列 if を置換、capability failure の typed 化）
3. file act を痩せた形（load / store / meta）に刷新し、std::io::file の int 解読層を撤去
   （v1 決定2 の buffer + commit は純粋 Yulang 側）
4. console を同じ機構へ移設
5. scheduler queue + suspend tier（server spec first slice = in-process test driver と合流）
6. unit 強制の移行
7. host 型（image 等の実例が要るときに）

## 実装しないと分からないこと（仕様が縛らない場所）

- `HostOutcome` の正確な形（payload 変換失敗の表現位置）
- scheduler の公平性・queue 順序の保証範囲
- host handle 回収のタイミング（GC unreachable 通知の粒度）
- native の capture 戦略 (i)/(ii) の選定（計測後）

## Non-goals

- native ABI FFI（第二層）を本仕様で扱うこと。
- 再入コールバック（host→Yulang の同期呼び戻し）。
- multi-shot 性の静的追跡（線形型・mono 境界の重い検査）。
- wire codec の一般化（第一層は同一プロセス・メモリ共有前提。codec が本当に要るのは
  第二層と server の network 境界）。
- 可変な host 型。
- 型推論・effect row の意味を変えること。

## Rollback 条件

次のいずれかが起きたら、実装を進めず本文書へ戻る。

- host が `resume k v` 以外の操作（継続の inspection / 部分実行 / 再入）を必要とした。
- 直交性規則（F8）を破らないと実装できない act が現れた。
- R2（enqueue 規律）を破って同期再入を入れたくなった。
- テスト期待値が実装出力と食い違い、期待値側を変えたくなった
  （期待値は本文書と v1 から手で導出する）。

## Validation（fixture の骨子）

```text
1. mock handler が host act を横取りできる（catch が registry より優先）。
2. 未登録の host act operation → capability failure（EscapedEffect クラッシュではない）。
3. operation 層のドメインエラーが constructor として届く（int コード経由でない）。
4. multi-shot accept: in-process test driver が同じ継続を 2 回 resume し、
   分岐ごとに state が独立していることを観測する。
5. token 二重消費（one-shot tier）→ ランタイムエラー。
6. F10: mock の内側に明示的に渡した capability record 経由でだけ実 I/O が起きる。
```

---

*署名: この文書は Claude (Fable 5) が 2026-07-02 の設計相談セッション（2 回目）で
ユーザと合意した内容を固定したものである。v1
（2026-07-02-resource-lifetime-decisions.md）の決定4 に対する修正条項 §F7 を含む。
ChatGPT / Codex が生成した文書と矛盾する場合、本文書を優先する。
変更にはユーザの明示的な承認を要する。 — Claude (Fable 5)*
