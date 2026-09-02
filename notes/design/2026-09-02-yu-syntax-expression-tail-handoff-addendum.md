# Authoritative: yu-syntax の式 tail 引き渡し追補

Status: Authoritative

Scope: 提案中の `chasa-recover 0.2` 書き換えにおける、式の `expr` /
`tail` 手続きを訂正する。この追補が扱うのは実行トポロジーだけである。
Yulang の表面文法、source order のまま平坦な `OperatorChain`、CST の語彙と階層、
AST/direct 互換生成物、diagnostic、recovery identity、Yumark のストリーミング規則、
および Gate 9 以前に old/new production crossing を禁じる境界は変更しない。

Drafted-by: ユーザーが示した手続きと Yulang2 の式パーサを基に primary agent が起草

Approved-by: user

Approved-at: 2026-09-02

Review: M3 compiler/recovery・specification review。初回の blocking 指摘を修正し、
2026-09-02 に scoped delta review で両方の closure を確認済み

User decision added: 2026-09-03。受理済み RHS の recovery は子に渡した `level` と
ML mode を保持し、trivia boundary の再開・close/stop 変換は payload cursor、active frame、
実際の token と owner capability を検証する。この追加は Gate 2 の二巡目 review が検出した
所有権 gap を閉じるものであり、M2 の repair budget を使い切ったため M3 の一回だけの
scoped repair/review を認可する。

この追補は expression pilot とその後の移行 closure に限って、
次を置き換える。

- `2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md` の §3.2、§3.3、
  §6 にある、expression tail に限った次の定義
  - `TailPosition::Start | TailPosition::AfterOperand`
  - level を「non-numeric な structural context」に限定する記述
  - fallible direct function は `In<I, R, ()>` だけを受け、`S` には
    total な `then` を通じてだけ触れるという記述
- 同文書に混ざっている、tail を recognize してから materialize するという解釈
- 未コミットの Gate 2 `rewrite/` shell にある `CommittedState`、accepted-action
  buffer、generic materializer のトポロジー

この文書は stopped shell の削除、production dispatch の変更を認可しない。狭い訂正範囲の
外では、元の Authoritative plan が引き続き正本である。

## 1. 手続きの出典

手続きは、2026-09-02 にユーザーが示した説明と、Yulang2 v7 の以下の実装を合わせて
読むことで定める。

- `expr/core.rs` の `parse_expr_bp` と `parse_expr_from_nud`
- `expr/tail.rs` の `parse_tail_bp` と `pratt_tail_bp`

特に Yulang2 では、子の式を読み終えた後に次の三つの継続がある。

1. 子が通常完了する。外側 tail は次の LED を自分で scan する権利を持つ。
   次は二項演算子でも ML application でもよい。
2. 子が、その子の `level` では読めない、すでに scan 済みの LED を一つ残す。
   外側 tail はその**同じ** LED を自分の `level` で直ちに読み直す。
3. 子が caller-visible な boundary に達する。外側 tail はその `End` を caller へ
   伝播する。

三経路とも source を巻き戻さず、保持した trivia を再 scan せず、
平坦な operator chain を precedence tree に変えない。`level` は各 tail が何を
読めるかと、受理した二項演算子が RHS に渡す level を決める明示的な operational binding
threshold である。内部表現は private に保ってよく、operator environment を参照してよい。
ただし AST node でも CST node でも別の operator-association 生成物でもない。

## 2. recognize/materialize ではなく直接手続きにする

新しいパーサは recursive descent の手続きをそのまま直接書く。ここで supersede する
§3.2 の制限に代わり、expression の `expr`、`tail`、および受理済み branch から呼ぶ
direct continuation は `In<&str, R, S>` を直接受ける。branch を受理した時点で
Rowan/recovery effect を出す。`S` は通常の出力能力である。例えば Rowan builder と
commit 済み publication を持てるが、parser result でも phase transition でも
`CommittedState` wrapper でもない。

generic な `AcceptedAction`、action buffer、後段 materializer は作らない。特に、
tail 全体を先に recognize し、中立な action として保存してから Rowan へ replay しては
いけない。そうすると、この手続きに必要な局所的な所有権と handoff が失われる。

tail は、現在の item を自分の level/mode/frame で読めると決めるまで、`S` を mutate せず、
commit 済み recovery も作らない。従って未読 item を返す経路は、構造上 effect-free である。
構造で証明できないなら、tail entry の checkpoint から owner-local `R`、expectation state、
diagnostic allocation、persistent recovery state、`IsCut`、explicit frame mutation を全て戻す。
この rollback は既に完成した current `Item` より前へは戻らない。scanner-owned な leading
trivia、identity、payload extent はそのまま handoff する。

`None` の commit frontier は明確にする。direct function が `None` を返せるのは、まだ
input を受理せず `R` と `S` の effect を作っていない入口だけである。core/prefix/tail
introducer を受理して Rowan/recovery を emit した後、以後の continuation は total でなければ
ならない。失敗は `None` にせず、その owner の typed recovery、`Ok(())`、未読 `Item`、
または `End` に変換する。

この狭い direct-`S` override の外では、元の `R`/`S` 契約を保持する。`R` は
speculative/recoverable state を引き続き持ち、`ParserOnce::None` は非消費と rollback の契約を
守る。以下の Pratt handoff は別の局所 control flow であり、ここでの `Err` に一般の
parser/recovery としての意味はない。

### 2.1 受理済み operand recovery の control 継承

binary、prefix、ML application が operand を受理するために子の `expr` を呼ぶとき、子の
`level` と `ExprMode` はその child owner の control context である。子が `None` になった後に
owner-specific typed recovery を emit して total continuation へ移る場合も、この context を
捨てて `Level::OUTER`/normal mode へ戻してはならない。

recovery 後の child は、通常の child と同じ三経路を返す。すなわち次を自分で scan する
`Ok(())`、読めない scan 済み item の `Err(Left(item))`、boundary の `Err(Right(end))` である。
特に child level で読めない下位演算子 item は、recovery path でも同一 identity のまま外側 tail
へ handoff されなければならない。

## 3. Item と boundary 入力

既存の「一論理 item」規則は変えない。

```text
Item {
    leading_trivia,
    payload: token | boundary,
}
```

`tail_item(i)` は「operator だけを読む scanner」ではない。tail 位置で次の続きになりうる
現在の item ちょうど一つを完成・分類する。leading trivia はその item に属する。分類対象は
infix/suffix/field/path/colon/assign/with/cast、call/index 開始、そして ML application の
右側になりうる NUD である。

`(` はこの違いをよく表す。まず leading trivia が現在の layout/frame/mode では continuation を
許すか判定する。same-level newline や dedent のように許さないなら、opener を消費せずに
trivia-caused boundary を返す。continuation が許される場合だけ、leading trivia がない `(` は
call 開始として分類し、許された trivia を伴う `(` は `MlNud(OpenParen)`、すなわち ML
application の右側として分類する。他の atom、prefix、nullfix、string、list なども同様に
`MlNud(nud)` になりうる。`ml_arg` は token ではなく、この右側を読む `expr` に渡す局所 mode
であり、そこで更なる tail を読める条件を制限する。特に nonempty trivia を持つ ML argument
は、Yulang2 と同じく次の LED scan より先に止められる。

現在の item を `Close`、`BorrowedClose`、`Dedent`、`Stop`、`EofAfterTrivia` に分類してよいし、
現在の payload token を消費してよい。しかし二つ目の論理 item を取得したり、lookahead を
state に隠したり、保持した item を再 scan してはいけない。

expression 手続きにおける `End` は、そのような item から得た caller-visible な式の
boundary である。boundary の正確な語彙と所有権は、元の rewrite plan §3.3 を維持する。
返す `Item` は identity、payload、leading trivia、source extent を正確に保つ。受け取った
tail は scanner を呼び直さず、そのまま使わなければならない。

### 3.1 再開と boundary classifier の capability

trivia-caused boundary を再開して payload を完成させる owner は、retained item の payload
cursor と live `&str` cursor が同じ位置であることを cheap index/pointer identity で検証する。
次の layout frame は、現在の baseline で再度 dedent predicate を判定する。まだ dedent なら
payload を消費せず同じ boundary を返す。そうでなければ、identity、leading trivia、extent、
logical position を保つ同じ current item を完成できる。

`BorrowedClose`、`Stop`、およびその release/reclassification は `Item` の public conversion
ではない。期待 delimiter または stop token と active owner/frame capability を持つ手続きだけが、
item 内の実際の lexical evidence を検証して行える。異なる cursor、まだ dedent の frame、
異なる delimiter/stop token、owner を持たない呼び出しは fail-fast し、item を再分類も消費も
してはならない。

## 4. `expr` と `tail` の handoff

次は control flow を示す擬似コードである。個々の syntax owner の recovery recipe は
定めないが、handoff の三結果は具体的に定める。

```rust
// Ok(())             : 子は通常完了。呼び出し側 tail が次を scan する。
// Err(Left(item))    : 子が読めない、同じ scan 済み item を返した。
// Err(Right(end))    : caller-visible な boundary。
type TailExit = Result<(), Either<Item, End>>;

fn expr(mut i: In<&str, R, S>, level: Level) -> Option<TailExit> {
    if let Some(prefix) = prefix(i.rb()) {
        // prefix を受理した後は total である。
        return Some(prefix_after_accept(i, level, prefix));
    }

    core(i.rb())?; // None はここまでの、effect-free な不受理だけで返せる。
    Some(scan_tail_after_accept(i, level))
}

fn scan_tail_after_accept(mut i: In<&str, R, S>, level: Level) -> TailExit {
    // EOF や trivia-caused boundary を含め、受理後の item completion は total。
    let tail_item = tail_item_after_accept(i.rb());
    tail(i, level, tail_item)
}

fn tail(mut i: In<&str, R, S>, level: Level, item: Item) -> TailExit {
    match item {
        Item::Boundary(end) => Err(Either::Right(end)),

        item if !tail_reads(i.rb(), level, &item) => {
            // item をそのまま handoff する。scan も output mutation もしない。
            Err(Either::Left(item))
        }

        item if item.starts_binary() => {
            let rhs_level = item.rhs_level();
            emit_binary_introducer(i.rb(), item);
            let rhs = expr(i.rb(), rhs_level)
                .unwrap_or_else(|| recover_missing_rhs(i.rb()));
            match rhs {
                Ok(()) => scan_tail_after_accept(i, level),
                Err(Either::Left(next_item)) => tail(i, level, next_item),
                Err(Either::Right(end)) => Err(Either::Right(end)),
            }
        }

        item if item.is_ml_nud() => {
            let nud = item.ml_nud().clone();
            begin_ml_application(i.rb(), item);
            let rhs = expr_from_scanned_nud_after_accept(i.rb(), level, nud);
            finish_ml_application(i.rb());
            match rhs {
                Ok(()) => scan_tail_after_accept(i, level),
                Err(Either::Left(next_item)) => tail(i, level, next_item),
                Err(Either::Right(end)) => Err(Either::Right(end)),
            }
        }

        item => {
            // field/path/call/index/suffix などは、それぞれの owner が直接
            // emit/recover し、total に完了してから自分で次を scan する。
            finish_accepted_tail(i.rb(), level, item);
            scan_tail_after_accept(i, level)
        }
    }
}

fn prefix_after_accept(mut i: In<&str, R, S>, outer_level: Level, prefix: Prefix) -> TailExit {
    begin_prefix(i.rb(), &prefix);
    let rhs = expr_from_prefix_after_accept(i.rb(), &prefix)
        .unwrap_or_else(|| recover_missing_prefix_rhs(i.rb()));
    finish_prefix(i.rb());
    match rhs {
        Ok(()) => scan_tail_after_accept(i, outer_level),
        Err(Either::Left(next_item)) => tail(i, outer_level, next_item),
        Err(Either::Right(end)) => Err(Either::Right(end)),
    }
}
```

`TailExit` は user-specified な局所 handoff の説明名であり、新しい public wrapper type
の提案ではない。外側の `Option` は entry での effect-free な不受理だけを表す。受理後に
`None` になった場合は、その場で既存 owner の typed recovery を emit して total な
`TailExit` に変える。従って `recover_missing_rhs` は fallback parser でも action materializer
でもなく、すでに受理した binary owner の recovery continuation である。

`tail_reads` は `Item` を消費せず、level、ML mode、delimiter/stop/layout frame を見る pure な
判定である。ここで `Err(Left(item))` を返す時、outer tail は scanner を呼び直さず同じ item を
受け取る。`Ok(())` は cache された次 token を表さない。次 item がまだ scan されていないため、
呼び出し側が `scan_tail_after_accept` を実行するという通常完了だけを表す。

重要な場合分けは次のとおりである。

| 状況 | `TailExit` | 次に動く owner と必須の動作 |
| --- | --- | --- |
| 子が通常完了 | `Ok(())` | 外側 tail が自分で次を scan する |
| 子が読めない item を返す | `Err(Left(item))` | 外側 tail が再 scan なしに同じ item を読む |
| 子が close/stop/dedent/EOF boundary に達する | `Err(Right(end))` | caller expression owner へ正確な `End` を伝播する |
| field/path/call/index/suffix を受理した | owner ごとの total な通常完了または `End` | 同じ tail が次を scan する。terminal/outer form は既存契約どおり `End` を返してよい |
| `MlNud` を含む ML application を受理した | 子の三結果をそのまま分岐 | `Ok(())` なら同じ tail が scan、item なら同じ item を読む、`End` なら伝播する |

ML application の三分岐は意図的である。例外的 fallback ではない。例えば `f x y` では
`x` の `Ok(())` 後に囲む tail が `y` を scan する。`f x: rhs` では `x` が返した scan 済み
colon を囲む tail がそのまま読む。Yulang2 の `ExprLedTag::MlNud` と同じである。

prefix も同じ三分岐に従う。prefix RHS の `Ok(())` なら外側 tail が scan を続け、未読 item
なら prefix は自分の Rowan node を閉じてから正確な item を外側 tail へ渡し、`End` なら
伝播する。item を捨てたり、式 scan を最初からやり直したりしない。

## 5. Rowan と recovery の所有権

直接 emit とは、受理した grammar owner が自分の start/token/finish と typed recovery emit を
持つ、という意味だけである。Rowan を expression return value に入れることでも、output を
global transaction にすることでもない。

- core/prefix/tail owner は、受理した部分の既存 CST node を自分で begin/close する。
- 未読 `Item` を返す branch は、その item に対して何も emit していない。それ以前に受理した
  operand は通常どおり emit 済みである。
- introducer を受理した後の malformed operand は、その introducer の既存 typed owner rule
  で recover する。後段の generic materialization pass ではない。
- boundary と caller-owned close は、元の leading trivia とともに owner へ戻す。recovery が
  それらを消してはならない。

平坦な `OperatorChain` は expression tail order の唯一の AST product である。binding level の
変更は recursive control flow を変えられるが、precedence-shaped AST/CST product を作ったり、
chain item を並べ替えたりしてはならない。

## 6. 移行計画の訂正

Gate 2 の authority と acceptance template は保持する。root-range derivation、pilot の
transitive `ParseLocal` dependency cone の field map、speculative expectation と diagnostic
allocation の `R` 配置、committed Rowan/recovery publication の `S` 配置、current-item
completion、byte-exact EOF/logical position control、generic recovery node/record identity、
old/new crossing 禁止は、全て従来どおり Gate 2 の必須要件である。

置き換えるのは「generic execution shell と generic tail driver を先に作る」という実装形だけで
ある。isolated pilot は、上の Gate 2 要件を満たす最小の**直接** `expr`/`tail` closure とする。
含めるのは item completion、一つの core、少なくとも一つの読める二項 tail、一つの
unread-at-level handback、一つの scan-again tail（ML application を含む）、一つの expression
boundary である。public dispatch edge も legacy fallback も持たない。

Gate 3 に割り当て済みの E2/E3 recovery matrix と borrowed outer-call close evidence は Gate 3
に残す。Gate 4 の Expression cells と RB-E も元の gate に残す。この追補はそれらを Gate 2 の
pilot witness だけで閉じたことにせず、共通 acceptance template を弱めない。

pilot が次の gate へ進む前に、focused evidence は少なくとも次を示さなければならない。

1. root pointer から導いた range、UTF-8/CRLF、EOF-after-trivia、logical position が Gate 2 の
   正確な契約を満たす。
2. pilot dependency cone の全 `ParseLocal` field が immutable context、explicit frame、`R`、
   `S`、または no-reader witness を持つ eliminated のいずれか一つに割り当てられる。
3. 子が低い level の unread item を返し、外側 tail が再 scan なしに同一 identity/trivia/extent
   の item を消費する。
4. binary、ML application、prefix の各々で、`Ok(())` は outer scan、`Err(Left(item))` は
   same-item handoff、`Err(Right(end))` は boundary propagation になる。
5. non-binary tail を受理した tail が、次の scan を自分で行う。
6. adjacency、許された spaced continuation、same-level newline/dedent の `(` control が、call、
   ML NUD、boundary をそれぞれ opener の消費有無も含めて正しく分ける。
7. `Err(Left(item))` により入力 cursor、selected `R` state、expectation、diagnostic allocator、
   persistent recovery state、`IsCut`、explicit frame、`S`/committed publication が tail-entry の
   値に保たれる。これは structural non-mutation か完全 checkpoint rollback のいずれかで示す。
8. 受理後の malformed core/RHS/tail が `None` を返さず、既存 owner の typed recovery と total な
   handoff へ変換される。generic recovery node/record の範囲・identity・source order も、元の
   acceptance template どおり一致する。
9. pilot が emit する CST と source-order `OperatorChain` が、選んだ frozen observation と
   一致する。
10. malformed binary/prefix/ML operand の recovery が child `level`/mode を保持し、直後の
    lower-level item を同一 identity の `Err(Left(item))` として outer tail へ戻す。
11. trivia boundary の resume は wrong cursor、still-dedent frame、wrong close/stop token、
    owner capability 欠如を拒否し、正しい再開だけが同じ item identity/trivia/extent/logical
    position で payload を完成する。

止めた未コミット `rewrite/` files は、却下されたトポロジーの証拠であり、修理対象の土台では
ない。この Draft のレビュー中は触らない。承認後の Gate 2 実装だけが、その内容を置換できる。

## 7. 明示的に決めないこと

この Draft は次を意図的に決めない。

- 各 grammar boundary で `Option`、`Result`、`Either<Item, End>` をどう Rust alias にするか
- 個別の expression recovery recipe、delimiter frame、stop set、layout rule
- expression pilot より後の移行順

これらは既存の recovery/specification contract が決めるか、直接 pilot が実際の gap を出した時に
別途レビューする。handoff protocol を単純化するために勝手に決めてはならない。
