# C400 I-71: B6 の型つき木を出力レシートに保持する

正本 `ad54e4f9703bc43501a605c58eec813f9fcf199f`、I-71 inbox `eb64179ca0cf4f86fe36697b824b58fac3ffec12`。C397 の質問への回答を確認。混在 `.declared` を平坦ベクタへ変換する義務はなくなった。C386 の内部形式が仕様だとは扱わない。言語の意味・判定・拒否、固定 `dictionary_sound`、S13bbba の文と分解は変更しない。

- 新しい受け取り口は、元の選定済み source frame（元宣言の位置、実 lexical capture、実の ordered where 要求）と、出力ごとの B6 の型つき RHS tree を別々に保持する。元出力の `Fin` と fixed target をレシートへ持ち、record/variant/join の中の nominal も木のまま。C398/C399 の `CompoundSourceRhs394` と `EventLogicalOutput399` は元 tree の保持・同一 slot での代入を機械検証済み。全称の意味証明のみから右辺の字面を再構成しない。
- 旧 event を単にラップして「旧 `.declared` receipt を一個入れて」と言うと混在形を表現したことにならない。新しい出力は旧 literal vector/旧 receipt を前提にしない pre-output frame から直接作る。既存の source selection と同じ event-data / guard は保持し、元要素の置換や未読セルの詰め直しはしない。
- 既に独立の local rule が認めた有限木・同じ ordered where 森の上で、同じ B6 source plan の作用を同じ選定・元の supplier・元出力番号・固定先と結ぶ。局所ルール群と all-model interpretation が全称で成り立つことは別で、補助 theorem を固定 S13bbba の完了に数えない。既存の ordinary と純粋 native も意味を削らず保持し、付随する既存直列形式との完全な同一性は不要。
- [I-71 が引用する型の権威](https://github.com/momota1029/yulang/blob/ad54e4f9703bc43501a605c58eec813f9fcf199f/spec/10-inference-core.md#L25) と [role §6.3](https://github.com/momota1029/yulang/blob/ad54e4f9703bc43501a605c58eec813f9fcf199f/spec/06-roles.md#L88-L95) に従い、木は B6 の入力、supplier/ordered child/fixed target への等式は B4。S13bbbb 側の新しい大域 retention はこの周の対象に増やさない。
