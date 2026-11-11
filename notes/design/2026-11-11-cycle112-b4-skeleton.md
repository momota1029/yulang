# B4 skeleton の復旧と分解（cycle112）

状態: Draft。I-16 に従う。一般 B4 の完成宣言ではない。

## 既存 target と、先に露出させる境界

`Main.lean` の `Yulang.B4Target.Statement` は既に承認済みの五項を全量化している。
ただし source carrier と独立局所判断は `SourceBoundary`、実入口は `Executor` の未接続のパラメータ。
これを狭い settled carrier で満たして全言語の定理とは呼ばない。

2026-11-09 の回答では、唯一候補の子が非成功なら未完成の診断 tree を保持し、
四方向の最終言語分類への写像は後へ遅延する。既存 target の全域な四方向 Executor と
全子成功だけの selected 規則には、この境界が残る。既存の child-failure fold は、
親に新しい拒否理由を増やすため代用しない。

## 分解の方針

進行一段の model 保存と有限到達から最終 model 包含を導く。最終状態の無遷移から
root と全生成需要の安定へつなぐ。独立局所判断と有限診断 tree を先に扱い、
完全辞書を持たない tree の処理を暗黙に決めない。辞書の健全性は一つの head と
全 where 証拠を組み立てる局所規則から木の帰納で得る。

最終分類の全域性を結論そのもののフィールドに隠す構造体は作らない。
ソース義務の identity を落とす単なる辞書 key の multiset 比較も使わない。
P0 の target を具体化できない境界は独立した阻害定理とともに報告し、P1 では
既存 settled fragment の lossless tree と根の拒否理由の正確な iff を先に閉じる。

## 今回の運用境界

cycle111 の公開操作の結果が未確定で、writer ownership も戻っていない。
親の許可によりソースだけを独立ディレクトリへコピーし、元 checkout・公開 branch は
変更しない。ビルドキャッシュは読み取り再利用し、新しい出力は別の小さな overlay に置く。

## P2: whereなし単一scalar宣言の全モデル証拠

最小断片は既存ordinary materializerが表す int/str、一引数、whereなし、可視宣言1個。
入力は任意の `State n` と実receiver slot、role/impl identity。実ordinary solverの
整合性検査とpaired-bound materializationを先に行い、既存 `RoleDictionaries.elaborate`
から実際の辞書を作る。roleの一意性からreceiverを逆算しない。

独立の辞書意味は、実宣言のhead scalarにreceiverのモデル上の値が同値で、
辞書のdecl identityと全where子列（この断片は空）が一致すること。
任意の旧状態・任意の返却planについて成功 iff `Models` と実materializationと実leaf辞書。
さらに、その任意の成功について、旧状態の**すべてのCommonモデル**に証拠が成り立つ。
method bodyの実行意味や一般のassociated equationsは対象外。これは12義務の
`evidenceNode` を本当のordinary source slotに接続する最小の部分実装であり、
一般のフィールド全体を閉じたとは数えない。

## P3: 可視implの列順だけを変更する

P1 の全 tree exactness とP2の最小全モデル証拠のあと、`canonicalLocalOrder` の
可視宣言順の部分へ進む。対象は同じchecked settled宣言の列のPermutation。
scanの結果もPermutationになり、K2/pendingの有無・survivor数・唯一候補の
実宣言/捕捉payloadは変わらない。その一需要のfrontier一致から、Paterson下降に
沿って全診断treeのliteral equalityを得る。全子を保持するので辞書の有無も失わない。
where列そのものの並べ替え・source義務の正準化は未対象であり、単なるkeyの
multisetを辞書同値と定義しない。

## Target の忠実性レビューで露出した阻害

### 1. 古い全域four-way targetと、承認済み未完成tree

`rejected_child_has_no_completed_readback` は、selected親の子列にrejectedがあれば、
その親を旧targetの四方向結果へ意味を変えずに読み戻す `Completed` が存在しないことを示す。
これは既に回答済みの `2026-11-08-cycle4-b4-classification-boundary.md` 境界1を
再質問するものではない。`CommonRoleSettledExamples.x9_where_tree` は実resolverが
`selected 3 [rejected]` を返す具体例。新しいroot拒否定理は、その親にrootの三理由が
ないことも検証する。子failureを根へ伝播する既存summaryを完成の代用品にはしない。

### 2. 古いRejectReasonの候補ゼロにはpendingの除外がない

`Main.lean` の `B4Target.RejectReason` は
`RootK2 ∨ CandidateK2 ∨ (∀ key children, ¬ Survivor ...)`。
`Classify.pending` の前提は `RootPending` だけであり、両者の排他性は定義されていない。
`pending_empty_survivors_obstruction` は、最終stateで `RootPending` と候補ゼロが
同時成立する一つの入力があれば、どんなexecutorでも旧 `B4Statement` のexactnessが
成立しないことを証明する。`bridges_obstructed_by_pending_empty` はその場合の12義務も
同時には成立しないことを示す。

根拠はspec/06-roles.md §6.3の型未解決は保留し、型の決まった需要だけで可視implを
検査する規則、承認済みB4草稿の「下界の頭が未解決ならpending」、既存settled Local。
空の可視集合で未知receiverを持つ例では、actual settled frontierはpendingであり、
実宣言由来というorigin条件を満たすsurvivorは存在し得ない。

必要なのは証明の仮定を増やしてこの入力を排除することではなく、targetの
「候補ゼロ」を検査が実際に始まったケースに限定することと、承認済みのlossless tree
を結果carrierへ反映すること。元の定義は変更せず、監督役のtargetレビューへ渡す。
新しい言語意味論は選択していない。今回の `b4_of_bridges` は旧五項への正しい条件付き
合成だが、これらの阻害を無視して一般sourceの完成可能な最終targetとは呼ばない。
