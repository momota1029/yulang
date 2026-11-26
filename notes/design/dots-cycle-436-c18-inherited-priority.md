# C436 / I-79: 旧診断と新しい completed-native leaf の両立境界

`integration/m1-final@a6c7ed28…` の **実ファイルにある** `R17.named426.other` の和を点検した。新しい葉が旧検査器を優先順で横取りしないだけでは、宣言的な旧診断との重複を排除したことにならない。次の狭い lane では、旧分類から生じる競合を**形から**取り除ける。これを新しい言語上の拒否規則や `¬ OldClassifies` を入力する predicate としては実装しない。

新枝の同じ (s,q) には元の入力が一つ、visible list が `[row]`、literal head が `[.app key [.var binder]]`、実 declaration の requirements は空、元の要求された出力は空。予定するモデルなしの source rule は `RootCycle s q` の否定も持つ。どれもユーザー報告とは独立に元データを調べる。`no authored lower` はこの coverage の切り出しで、入力を拒否する一般意味ではない。

| 古い枝 | その一次ソース（blob） | 新しい singleton leaf との矛盾 |
|---|---|---|
| R0/R1、R2・R3 は同じ `other` | `RuleUnionNormal407` `3828f80d…`; `ListPriority410` `ce96d24c…`; `NamedLeaf409` `7c9de0e0…`; `InvariantList410` `120cd30c…`; `WhereListRule411` `2a8ca8f3…` | 旧 ambiguity は visible が最低 2 行。authored/completed native K2 は normalized `.app` の実 rigid 子へ入る判定だが、同じ declaration 上の子は `.var binder`。C410 の private 証明の前提は実際には `only`, `named` だけだった。invariant の証拠を捏造せず、新 module でこの二つを一般化して再証明する。 |
| R4 の record K2 | `RecordRule412` `6b8a1ed3…`: `ActualRecordField` | `field.only` から同じ declaration。 `field.clauseAt` が requirements 一つを求め、空と矛盾。record/nominal translate の対立を実装するまでもない。 |
| R5 の nested/mixed K2 | `MixedRecordRule413` `e6bef223…`: `MixedRecordRejection.rivalsExist` | visible が少なくとも 2 行。 |
| R6 の open-tail pending、R7 と R8 は追加診断なし | `OpenTailRule414` `0104ed60…`; `ClosedResidualRule415` `84264754…`; `PlainMergedRule416` `22f72732…` | `candidate.exactVisible` から同じ declaration。 `candidate.requirements` に実 tail 子一つが必要で空と矛盾。 |
| R9 の plain/ground ambiguity、R10–R12 は追加診断なし | `X6AmbiguousRule417` `70dfa6e3…`; `RigidRivalRule418` `16f205ca…`; `ExplicitPickRule419` `1ec64acb…`; `RoleDefaultRule420` `a99a546d…` | `ordered` の両枝とも visible が 2 行。 |
| R13 の repeated-center conflict、R14–R16 は追加診断なし | `RepeatedCentersRule421` `b588fd80…`; `RepeatedCentersSource421` `f4d1055f…`; `ProjectedRule426` `750abcee…`; `StructuralWhereRule431` `e3d303c9…`; `StructuralWhereAssociatedLocal432` `4385de4e…` | `conflict.choice.originalArgs` は元入力が 2 個で、1 個に矛盾。R14 の旧 endpoint は正例追加だけ。 |
| R17 の未完了 where pending | `PendingAssociatedSource434` `5cb47c89…`: `OriginalPendingWhere434.childDemandOut` | 同じ q の元の出力が必ず一つ、新しい leaf の空に矛盾。別のユーザー報告や別モデルの存在を仮定しない。旧 episode の `onlySeed` や mode に反証を頼らない。 |

形式化する補題（未コンパイル）: `no_inherited_local_other436 {s q row arg key binder} (one : visible s.core q = [row]) (head : row.head = [.app key [.var binder]]) (args : q.demand.arguments = [arg]) (noWhere : row.requirements = []) (noOutputs : q.demand.outputs = []) : ∀ v needs, ¬ PendingAssociated434.R17.named426.other s q v needs`。ここには `RootCycle` は仮定されない。従って wrapper で古い root K2 が `false` になる事故を起こさない。新しい選択そのものに rootSafe を入れ、旧 `root_k2_is_rejected_for_every_primitive_system` を旧枝で使う。選択の正の同じ報告を示すには新しい一つの枝の実 readback と固定先の意味を別途要する。

旧**選択**の不成立は上表とは別。C435 の旧 named/head と旧 projected/record についての inversion を適用するため、新 source の「authored route から読む独立した下端はない」が input facts として必要。これは例えば Origins367 の `actual_route_iff` を使って肯定的に読み取れる否定条件であり、旧 checker の失敗からは言わない。
