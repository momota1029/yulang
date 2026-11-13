# Cycle 166: producer 定理の日本語索引

対象は新規3モジュールの公開定理42件。各節の名前空間を定理名の前に付ける。
型の厳密な引数・定義は対応する Lean ソース、監査対象一覧は
`lean/AuditCapturedProducer166.lean` を参照。

## 共通の固定対象と量化の範囲

`packet` は既存の captured-input 親、`producer` と `consumer` はその実際の子、
`candidate` は今回の producer packet。`refreshed` は親の Shared install と
5スロットへの refresh を終えた実際の状態で、まだ producer は未記録。
以下で「固定」としたものはこの具体例についての閉じた命題であり、任意の
registry や任意の親についての一般定理ではない。`Models` はモデル全体の
journal 条件、`Equivalent` は双方向の subtype を意味する。

## `Yulang.GeneralDictionarySharedCapturedPreparation`（5件）

1. `source_pool`: 任意の source identity が現在の snapshot の source 集合に属すなら、その identity は初期 source 集合または親 invocation の予約集合に属す。
2. `fresh`: 任意の invocation 番号について、snapshot は `Fresh`。その invocation の任意の allocation key が既存 source と衝突すれば、key は既に所有済みである。衝突不存在を追加仮定にはしない。
3. `linked`: 固定 producer の需要の全入力端点と全出力 target は現在 snapshot の source 集合に属す。
4. `prepared`: 固定 producer・terminal declaration・checked 証明に対し、refreshedContext 上で `Prepared` が成立する。metadata、linkage、Fresh、実際の位置 `(3,4)`、検査完了、要求準備、branch model を構成する。
5. `survivor`: 固定 producer は declaration の ID と candidate の実際の children を持つ `Survivor` である。

## `Yulang.GeneralDictionarySharedCapturedProducerEnabled`（19件）

この節の `model` は既存の int-tail witness、`depth` は lo/hi を1、その他の identity を `2-i` とする自然数値関数。

1. `model_depth`: 任意の identity `i` について witness の型値は `tower (depth i)` に等しい。
2. `no_feedback`: 任意の identity について、実際の refreshed journal に feedback K2 cycle は存在しない。
3. `no_raw`: 任意の snapshot スロットについて、raw K2 cycle は存在しない。モデル上の nominal 観測に沿って depth が真に減少することを使う。
4. `no_root`: 固定 producer の root K2 障害は実際の refreshed journal に存在しない。
5. `no_candidate`: 固定 producer の candidate K2 障害も存在しない。
6. `declaration_only`: 任意の declaration `d` が registry に可視で producer と同じ role なら、`d` は固定 terminal declaration に等しい。
7. `selected`: 実際の refreshed journal で producer の結果は固定 declaration ID と candidate.children の selected である。selected を仮定せず、準備・K2除外・候補一意性から導く。
8. `sites`: refreshed journal の sites は、root site、実際に Shared emitter が作った producer site、consumer site の3要素リストに等しい。
9. `packets`: refreshed journal の記録済み packet リストは親 packet だけの単元リストに等しい。
10. `alias_identity`: 任意の2つの identity が refreshed journal の `Alias` で関係付けられるなら、それらは等しい。この具体状態では alias edge は空である。
11. `producer_ne_root`: producer identity は root identity と異なる。
12. `producer_ne_consumer`: producer identity は consumer identity と異なる。
13. `site_identity`: 任意の記録済み site の occurrence identity が producer identity と等しいなら、その site は candidate.site に等しい。
14. `site_role`: 任意の記録済み site の occurrence role が producer role と等しいなら、その site は candidate.site に等しい。
15. `prior_unrelated`: 任意の記録済み prior packet に対し、producer identity とその prior site identity の間に Alias は成立しない。
16. `joint`: 固定 declaration ID に対し、実際の refreshed journal 上で producer の `Joint` が成立する。共通モデルと alias 関連 site の branch 条件を構成する。
17. `merges_closed`: candidate.site と同入力の任意の記録済み site は、feedback 側の判定において既に Alias 条件を満たす。
18. `legacy_merges_closed`: 同じ merge 閉包条件が legacy CycleSteps の同入力判定でも成立する。
19. `enabled`: 固定 candidate は実際の refreshed journal で `FeedbackSteps.Installable`。選択、整合的モデル、Joint、両 merge 条件を全て証明し、任意の selected outcome を仮定しない。Shared guard と実際の install は別モジュールである。

## `Yulang.GeneralDictionarySharedCapturedNovelty`（18件）

この節の `tower 0` は **string**、`tower (n+1)` は List を1段付けた型。
この節固有の `model` は lo/hi に List string、それ以外に `tower (2-i)` を割り当てる。
既存の int-tail witness とは別モデルである。

1. `model_old`: 任意の自然数 `i ≤ 2` について、model は初期 source 用の finiteModel と一致する。
2. `model_lo`: lo の型値は `tower 1`、すなわち List string に等しい。
3. `model_hi`: hi の型値も List string に等しい。
4. `model_target`: 親が割り当てた target の型値は `tower 0`、すなわち string に等しい。
5. `source_models`: この string-tail model は固定初期 source の全モデル条件を満たす。
6. `mid_seen`: 親の中間 origin `mid` から `tower 1` が観測される。
7. `captured_seen`: 親の capture origin から `tower 0` が観測される。
8. `mid_same`: 任意の型 `t` がこの model の mid から観測されるなら、`t` は `tower 1` と Equivalent である。
9. `captured_same`: 任意の型 `t` がこの model の capture origin から観測されるなら、`t` は `tower 0` と Equivalent である。
10. `private_models`: この model は親 packet.privateContext.state の全モデル条件を満たす。
11. `projections`: この model は初期 source と親 inspection report の ProjectionModels を満たす。
12. `lo_seen`: lo の nominal 第0引数から `tower 0` が観測される。
13. `hi_seen`: hi の nominal 第0引数からも `tower 0` が観測される。
14. `use_values`: 任意の use entry が親 namedSchema.variables に属すなら、name は0、mode は actual、origin の観測値が存在し、そこから観測される任意の型は `tower 0` と Equivalent である。
15. `outputs`: この model は親 packet の全 Outputs 条件を満たす。producer candidate の Outputs ではない。
16. `branch_models`: この model は初期 context・root・capturedProposal・位置 `(0,0)` について親の BranchModels を満たす。
17. `current_models`: この model は実際の refreshed journal の Models を満たす。初期モデルだけの反例ではなく、親 install と exact refresh 後まで成立する。
18. `not_committed`: 固定 candidate は実際の refreshed journal でまだ Committed ではない。もし committed ならこの string-tail current model にも producer の int 出力が要求され、string≤int となる矛盾を導く。

## 検証と未主張

3モジュールを直接 `lean --trust=0` で検証し、42公開定理の `#print axioms` を確認した。
依存公理は標準の `propext`、`Classical.choice`、`Quot.sound` の範囲。
この索引の定理だけで consumer の I26 trusted readiness、consumer install、一般の
Evidence bridge、V5全体の完了を主張しない。後続の実際の producer install と scalar
refresh は別の Resumption 定理を参照する。
