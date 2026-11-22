# Cycle 354: exact typed associated-output release and child receipts

本周は、実際の associated 出力を番地付きで release し、コンパイラが生成した非点子で読み直す証人を検証した。同じ payload の別番地は代用できない。実際の子が次の固定出力 10 に同じ全 payload を再出力するところまで確認したが、10 の release と孫への伝達、全体の検査器健全性はまだ示していない。

## Scope

- Owner source: `integration/m1-final` `cf2a819e4bbf15fb84de8e27860ab372c7a5bbbd`; active `I-63`, with §6.3 variance and whole merged payload, §10 independent certificate boundary, and I-57 frozen files. Prior verified work `895d3e78b48f4559b66909e3693f3d011cec62e5`.
- Actual start 2026-11-22T21:36:39.324Z after recovery/handoff; this slot had a fixed 22:25Z cutoff. Only `work/dots-main` was updated. This cycle implements one typed-output slice; it does not reconstruct old solver evidence, revive old Local, prove termination, or equate the typed fragment with the C334/C337 classifier.

## Verified positive route and exact rejection boundaries

1. The emitter independently reruns the selected declaration's actual `lookup` at the requested output name, recovers the explicit authored `variant tag (Box(input binder))`, checks declaration kind and unary covariance, and uses `portNames`' actual capture. It retains actual ordinary compiler `preparation` and `whereBatch`, exact ordered demands, and the mixed ordered write list. A typed row is a companion view, not a Common invariant/ordinary equation. With only ordinary items, the old ordinary `fixedBatch` yields the same batch; a genuinely new typed item cannot be built by that old route. A role default is not admitted as an explicit typed write.
2. The receiving certificate uses a producer stamp and independently released (authored path, role, declaration id, active version, output ordinal, associated name, fixed target). It reruns the actual writer, selects the exact compiler-emitted index, appends only the exact released typed row to independently written source rows, and reads the actual nonpoint center at that physical name. The exact writer/receiver output equations and endpoint bounds hold in the same supplied ordinary model, and the typed view at the actual center contains the whole merged arms. The typed view carries the declared Box name; the ordinary variable still denotes the payload.
3. The actual two-child slice emitted typed writes at target 5 and target 9 with equal payload, then the ordinary output at 6. The children are independently authored at occurrence paths [4,0] and [4,1]; their actual demands have nonpoint centers `(32,9,33)` and `(34,9,35)`. The exact ordered dictionary is `92[93,94]`. Even the separately authorized earlier write at 5 cannot stand for 9. Missing release, stale version/path, substituted nominal name or write/root site, authoring a produced row, missing/reordered children, reordered fixed writes, and altered report order were tested. The positive result is nonvacuous: a particular ordinary model and the actual finite output/evidence were checked by Lean.
4. One compatible independently authored/released rows table gives one valuation for all the verified siblings' typed intervals at once, in addition to their same ordinary model. Per-child acceptance does not imply this compatibility. The concrete extended sibling pair both read successfully but independently write conflicting immutable author data at unused root 44; in the same ordinary model its payloads are Int and Bool, so no valuation can satisfy the two typed-table entries. This pair is a certificate-scope counterexample, not a new language-level rejection rule. Literal root/shape agreement is a checked *sufficient* compatibility condition, not a general semantic completeness result.
5. A checked later child can itself emit a new typed item without implicitly releasing it. In the actual compiled fixture, the root emits the role-3 demand (32,9,33) with associated name 4 and fixed target 10. The nonpoint child consumes the released type at 9, reruns actual preparation and where, and emits the declared typed Box at 10 with the same whole arms. The same-model theorem checks the actual trace occurrence and payload; the reproducible example checks an ordinary model, the exact write, and that the receiving typed scope still has no entry at 10. It does not authorize a grandchild to consume 10; that requires a separate release and certificate. See [the next-step design](../design/dots-cycle-354-next-typed-release.md).

## Next path to verify

A grandchild at the new target must come from a real emitted demand, not from reusing an output name as a bare input binder. For the checked ordinary compiler, `GeneralDeclarativeProducedNames325.exact_clause_input` restricts a bare clause argument to an actual head binder; compound argument names come from the independently prepared port. Its seed (`GeneralDeclarativeFreshWhere325.seed`) is after the existing state/protected names. In this fixture the parent where receipt already mentions ordinary 10; reusing it as a newly allocated compound center would require checking an explicit legal reuse route, not setting the wire to 10. Thus a fresh write at 10 is not evidence that the compiler has emitted a child centered at 10. A next useful fixture should compute that position through genuine allocated/author-backed provenance, or expose the exact compiler gap before changing any witness shape.

## Remaining

- **S1: 1 partially covered.** This scoped checked syntax/metadata/occurrence route has a genuine emitter and authorized consumer; no extraction from actual solver traces, no general accepted normal-form coverage or arbitrary-origin/recursive nominal carrier, and no default-to-typed conversion.
- **S2: 1 partially covered.** Same-current-model equations, ordered bounded dictionary and positive typed scopes close here, but no full latest grammar-to-classification theorem or generally recursive typed receipt forest. A single common typed valuation is proved only with checked compatibility; the old ordinary carrier is not the typed carrier.
- **C: 1 deferred.** No verdict completeness, no evaluation or termination claim, no Rust or whole Lean build claim.

## Lean の追加と主要定理

対象は `lean/Yulang/GeneralDeclarativeWitnessTyped*354.lean`（27本）。次の表記では共通接頭辞 `GeneralDeclarativeWitnessTyped` と末尾 `354` を省く。全ファイルと Git blob は [exact proof manifest](../verification/cycle354/exact-proof-manifest.txt)、個別の定理名と公理は六つの `standalone-*-axioms.log` に記録した。

- **Output / Packet / Release / Child / Fixture:** `Packet.exact` は、この有限検査が通った任意の writer と同一の最終状態を満たす任意のモデルについて、固定 target の並びと普通式が正しいことを示す。`Release.exact_ordinal` は、任意の通過した release の要求・行・番地が同じ実出力位置に対応することを示す。`Child.physical_target` は通過した任意の子の実中心が、この release の target そのものであることを示す。
- **Sound / Model / Tree / TreeFixture / LegacyCut:** `Sound.released_type_at_actual_center` と `Sound.both` は、任意の通過した子と普通モデルに対し、実中心・上下端・全 payload・親子の普通出力を検査する。`Model.inhabited` と `TreeFixture` は実例。`LegacyCut` は新しい typed 実例を旧普通コンパイラに偽装できないことを区別する。
- **Forest / ForestFixture / ForestModel / Source / SourceFixture / Scope:** `Forest.exact_model` は、任意の通過したこの有限一段 forest と任意の最終普通モデルについて、実 compiler 子の順で `All₂` の証拠、辞書、固定出力が揃うことを示す。`Source.not_solver_rows` は真正な raw author 行と順序を保持する。`Scope.exact_scope` は各通過子の位置とその実行時親・出力番地を固定する。`ForestModel.inhabited` は実際の二子がこの判定を満たす非空モデル。
- **Index / Joint / JointFixture / Overlap / Conservative:** `Index.typedAt_defined` は実書き込み列の任意の typed 出力番号が正確に引けること、`Joint.one_valuation` は同じ名前の定義が衝突しない全通過子について任意モデルに共通 typed valuation があることを示す。`Overlap.no_common_view_for_the_actual_accepted_pair` はこの補助条件を個別通過から導けない実例。`Conservative.no_ordinary_semantics_changed` は typed 出力がゼロなら旧 ordinary batch と一致する。
- **RangeWriter / RangeFixture / Reemit / ReemitFixture / ReemitPayload / ReemitModel:** `Reemit.scoped_write` と `ReemitPayload.exact_same_model` は任意の通過した release→非点子と任意最終モデルで、実際の固定出力順と子の同じ全 payload を保つ。`ReemitPayload.fresh_fixed_name_not_prematurely_published` の前提は、その固定名が子の現在の typed scope に未登録であること。`ReemitModel.actual_chain_same_model` は具体の出力10と実在モデル、`actual_reemission_not_published_in_consumer_scope` は未発行を検査した。

質問ノートは新規なし（未解決点は次の実 provenance の作業で、方言や意味論の選択は行っていない）。

## Independent verification

- Exact final science pin `5af319d8551105706ef37d6dc5dbd14b94b57f95`, verified after detached source-byte checkout. Warning-strict scoped Lean 4.35.0 checked 27 new source modules and 6 stand-alone audit files directly under `--trust=0`. 103 individually reported declarations and 114354 transitive declarations, only propext, Classical.choice and Quot.sound.
- Combined scoped Lake succeeded (3897 dependency jobs); exact frozen-skip diff gate passed; old barrel byte prefix and precisely 27 additive same-change imports verified. No whole Lean/barrel or Rust claim.
- Original frozen objects match by metadata, with neither file materialized: `97dd1cfaded3e3abc3fd8caa98a64843d6f7a3d9`, `9fd6842bcc00c5bc5c00a196d9ccb328c6b0c94a`. Evidence commit `eef1db20feb4424f4ef6afbbbca8d11ba5e10e75`; logs and exact source-blob manifest: [verification](../verification/cycle354/). A historical pre-fix child build log remains annotated and is not counted as passing.

Pre-handoff paths verified: 64; final handoff adds one report and updates the existing heartbeat.

Completion marked 2026-11-22T22:20:45.078Z at 44.10 minutes from recorded actual start, within this slot's absolute cutoff.
