# C436 / I-79: 同じ意味だが別の行を通さない fixture と公開 entry の契約

以下は a6c7ed28… の exact ソースで組み立てる**テスト計画**。C435 の test 形を強化した。実 checker の Lean 実行は無し。raw escape の一部だけ下記の数値計算で読み合わせた。

## 正例の元データ（既存の source builders を使う）

`GeneralDeclarativeWitnessVarianceFixtures357.source` (`c3bfa859…`) の body graph を `GeneralDeclarativeWitnessSparseVariance357.compile`。Box key=20 を catalogue/snapshot の両方に `⟨20,some ⟨[.type],20⟩,.unclassified⟩` (Rows291 `e263` ではなく `c` を付けず実 `GeneralSourceMetadataRows291` 下記 anchor) として置く。両 fallback は `.absent`。roles/declaration は `GeneralSourceMetadataBareBundle291.compile`（`da5b0c0a…`）の metadata builder、entry の例 `Cycle432I74StructuralWhereAssociatedEntry.lean`（`92e74fa7…`）と同じ builder。前例は invariant なので **variance metadata は流用しない**。

| 元の項 | 候補/要求（planned fixture） |
|---|---|
| Seed | actual declaration `⟨701,11,[.app 20 [.var 8]],[],[⟨80,6,.app 20 [.var 8]⟩],[]⟩`、actual role 11 arity 1 required associated 6; 元 request `⟨[101],⟨11,[point 10],[⟨6,40⟩]⟩⟩` |
| Observe | actual declaration `⟨702,22,[.app 20 [.var 9]],[],[],[]⟩`、actual role 22 arity 1 outputs empty; 元 request `⟨[202],⟨22,[⟨40,41,42⟩],[]⟩⟩` |
| original syntax | slot 10 issuer [101] Box(30); slot 41 issuer [202] Box(32); slot 42 independently authored Box(34); no routes to 40, no Origin at 40. No current value observations required. |
| exact B6 syntax | `.declaredApp 20 use names table (.cons (.valuePoint 8 rfl nonInvariant ()) .nil)` for the actual Seed source body, not `.valueInterval`. Explicit body key role 11/output6 and kind known from source.`atlas.read` uses full addressed request, declaration ordinal, output 0 and body as keys. |
| raw rows | #0 `40 = Box(30)` (actual retained typed RHS); #1 **decoy** `40 = Box(32)` (syntactically different name; assignment can satisfy both). Raw tyLe atoms 30≤30,30≤32,32≤34,30≤34,40≤41,41≤42. |

The `models` sanity check can be made nonvacuous: ordinary assignments at slots 10,40,41,42 are each `nominal 20 [.inl (.base .int)]`, the others are `.base .int`, row parts empty; `m.authoredValues` empty if Current.visible empty, `m.nativeSyntax` is defined precisely at actual origins. Both raw rows and all bounds are then reflexive after evaluating source types, including the decoy. This does **not** force distinct name 30 = 32 as a syntax equality. Construct a second fitting model by replacing `m.nativeSyntax 40` with `some` unrelated endpoint while leaving the rest; `Fits` and expected lower meaning remain unchanged. Cite `GeneralDeclarativeWitnessDeclaredState357.ModelsCurrent` and `State365.Fits` for precise model fields; old basis is `exact_episode_model_fits434` but not its whole state.

## Actual wire controls

- Positive producer uses raw row #0. Wrong existing row #1 must be rejected even though *this* model evaluates them identically. In Lean run both wires in **one exact same State**. No assumption that every duplicate syntactically equal raw row is invalid; this particular foil is literally different. `readOriginalOutput432` must reject before selection can use the wrong receipt.
- Mutate only producer occurrence, then only retained output ordinal (from 0 to 1), then only requested target (40 to other). Prove actual guard failure; the first can be caught by issuer or atlas while a separate fixture deliberately omits the original atlas value without changing any source input. If wire derives ordinal instead of storing it, apply the wrong-ordinal negative to the nested reader or address reflection; do not report a nonexistent public field.
- Mutate only the centered Origin locator to the actual upper Origin. Both show Box20 in the same fitting assignment; it is the wrong logical source/route for C and must not furnish the captured center. Keeping center absent is unsupported here; it is not a rejection or a reason to not try head election in the language.
- Mutate only dictionary key, root tree, or consumer result writes. The public result is `Check408.nullaryReport row` (root declaration id=702, no where/write). Even if the producer fact really was written, including its own write in the consumer result must return false.
- Raw K2 negative keeps both retained rows, then adds **only** row #2 `30 = 40`. Exact raw wire points to #0 for the nominal edge and `.forward 2` for the ordinary alias; two actual traces are rebuilt under the two different States (not casting traces). Existing raw helper `RootEscape410/ExactEscape410` tests K2 before facts guiding candidate exploration. Producer root 10 remains safe, consumer raw root 40 is cyclic. The original proposed old witness in *baseline without decoy* has `.forward 1`; index 2 here is obligatory. Do not claim a fitting finite model for this negative.

In a restricted numeric interpretation of `aliasRanks` and `exactShapeEscape` formulas from `ExactEscape410` (`0795621d…`), the positive producer+consumer certificates from C435 remain true with the added decoy; after #2 only the consumer check becomes false. The positive assignment evaluates both literal but different nominal rows identically; the same assignment does not fit #2. This small paper/JavaScript calculation is **not** a Lean/Rust execution, and the negative `RootCycle` itself still needs the actual old raw classifier witness/certification in Lean.

Fixture metadata anchors: `GeneralSourceMetadataRows291.Class.unclassified` maps to `primitiveValue=none`, `invariantFlag=false`; `GeneralDeclarativeWitnessConstructorModes357.readMode` must recompute the declared choice from the body graph. Verify metadata checks, actual B6 plan, new rule, dispatcher and same-model theorem independently. Old public Bool identity is by `rfl` on `previous` for every P/r/w, not an enumerated observation.
