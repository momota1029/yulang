# Cycle 166: captured source の観測更新と trusted readiness の定理

対象は `GeneralDictionaryCapturedScalarRefresh` と
`GeneralDictionaryCapturedTrustedBoundary` の公開定理12個。
以下は可読な主張索引であり、厳密な型は各Lean宣言を正とする。
`Equivalent` は型値の相互部分型関係であり、source識別子の同一性ではない。

## 固定された例と二種類のモデル

ここで `candidate` は既存のcaptured producer packet、`packet` はその親packet、
`target` はproducerの割当済み出力source、`consumer` は同じ親のconsumerである。
`before = candidate.privateContext`。`scalarContext` はその5-slot状態のsource 2だけを
intとして観測する更新であり、他のnominal記述とメタデータを保存する。
`refreshed current` はcurrentのjournalを保存したままこのcontextへ再生成した状態。

- **current Models**: 現在の状態・全記録packet等を満たすモデル。
- **trusted-slice Models**: 元のsource状態と、指定したfactsだけを満たすモデル。

前者についての全称命題を、そのまま後者についての命題に読み替えない。
各定理はこの固定例について述べる。任意のproducer宣言への一般化ではない。

## GeneralDictionaryCapturedScalarRefresh（8定理）

1. **`raw_models`**: 任意のassignment `m`について、`m`が`before.state`のraw Modelsであり、
   `(m 2).1 ≃ int`なら、`m`は`scalarState`のraw Modelsである。
   journalの充足・到達可能性はこの定理の前提でも結論でもない。
2. **`newly_known`**: 固定された`before.state`ではsource 2はKnownではなく、
   固定された`scalarState`ではKnownである。
3. **`step`**: 任意のTracked `current`について、contextが`before`と等しく、
   **すべての**`current Models` `m`に対して`(m 2).1 ≃ int`なら、
   `current → refreshed current`は指定registry/rootの実際のShared行政refresh stepである。
4. **`models_exact`**: 上のcontext等式と全称scalar前提を満たす任意の`current`、
   任意のassignment `m`について、`Models (refreshed current).current m`と
   `Models current.current m`は同値である。新たなモデルの存在は単独では主張しない。
5. **`source_formed`**: 上と同じ任意の`current`と二つの前提に加え、`current`が
   指定registry/rootのSourceFormedなら、`refreshed current`もSourceFormedである。
6. **`packets_retained`**: 任意のTracked `current`について、`refreshed current`のpacket列は
   `current`のpacket列に等しい。context等式・scalar充足の前提は不要。
7. **`not_ordinary_extension`**: 固定された`before → scalarContext`は
   `GeneralDictionaryOrdinaryTrace.Extension`ではない。baseのordinary制約列と観測を
   実際に変えるため、ordinary-only transportとして扱えない。
8. **`consumer_raw_ready`**: 固定された`scalarState`で`consumer.demand`はRootPendingではない。
   これはraw既知性だけの結論であり、SharedのTrusted ReadyAt・DecisionGuard・consumer実行ではない。

補助的な公開定義 **`certificate`** は、任意の`current`について上記context等式と
全current Modelsに対するscalar前提から、`Refresh current.current scalarContext`を構成する。
目的の結論を仮定したものではないが、scalar前提を別途証明する義務は残る。

## GeneralDictionaryCapturedTrustedBoundary（4定理）

9. **`producer_output_int`**: 任意のassignment `m`について、
   `GeneralNominalPacketSupport.Outputs candidate m`なら`(m target).1 ≃ int`。
   producerの記録・settlement・実行・trusted fact化は前提から自動的には得られない。
10. **`ready_from_trusted_alias`**: 任意のTracked `state`、facts列、readbacks列、support列について、
    (a) current contextが`scalarContext`、(b) そのfacts/readbacksが`Trusted state`、
    (c) producerのoutputs factがそのfactsに属し、
    (d) **同じtrusted-slice Modelsのすべて**で`target ≃ source2`なら、
    本物の`GeneralNominalSharedSupport.ReadyAt state 2`が成り立つ。
    (d)を全current Modelsの命題に弱めることはできない。この定理は(d)の充足を証明しない。
11. **`alias_from_parent_output`**: 任意のTracked `state`、facts列、support列、assignment `m`について、
    親packetのoutputs factがfactsに属し、`m`がそのtrusted-slice Modelsを満たせば、
    `(m target).1 ≃ (m 2).1`。この定理自体はfactsがTrustedであることを要求も証明もしない。
12. **`parent_settlement_requires_consumer`**: 任意のsaturation `state`について、
    親packetが`PacketSettled state packet`なら、`Discharged state consumer`。
    親のsettlementでconsumerのreadinessを説明する経路は、既にconsumerのdischargeを必要とする。
    別の独立した説明が存在しないという不可能性定理ではない。

## この索引の結論範囲

全journalのscalar帰結によるexact refreshと、trusted説明に基づくconsumer再開は別の段階である。
独立したtrusted-slice上のaliasまたは別の正当な説明をまだ構成していないため、
この2モジュールからconsumer再開・一般飽和driver完成・surface処理系との一致を主張しない。
