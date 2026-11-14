# Cycle184: 主張と量化範囲

以下はすべて roles/registry/root/state など明示引数を任意に取った主張。正確な92定理の名前・全前提・結論は `notes/verification/cycle184/theorem-signatures.md`、推論済み暗黙引数を含む型は `public-types.txt` に列挙した。補助定理数を一般フィールド完了数に換算しない。

- `RawSeparation184.ground_raw_separate`: 任意の元のground境界Gの到達可能状態とpurpose≥7のfresh名について、rawSourcesに属さない。外部の「分離している」という仮定はない。`raw_assign_preserves`: その名前の任意の有限集合に任意の値を割り当ててもraw Modelsを保存する。centered ledgerの保存までは結論でない。
- `GroundSiteCoherence184.ground_site_unique`: Checked registryとG到達可能状態で、登録された任意の二つのSiteのoccurrenceが等しければSite全体が等しい。identityだけの一致をoccurrence一致に置き換えてはいない。
- `OverlapProvenance184`: 任意のpurpose8名がG到達状態のfullSourcesに属するなら、その名を与える登録済み実際のbinderが存在する。証人はモデルを量化する前に選べる。`OverlapIdentity184`はその登録元のinvocation identity・declaration ID・名前・位置0・非output/非pointも同定する。
- `GroundCandidateReadback184`: 登録済み歴史plan、現在候補、Checked、G到達、入力登録、同occurrence/同declaration、head実使用などの全前提の下で、全centeredモデルで候補originを歴史binderに読み戻せる。歴史planの存在や同occurrenceを任意の候補へ一般化しない。
- `GroundLedgerExtension184`: purpose≥7有限名の割当でledger値を保持すれば、G到達状態のcentered Modelsを保存。raw保存は内部で導出する。
- `GroundHistoricalExtension184`: 既存centeredモデル、purpose8有限名、fullSourcesへのendpoint/originリンクの下で、有限引数拡張の必要十分条件に現れる歴史証人を到達可能性から供給する。candidateと歴史binderのSameは一般には残る。
- `RootOverlap184.candidate_root_overlap`: Checked、G到達、登録入力を持つ現在root候補、可視declaration、非output/非pointの実head-use、fullSources overlapを持つ任意の対象に対して、すべてのcenteredモデルで候補originと候補binderはSame。歴史planや希望するSameを仮定しない。
- `RootExtension184.root_extension_iff`: 上記root候補の任意の有限個の実head-useを選び、そのendpoint/originをfullSourcesにリンクする。任意の既存centeredモデルについて、旧fullSources値と旧Modelsを保持し選択引数のHoldsを満たす拡張が存在することと、各観測の存在・すべての観測のFits・同一binderの観測間整合性とは同値。歴史overlap条件は導出済み。候補plan全体のJoint、子の再帰、一般EvidenceNodeは結論でない。

その他のGeneratedSupport/SiteSupport/SiteSeparation/GroundSiteSupport/CenterCoherence/ChildCoherence/HeadTransport/CandidateCoverageの定理は、以上の証明に必要な構造支持・登録・捕捉・head読戻しを記述する。量化と前提を省いた別の一般定理を主張しない。

## 13定義項目と証明フィールドの区別

| 定義項目 | 状態 |
|---|---|
| Checked | 一般nominal registryの定義あり |
| Models | 一般centered状態の定義あり |
| Step | 一般centered更新の定義あり |
| Stable | 一般定義あり |
| Generated | 一般定義あり |
| RootPending | 一般定義あり |
| RootK2 | 一般定義あり |
| CandidateK2 | 一般定義あり |
| InspectionPending | 一般定義あり |
| Survivor | 一般定義あり |
| Evidence | 一般定義あり、EvidenceNode未証明 |
| Reorders | 一般定義あり |
| DictionaryEquivalent | 一般定義あり |

これは言語全体の網羅性や正しさの証明状況ではなく、Gが参照する定義の存在の棚卸し。元GのV5骨格は14証明フィールド中10本が既存証明、4本Remaining。今回閉じた一般フィールドは0。I32の移行先V6/WFの証明数と混同しない。
