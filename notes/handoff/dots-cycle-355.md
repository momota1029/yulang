# Cycle 355: exact released sites and a fully authored finite typed spine

本周では、前周で再出力した10を正しい版・発生箇所・書き込み番号で release できることと、値が等しくても9を中心に本当に生成された孫を10に付け替えられないことを Lean で確認した。一方、根が実際に10を捕捉し、生成された子の中心が最初から10である別の例では、五節点・四つの別々の release を、原文入力から一つのモデルと一つの型付き表で検査した。

## 最新の範囲と実装

- Owner source: `integration/m1-final` `73d449534e5fdecca98140b4d6c1e4a72e77c38f`. I-63 unchanged, I-62 old Local out of scope, frozen I-57 preserved. Actual start 2026-11-22T22:33:37.309Z; absolute scheduled cutoff 23:25Z. Baseline C354 verified `a6459ce5827d95243551393e65c07f8f3c9387e1`. Direction and active source were reread before coding; the retained authorized cloud executor detached mid-cycle and was restored by normal reattachment without a permission change or unverified source publication.
The source landmarks for the two independent claims are [the approved whole covariant payload](https://github.com/momota1029/yulang/blob/73d449534e5fdecca98140b4d6c1e4a72e77c38f/spec/06-roles.md#L117-L123) and [the literal current argument center](https://github.com/momota1029/yulang/blob/73d449534e5fdecca98140b4d6c1e4a72e77c38f/spec/06-roles.md#L383). The release/evidence records are checker implementation data under I-63; no new language rule is inferred from the test or from its failure.

- `RangeRelease`: C354 nonpoint child role3/declaration93 at [4,0] can release its actual associated output name 4, write 0, fixed target 10, active version 8. The first parent’s authority, wrong child path/version/index/name/fixed site, and simultaneous conflicting versions fail this checker. This is separate from selecting a consuming child.
- **Original different-site cut.** Extend the exact source template with a real bare where request, not an invented demand. The compiler emits role4 at (50,9,51); an ordinary receipt for that real demand exists. The very state with both stages has the actual ordinary row `10 ← 9` and is inhabited. Every ordinary model of this state assigns equivalent values to 9 and 10. Nonetheless, for that checked chain and external release10 there is **no wire of any shape** accepted at the attempted grandchild by the scoped verifier. `RealAliasCut.witnessed_alias_never_repairs_the_actual_site` exhibits this nonempty case. The general reason is structural: the retained typed reader guarantees a residual join in the actual selected head, the accepted descent permits only a bare head binder, and the compiler’s named span construction preserves that binder’s literal captured name. A fortiori a release payload or ordinary model relation cannot select a different physical center. Independent broader lemma `WhereFresh.emitted_compound_not_any_protected_name`: in genuine ordinary preparation, a non-bare operand's allocated center is strictly above prior state/protected names. This is not a global impossibility of all future distinct-name certified transfers.
- **Independent same-site positive route.** The root's authored head is observed at 20 and independently captures literal payload name 10. All subsequent actual emitted child centers are 10; no 9 demand is relabeled. The real compiler generates the nonpoint grandchild (50,10,51), then an actual depth-five selected spine `92[93[94[95[96]]]]`. There are four exact grants in order, at paths [4], [4,0], [4,0,0], [4,0,0,0], each for its own role/declaration/version/write/name/target, independently authored. The reader checks these actual demand lists, exact fixed targets, diagnostic tree and dictionary, and literal author rows in independently supplied resolved source syntax, not solver rows and not a new textual/Rust parser. Wrong, stale, truncated, cross-path and reordered certificates fail this **scoped checker**. Same literal type at the same site is not a new permission to reassign a recorded fact or retarget an output.
- **Finite selected-spine theorem.** For any checked finite authored spine in this covariant nominal reader, and every supplied model of its exact declared final ordinary state, there is one compatible typed valuation for all checked nodes and traversed releases; every ordered ordinary output holds in the supplied common model and all mixed fixed targets are exact. Each authorized release preserves its independently authored exact associated body and the whole payload at the new child’s actual root. The recursive `Evidence` is indexed by the true authored root `Demand` and actual ordered `Dictionary`; there is a real model of the five-node example, not only a conditional proof about an uninhabited premise. Root input and release tables are independent of the reported output. Checked author order and actual occurrence paths are reconstructed exactly.
- **Same metadata, different old premises.** Existing C334 `Coverage` cannot hold for the actual visible declared unary covariant constructor: the original carrier requires primitive or invariant, both absent under the real explicit metadata. Where there is a genuine emitted child, old registry `Checked` also fails at the selected declaration's `CountsCovered` premise for the normalized residual join. Actual `Declared` is still shown separately. This scoped typed `Evidence` is a new carrier-specific ordered kernel, not a claim to apply the unchanged C334/C337 theorem to unsupported author syntax. Their results were neither changed nor invalidated.

The actual ordered external release ledger in the positive fixture is:

| Author path | Role / declaration | Active version | Write ordinal | Output name → target |
| --- | --- | --- | --- | --- |
| [4] | 1 / 92 | 7 | 1 | 1 → 10 |
| [4,0] | 3 / 93 | 8 | 0 | 4 → 10 |
| [4,0,0] | 4 / 94 | 9 | 0 | 7 → 10 |
| [4,0,0,0] | 5 / 95 | 10 | 0 | 8 → 10 |

The root still emits its other fixed outputs in order (name 0 → 5 and name 2 → 6). Neither is a granted traversed edge here. The terminal declaration 96 emits no children and is checked as a real leaf, not truncated by the wire.

## 追加 Lean ファイルと主要な定理

共通接頭辞 `GeneralDeclarativeWitness` と末尾 `355` を省略。全追加ファイル・blob は [exact proof manifest](../verification/cycle355/exact-proof-manifest.txt)、全個別定理名とその公理は同ディレクトリの六つの `standalone-*-axioms.log`。

- **RangeRelease / RangeReleaseFixture / RangeCut / RetainedCut:** 任意の通過 release が同じ実書き込み位置と独立の active authority に由来する。任意の保持型検査で実子が生成されると、その全引数の中心は実捕捉名に固定。名前番号を9に固定した仮定は不要。
- **Grandchild / GrandchildSeed / GrandchildFixture / GrandchildContinuity / GrandchildTree / GrandchildTreeFixture / GrandchildModel:** 通過する任意の同一名三段木について全適合モデルで上下端・実中心・書き込みと辞書を検査。互換表なら同じ typed valuation。前周系の実子と字面10の別例を混同しない実行例。
- **SpineNode / NominalSpine / NominalSpineWhole / SpineLedger / TypedEvidence / CoverageBoundary / OldPremises / WhereFresh:** 任意の有限の実生成単一子列から順序付き Evidence を組み立て、compiled 固定出力・同一モデル・原文の release 順・実位置の深さを保存。型のモデル値が同じことだけでは物理名を変えられない。旧前提の失敗と実 `Declared` を区別。
- **SpineDeepSeed / SpineDeepFixture / SpineDeepModel / SpineFront / SpineFrontFixture / SpineFrontModel / SpineFrontLedger:** コンパイラの計算から五段の実例を構成し、任意の成功入力について原文付きの全根から決定木・辞書・出力を照合。独立入力行の変造、旧版、根の出力順、途中節点欠落などが検査を通らない実例。
- **SpineEdgeMeaning / SpineKeysFixture / RealAliasCut:** 任意の通過する全根証人と適合モデルで、一つの typed valuation が全再帰 Evidence と全実 release の本文・記録先・名義・合流 payload を支持。実例で四つの鍵と順を明示。旧9→10源の同モデルの等価からどんな wire でも別実中心を作れない最小証明。

## I-63 残数

- **S1 1群、部分済み:** 独立入力の解決済み原文構文・名義・現在の版付き発行・有限単一子経路を検査。任意有限の順序付き複数子混在、別名の認可済み由来、言語全体の入力構文は未接続。
- **S2 1群、部分済み:** typed 専用実範囲で、全根の再帰辞書／出力／外部作者と同一モデルの健全性を示した。一般の C334/I-61 証人付き分類全体との橋は未達。旧 carrier の前提を読み替えない。
- **C 1群、後回し:** 任意の仕様受理をカバーする証人生成、旧実行器からの証拠抽出、停止性、Rust/全体ビルドは示していない。

次の最小の独立課題は、実 compiler の同じ子リストにいる typed 片側と ordinary C337 片側を、同じ現在モデルで順を保って接続すること。[次の作業の設計](../design/dots-cycle-355-next-mixed-evidence.md)。普通側で同じ番号10が現れても、それだけで Box 全体を普通の payload と読む証拠にはならない。別の ordinary 観測経路、または明示的に author-backed な payload 投影が必要。旧 `Coverage` は全宣言を量化するため、typed root だけ取り除いて別の typed 子を残す射影では使えない。ordinary 枝を選んだ実出力に対して必要な source scope を先に固定し、削った型付き役割を ordinary 枝が参照しないことを確かめる。今回は未指定の言語判断を追加せず、質問ノートは作成しなかった。

## 検証と公開

- Exact final science pin `1ad63c02954f651f188c33c2dad2925984f4e666`, verified after detached source-byte checkout. Warning-strict scoped Lean 4.35.0 checked 29 new source modules and 6 stand-alone audit files directly under `--trust=0`. 118 individually reported declarations and 115148 transitive declarations, only propext, Classical.choice and Quot.sound.
- Combined scoped Lake succeeded (3922 dependency jobs); exact frozen-skip diff gate passed; old barrel byte prefix and precisely 29 additive same-change imports verified. No whole Lean/barrel or Rust claim.
- Original frozen objects match by metadata, with neither file materialized: `97dd1cfaded3e3abc3fd8caa98a64843d6f7a3d9`, `9fd6842bcc00c5bc5c00a196d9ccb328c6b0c94a`. Evidence commit `48c177cb80df4b63507641beb6a6af4c596634c6`; logs and exact source-blob manifest: [verification](../verification/cycle355/). Only successful scoped logs are counted; the final detached logs are the evidence for the exact tree.

Pre-handoff paths verified: 65; final handoff adds one report and updates the existing heartbeat.

Completion marked 2026-11-22T23:22:18.395Z at 48.68 minutes from recorded actual start, within this slot's absolute cutoff.
