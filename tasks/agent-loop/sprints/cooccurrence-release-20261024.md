# 共起分析と解除の保存：訂正後の証明契約

Sprint-ID: COOCCURRENCE-RELEASE-20261024/r1
Baseline: `6602786c430df75312a2ffb74ebd9561113f3511`
Worktree: `/home/momota1029/rust/yulang-semantics-proof-20261024`
Branch: `research/semantics-proof-20261024`
Status: fixed successor to the completed local-results packet; whole-language parent OPEN

## 元の目的と今回の到達点

元の依頼は Yulang 全体の意味論・型健全性を docs/theory に完成させることであり、実装は対象外、子は Astra のみである。元の source 領域、任意の型導出と有限実行 prefix、Simple-sub A/B・主型性・停止性の義務を変更しない。

今回の直接訂正は `'e?` を独立した実行意味論にせず、引数の保護と正確な共変位置の共起から共有変数と解除を説明するものである。誤った追加仕様選択の問いを取り下げ、共起による静的変数の併合と、動的な保護・解除の保存を構成的に接続する。`A_all` を承認済みにしない。

到達証拠は、位置の共起条件、provenance を保持する商表示、保護と解除の可換図式の導出、固定された実際の簡約 owner との対応範囲である。全 source の対応を仮定して同名の結論を得る循環証明にしない。残る bridge は生成・消費 owner とともに記す。

## 依存と source 所有者

- 直接 authority: `notes/design/2026-10-24-cooccurrence-release-clarification.md`, SHA-256 `c9eb9b8d274172f02bc82088896c30dd92e219a02adf6ba22418b2cc34207d12`。
- compose authority: `notes/design/2026-10-15-compose-scoped-effect-release.md`, `fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679`。
- flat covariance/evidence: `notes/design/2026-10-03-concrete-compatibility-boundary.md`, `5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16`。
- candidate machine: `notes/theory/2026-10-24-corrected-machine-simulation.md`, `fffb4f1540739020a0702d4f7b07d41cd9b68a9063f36d24292914b84e6b606d`。
- Oracle immutable commit `a58eefc31e22141574b6f20c6a5748151c6d79f1` is readable with `git show` in `/home/momota1029/rust/yulang2-oracle-capture`. The obsolete `/tmp/yulang2-oracle-read` is absent. Do not use mutable checkout bytes as the historical source.
- Oracle `crates/infer/src/compact/analysis/occurrence/mod.rs`: `7bf082236f7c90a33fe9d0084dc3d993d3528bb5a272a44265df8f27728e46a2`。
- Oracle `crates/infer/src/compact/analysis/occurrence/substitution.rs`: `b6d04c187a870892239db84a16360f700f7efaef4c0ba7b731d1389db31f9bf2`。
- Oracle `crates/infer/src/compact/merge/entries.rs`: `d848f4034fa57cb7581e58116aba5e825b3f78c79d48bbd08800352dcfc3b10f`。
- Oracle `crates/poly/src/types.rs`: `9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c`。

## 分担と lease

Producer: `/root/astra_cooccurrence_proof`; exact sole output `notes/theory/2026-10-24-cooccurrence-release-preservation.md`; final message is the single handoff. Three related stages: incidence criterion and actual producer; quotient/transport/query/update proofs; parent application and exact residual obligations. No descendants, shared-record writes or Git.

Primary exact writes: this contract; `notes/design/2026-10-24-cooccurrence-release-clarification.md`; `docs/yulang-semantics-and-soundness-ja.md`; `docs/yulang-proof-index-ja.md`; `notes/design/INDEX.md`; `questions/2026-10-24-release-multiple-ingress/receipt.md`; `tasks/agent-loop/current.json`; `tasks/agent-loop/sprints/cooccurrence-release-20261024-outcome.md`. The original question and old frozen proof/contract/outcome bytes remain historical inputs. No question bundle is staged.

Implementation lane: EXCLUDED_BY_USER. No builds/tests/compiler changes. Original checkout's unknown writers remain quarantined; no copy-back or lease reclamation. The live tool reports the three prior children completed; that observation applies only to this conversation tree.

## Budget, review and stop

The material user correction authorizes this successor research direction under the original task. Reserve a new finite 300-second Astra envelope: dispatcher 45, producer 195, independent review 60. Prior 900 seconds remain charged, never reset. Maximum one active Astra child. Requested effort medium, actual model/effort/duration UNKNOWN unless observed. No background service.

Freeze producer bytes and dependency hashes before review by `/root/astra_semantics_review`, which did not construct this proof. Attack identical positive positions with distinct receipts and only one crossing; lost scope/route correlations; weights; negative pass, interval equality and sandwich branches wrongly presented as positive co-occurrence. Distinguish representation laws from full source correctness. Primary adjudicates, repairs and records actual accepted scope. No self-certification.

Stop the assignment on a frozen result, decisive counterexample, missing authority/input, or its bound. Do not add arbitrary restrictions to the original language to save a lemma. Hash/link/whitespace inspection is permitted, no tests. At coherent outcome preserve explicit intended paths and inspect the full outbound range before a non-force push to the dedicated branch. Whole-language closure remains OPEN unless all original premises are actually discharged.
