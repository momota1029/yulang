# R32 independent M1 review

Disposition: **prior two MAJOR findings closed in substance; three minor corrections remain**. No new semantic decision is approved. Read-only fallback: primary may persist this report verbatim.

1. **minor — substitution notation incorrectly substitutes into the whole recursive type.**

   Target: `tasks/agent-loop/history/paper-guard-constructor-authority-r30-primary-r2.md:106–110,117–119`.

   Authority: `docs/yulang-operational-type-safety-ja.tex:235`.

   With `T=μ α.F`, the required unfolded type is `F[T/α]`. The report instead writes `T[T/α]`, which leaves the bound recursive type unchanged. The displayed introductions otherwise provide the intended conditional derivations.

   Closure: name the recursive body separately and replace these equalities with substitution into that body. Preserve every formation qualification.

2. **minor — nominal declaration premise conflates payload and result templates.**

   Target: `tasks/agent-loop/history/paper-guard-constructor-authority-r30-primary-r2.md:110`.

   Authority: `docs/yulang-operational-type-safety-ja.tex:126–130,220`.

   “Payload template `D⟨α⟩` and one payload of type `α`” gives conflicting descriptions of the constructor payload. The intended derivation requires one payload template `α`, with constructor result `D⟨α⟩`.

   Closure: distinguish those two templates explicitly; retain conditional declaration and recursive-type formation.

3. **minor — continuation row overstates the missing typing authority.**

   Target: `tasks/agent-loop/history/paper-guard-constructor-authority-r30-primary-r2.md:123`.

   Authority: `docs/yulang-operational-type-safety-ja.tex:350–354`; graph admissibility `:265–268`.

   The manuscript explicitly supplies a continuation introduction rule. The absent authority concerns its graph guard classification, rather than absence of a continuation node typing rule.

   Closure: identify that missing guard classification precisely. Keep heap admission unestablished; do not infer a lambda classification.

The earlier direct-cycle typing defect is repaired by explicit rolls and conditional formation premises. Unsupported instances are called unestablished rather than impossible. The polymorphic two-node example provides valid pointwise node typings: application yields `Bool`, abstraction yields `∀β.Bool`, and fresh `β` satisfies the side condition for the same environment and declaration table. This establishes node typing only; manuscript graph typing additionally requires guardedness.

All 20 syntax constructors appear, with 21 rows after splitting lambda modes. The report preserves both derivations for the same underlying intersection value, distinguishes wrap function traversal from deferred adapter code, and keeps HigherOrder definitions separate from manuscript authority. `wrap` remains the first unresolved classification. All parent gates remain OPEN.

These findings concern report accuracy. No implementation defect, approved specification change, expected-output change, fixture change, diagnostic change, or semantic test-name change is established.

Receipt: supplied prelaunch start `2026-10-25 18:20:50 UTC`; first reviewer clock `18:20:59 UTC`; final clock `18:21:42 UTC`. Supplied-start elapsed bound: 52 seconds; independently observed interval: 43 seconds. Exact cumulative active duration is UNKNOWN; charge the full 150-second grant and cease. Effective model/effort UNKNOWN. All ten frozen contract/dependency hashes matched initially; final rechecks of the contract, target and three direct manuscript/syntax sources matched. Source reads, comparisons, hashing and clocks only. No files written, descendants, Git, network, checker, Lean/Lake/cache, builds, tests, runtime or benchmarks. All reviewer activity stops here.
