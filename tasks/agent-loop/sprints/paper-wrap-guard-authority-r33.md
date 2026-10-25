# Sprint PAPER-WRAP-GUARD-AUTHORITY-20261026/r33 — operational rule intake

Status: FROZEN; bounded primary-only source/authority intake admitted by Luna.

Branch: `research/simple-sub-intrusion`

Baseline: `609a56bdf`

Revision: r1.

## Goal and boundary

Resolve the next question after R30–R32 by identifying the exact missing
governing rule for `wrap` in finite typed graph observation and routing it to
its authority owner. The only output is a source/authority intake note. Do not
choose a guard classification, edit the manuscript, change compiler semantics,
write an approved question/answer bundle, or implement a graph rule.

The intake must make the required decision questions concrete, record what the
pinned sources do and do not say, distinguish operational head observation
from call-entry peeling and deferred adapter execution, and provide typed or
explicitly conditional discriminators. If no governing approved source is
found, record the gap as OPEN and give the exact authority/approval route.

## Frozen dependencies

- Corrected constructor report: `tasks/agent-loop/history/paper-guard-constructor-authority-r30-primary-r3.md`, SHA-256 `6a17db0e8c697d695f88a117f6f0800b90371aa141bff71e2117541a122609dc`.
- R32 independent review: `tasks/agent-loop/inbox/paper-guard-authority-r30-delta-review-r2.md`, SHA-256 `3488c2cb10e1b9b36ef2ed4388e1609b3e64332ad6e10dd7654e8ed4bcb22743`.
- Operational manuscript: `docs/yulang-operational-type-safety-ja.tex`, SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- Source manuscript: `docs/yulang-source-type-safety-ja.tex`, SHA-256 `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`.
- Raw syntax: `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`, SHA-256 `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`.
- R30 source handoff: `tasks/agent-loop/inbox/paper-guard-constructor-authority-r30-research.md`, SHA-256 `6c1717c0de5861d6e14c0a931af60bee8d10866546ca2fd76a06b57ecea800a6`.

A pinned dependency change invalidates this intake and returns it to Luna.

## Sole owner, path and resources

- Primary Luna alone owns this packet and its one output:
  `tasks/agent-loop/inbox/paper-wrap-guard-authority-intake-r33.md`.
- No child, proof, implementation, checker or independent-review lane.
- Cap: 300 active seconds for source reading, authority mapping and the single
  intake artifact. Record start and stop. If exact duration becomes unknown,
  charge the full cap and stop.
- Zero Lean/Lake/cache/Rust/build/test/runtime/benchmark/network calls. No
  source or manuscript edits, no Git operations by any worker, and no compiler
  semantic changes.
- `NO_SAFE_CODE_SLICE`.

## Required intake contents

1. Exact source clauses and their boundaries for `rec` graph guard, `wrap`
   typing, finite graph typing, call-entry peeling, and callable shape.
2. A concrete list of unanswered decisions: whether `wrap` is a head guard;
   whether observation follows its function child; how adapter code references
   are represented and when they are observed; how outer/inner callable types
   and adapter evidence are retained; and the guard outcome for a wrap-only
   cycle.
3. A minimal discriminator for `H(r)=wrap(graphReference(r),idArg,idResult)`
   at `Xi(r)=C(A,A)`, with identity-adapter typing explicitly conditional on
   its ordinary code typings, plus an adapter-only-reference discriminator
   whose typed heap admission stays unestablished if the source does not give
   its graph premises.
4. Authority route: operational `rec`/graph guard source owner first; the
   source SCC/closure owner may supply capture evidence but cannot infer the
   operational guard rule. Any new semantic rule remains subject to normal
   independent review and user approval before adoption.
5. Exact OPEN status, next evidence owner and stop condition. Do not create a
   user question bundle unless an actual user decision is requested by a
   separately authorized question packet.

## Acceptance

Accept only an accurate source/authority gap intake with explicit candidates
and no adopted semantics. A source citation, candidate discriminator, or
manuscript correction proposal does not prove the full graph-guard theorem or
close source/native, A/B, implementation, or production gates. At completion,
Luna synchronizes compact current state, consults the dispatcher at the packet
boundary, and commits only the intended exact paths after reviewing the entire
outbound range.
