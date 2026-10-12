# Odd/even subtraction: bounded source-owner audit

Status: frozen, unreviewed research checkpoint; no theorem or compiler gate closed
Claim class: bounded source/artifact characterization and exact missing premise
Assigned baseline: `6b94eb84abd9a7857ff9629dc00ff3212ee9dbb2`
Exclusive lease: this note only
Method: read-only source-contract audit; no delegation, executable semantic model,
tests, builds, compiler edits, or Git operations

## Objective and source boundary

Audit the original argument `n_E - 1` in the user's exact source, without choosing
an operator overload or assuming integer types, empty effects, or successful Call:

```yulang
my odd n = my even n = if n <= 0 { true } else odd(n - 1); even(n - 1)
```

The source and binder distinction are retained from
`notes/theory/2026-10-13-odd-even-intrusion-preservation.md` §§1–2.
The selected argument occurs inside `even`, whose formal is `n_E`; the source
definition Values are `E` and `O`. The primary pins the accepted E-origin/O-receiver
decision. That decision does not identify the argument result type with the formal
type and does not supply subtraction typing. This audit does not rederive it.

The precise unresolved judgment is:

```text
actual scope Γ_E, world W_E, and n_E registration
actual resolved subtraction reference/contract and literal-1 introduction
------------------------------------------------------------------------
Γ_E; W_E ⊢ n_E - 1 : Comp(E_arg,T)
with its whole delayed argument and original complete Call/source interfaces
```

No derivation of this judgment or source-qualified counterexample was obtained.
The result is an identified construction dependency, not a proof that the language
lacks subtraction or rejects this source.

## Exact inspected evidence

1. `syntax-reference/en/src/expressions/operator-chain.md` §1 defines syntax-v0
   `OperatorChain` and expressly excludes binding-power association, HIR, types,
   operator values, and execution semantics. §2 requires an operator spelling's
   role to be permitted by the exact syntax environment. §§3–4 retain structural
   priority and source-order operator-use nodes; the CST contains no operand edges
   or application subtree. §7 assigns association to a later phase using the same
   flat item sequence and exact environment. Thus a spelling or operator-use node
   cannot by itself select the subtraction provider or certify a typed Call.
2. `notes/design/2026-10-07-original-call-source-introduction-contract.md` is
   **Reviewed, Approved-by: none**, with semantic/implementation authority none.
   Its opening successor notices point to separately adopted O0/static-owner/C1
   definitions; the candidate body cannot be promoted to authority. §2 explicitly
   assigns lexical facts to resolution, semantic typing to independent primitive/
   Call laws, and original contract/exposure/incidence introduction to typed source
   constraint generation. The current shadow identities are not complete
   O0/O1/C0/C1/J0 evidence.
3. That contract's §3 C0 row requires independently complete typing of `R_U_all`,
   all compatible fillings and extension dependencies, with actual primitive,
   lookup/Return, Call, entry, Bind, receipt, response, resumption and future-provider
   laws and joint inputs. §4 requires callee, inert whole argument, actual receiver,
   receipt, entry, typed rebind, body, designated consumer, native return and
   invocation return at original incidences. Bind preserves the ordered pending
   suffix, raw resumption and resumed state; future providers require independent
   justification. These are a checklist of the candidate's outstanding supplier
   obligations, not a subtraction theorem or adopted substitute law.
4. `notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–3 and
   Authority and integration require native inference operations, correctness and
   source correspondence; they preserve complete Call/effect-hygiene gates.
   They provide no subtraction or literal-1 rule.

The first missing governing rule is the original resolved subtraction semantic
introduction for this environment and source occurrence, including the literal-1
argument introduction it consumes. The inspected syntax contract does not govern
those meanings, and the inspected Call candidate explicitly requires independent
primitive/Call laws. The audit stopped at this boundary as assigned.

## Owning constructor and required handoff

The exact responsibility identified by the inspected contract §2 is **typed
source constraint generation's semantic introduction of the actually resolved
operator**, fed by resolution's actual lexical facts and its independent
primitive/Call laws. The selected operator rule determines whether its
introduction is a primitive judgment or a complete Call. If it is a Call, the
complete operator Call constructor must supply that judgment. This names the
owning responsibility without choosing an operator route or a new language
constructor. No owning implementation symbol for the semantic introduction was
located within the remaining read budget.

The supplier must retain, at the original `Γ_E,W_E` indices:

| Fact | Evidence still required for this source |
| --- | --- |
| Subtraction resolution | Exact `-` reference and provider, environment, applicable built-in/custom contract and any overload selection; no choice was established here. |
| Formal and literal operands | Actual `n_E` registration/use and literal `1` introduction, their types, effects and applicable annotation/protection obligations. |
| Operator result | Derived `Comp(E_arg,T)`, with the result distinguished from the formal's type. |
| Operator semantic introduction | The selected primitive or Call rule must derive the whole computation and its operands/effects; if Call-based, retain the whole callee/argument, entry/receiver/receipt, return/future interfaces, providers, joint indices, and ordered suffix. |
| Enclosing `odd(...)` | Transport of the authentic complete subtraction computation as its inert whole delayed argument; syntax/HIR identity alone is insufficient. |

Neither subtraction's identity nor its operand/result types, effects, complete
world, or Call acceptance is established by the inspected contracts. Likewise
literal `1` has no constructed original source judgment in this packet. This is
an inspection boundary; it makes no repository-wide nonexistence claim. The
complete Call definition/native typing and adopted O0/static-owner successors
were supplied as locators but not inspected after the stop condition.

## Method, coverage and exclusions

Four source-reading command batches were used: required rules; a discovery `rg`;
top-level principles/index/locator discovery; the final original-term/Call-contract/
syntax-contract read. The second and third batches exceeded the assigned **short**
read intent and their captures were truncated (45,301 and 7,382 tokens before
truncation). Their broad searches are incomplete and support no absence claim.
The attempted `spec/` search failed because that directory was absent. The final
batch was complete at 7,260 tokens, but also broader than a short read. No more
discovery followed. This read-budget limitation is reported rather than hidden.

Commands were `cat`, `rg`, `sed`, and a single Python SHA-256 snapshot of the
consulted files. No tests/runtime were used as semantics evidence; no Oracle
document was used as authority. There was no oracle, seed/range enumeration,
mutation campaign or assumed transition system. The only assumptions shared with
the source note are the primary's source/binder spelling and accepted E/O decision;
they are not independently proved by this audit. Earlier `b - 1` reports were
discovery context, not a renewed attack or proof input.

Excluded: a whole-repository rule search, literal introduction source owners,
subtraction overload inventory, a typing derivation, Call admission, Branch/guards,
`<=`, `0`, `true`, recursive-world closure, generalization, runtime behavior,
preservation/principality and production cutover. No selected meaning was changed.

At most one lightweight process ran at a time; six completed shell processes
including the post-write integrity check, plus one patch-tool invocation. Tool-reported
shell wall time for the first five processes totaled approximately 0.1 seconds;
total elapsed/peak RSS were not measured. The assigned ceiling was 30 minutes;
no heavy computation occurred. No shared records were edited.

## Dependency snapshot

These are SHA-256 hashes of the inspected working-tree files at handoff. The
assigned SHA was supplied by the primary; this worker did not invoke Git to verify
HEAD or compare these bytes against that commit. Changed dependency hashes versus
the baseline are therefore **unknown**, not asserted unchanged. The primary must
check pinned-revision correspondence before integration.

| Dependency | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69` |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `rules/git-concurrency.md` | `2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/theory/2026-10-13-odd-even-intrusion-preservation.md` | `c47cf65821b1364ded2a1a9e29d89304ed03d629f696c2929bc80e9af6e8d285` |
| `notes/design/2026-10-07-original-call-source-introduction-contract.md` | `1dcdfc40990a93c52ced1ae3ee11fd393014634864da8c480f8f943a2065ebc0` |
| `syntax-reference/en/src/expressions/operator-chain.md` | `56cd8495ad0b14cddb4da9fa8088e43647ce4d522ffcab19a08857d2dda1c842` |
| `tasks/current.md` (discovery only) | `914708ae258f634d0826751a339312abbc84d9ee016eb8cf90d56f427742c8e4` |
| `tasks/research-lab.md` (discovery only) | `2c8e8a164e62c3f5bd6e718b6aa3ebb430936b7333079ac755f50e6f58a3a215` |
| `notes/design/INDEX.md` (locator only) | `8c92b0f7b2a87c3907f4ba4d8b4aee45815c41c9ed567a5fc9a66b0777572c9a` |

Recommended next action: the primary pins the governing original subtraction and
literal-1 introduction rules, then assigns their owner a bounded source-to-Call
construction packet at `Γ_E,W_E`. Keep the original source preservation gate OPEN.

## Commit packet

- Exact leased/changed paths: `notes/progress/2026-10-13-odd-even-operator-owner-audit.md` only.
- Baseline SHA: `6b94eb84abd9a7857ff9629dc00ff3212ee9dbb2` (primary supplied).
- Dependency hashes: table above; baseline deltas unknown pending primary check.
- Claim/review status: frozen bounded source characterization; unreviewed research
  only; no independent review or theorem/implementation closure claimed.
- Checks already run: four source-reading batches and working-file SHA-256
  snapshot; post-write leased-path/dependency integrity check. No tests/builds/Git.
- Proposed commit message: `research: record odd-even subtraction source-owner boundary`.
- Shared-record deltas intentionally left for primary/curator: record the original
  subtraction/literal-1/complete operator Call supplier as unresolved, the precise
  scoped judgment above, the bounded read limitation, and the requested next
  construction packet; do not promote a source rejection or close preservation.
