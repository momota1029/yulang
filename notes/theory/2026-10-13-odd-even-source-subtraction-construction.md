# Exact odd/even subtraction: source-constructor boundary

Status: frozen unreviewed research checkpoint; original judgment unconstructed
Claim class: bounded source/constructor characterization and minimized obstruction
Baseline: `6b94eb84abd9a7857ff9629dc00ff3212ee9dbb2`
Branch: `research/simple-sub-intrusion`
Exclusive output lease: this file; proof leaf, no delegation

## 1. Frozen objective and quantifiers

The source remains exactly:

```yulang
my odd n = my even n = if n <= 0 { true } else odd(n - 1); even(n - 1)
```

Let `n_O` and `n_E` be its distinct outer and inner parameter bindings, and
`O,E` its source definition Values. This packet concerns **only the occurrence
of `n_E - 1` inside `even`'s `odd(n_E - 1)`**, with its original source path,
scope `Γ_E`, joint world `W_E`, provider/declaration environment, and actual
parameter registration. It does not replace either subtraction occurrence,
the conditional, recursion, or either call by a lambda analogue.

The required child conclusion, as fixed by the
[parent derivation §2](2026-10-13-odd-even-intrusion-preservation.md#2-exact-source-stop-the-original-argument-judgment), is:

```text
original Γ_E; W_E and actual registered n_E
actual resolved subtraction reference/declaration and literal-1 introduction
-------------------------------------------------------------------------
Γ_E; W_E ⊢ n_E - 1 : Comp(E_arg,T)
with the original whole delayed argument and complete source/Call interfaces
```

For every lawful original instance to which this child derivation is applied,
the construction must use that instance's actual resolved operator, parameter,
literal, joint dependencies and retained evidence. It cannot independently
choose argument/result/provider witnesses and then assemble their projections.
`E_arg` and `T` are the original computation effect and argument-result type;
neither is assigned here. In particular `T` is not identified with the formal
type of `n_E`, and `E_arg` is not set to empty.

The original parent requirement remains preservation of declarative typing
and the required principal result under the actual E/O occurrence's qualified
equalities. Its source domain, lawful instantiations and histories, binders,
effects, alternative interfaces, and world assumptions remain as stated in
the parent. This packet does not establish that theorem, source acceptance or
refusal, a source counterexample, or semantic impossibility.

## 2. Governing premises and exact sources

| Source | Inspected governing section | Responsibility |
| --- | --- | --- |
| [Inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md) | §§1–5, Authority and integration | Native generation/accumulation/propagation and no proof-driven restriction of ordinary inference |
| [Occurrence association](../design/2026-10-12-intrusion-value-type-association.md) | Approved extrusion-event qualification; Definition-root origin for nested call-demand extrusion | Actual inner Call has E/O endpoints; intrusion affects only its actual retained pairs |
| [Copied-row ownership](../design/2026-10-12-value-reference-copied-row-ownership.md) | Decision and scope | Copying descriptions supplies no new Value-reference incidence or retargeted Name |
| [Exact-source elaboration](2026-10-12-odd-even-user-source-elaboration.md) | §2, especially lines 90–103 | Primitive/local relation is an independent source premise; interface placement does not manufacture it |
| [Source Generalize construction](2026-10-08-source-generalize-definition-and-proof.md) | §3.1, lines 130–156 | Literal/authentic primitive, Name, Parameter, Delay, Bind and complete Call schemas |
| [Original Call source introduction](../design/2026-10-07-original-call-source-introduction-contract.md) | §§1–3, especially §2 and C0 row | Resolution supplies lexical facts; independent primitive/Call laws supply semantic typing; most proposal cases are unadopted |
| [Complete Call contribution](../design/2026-10-07-complete-call-contribution-definition.md) | §2 Complete Call case, lines 53–81 | Retain authentic complete operation; independent C0 is required |
| [Native complete Call typing note](2026-10-09-native-complete-call-typing.md) | §1, lines 15–53 | Establishes native production/execution separation and conditional inversion, while original q/IF/M_E/DescMem/CallMem remain OPEN |
| [Literal Call checking](../design/2026-10-09-native-literal-call-checking-definition.md) | Scope and §§1–2 | Selected instance is literal 0 at native id's registered Int frame; no generic literal-1 subtraction application follows |
| [Operator-chain reference](../../syntax-reference/en/src/expressions/operator-chain.md) | §§1,4,7 | Flat accepted spelling/CST only; association, HIR, types and execution are explicitly outside this page |

Process authority is `rules/agent-orchestration.md` (Model routing and Astra
escalation; Proof delegation and decomposition), `rules/research-lab.md`
(Compact assignment packet; Commit conveyor; Evidence quality),
`rules/compiler-engineering.md` (Natural compiler behavior and
proof-obligation economy), `rules/design-authority.md` (Authority order), and
`rules/git-concurrency.md` (Disjoint-file mode). They grant no arithmetic law.

## 3. Actual producer path and its first cuts

The inspected source path has two distinct boundaries.

1. **Syntax to the current LocalSource route.** The operator-chain reference
   lines 45–47 records an infix spelling without operand edges or an application
   subtree. Lines 89–93 defer association to a later phase. In
   `crates/yu-hir/src/module/local_source.rs:488–579`, `Work::Expression` lowers
   permitted tails into `LocalSourceForm::Apply`, retaining callee, argument,
   scope and source form. The guard at lines 526–533 permits ML argument,
   CallTail and colon application tails (with the separate preceding
   ascription case); it does not permit an `InfixOperatorUse`. Therefore, for
   an admitted flat `n_E - 1` infix chain presented to this route, this guard
   returns `invalid()` before producing a subtraction Apply. This is a local
   route fact, not language rejection or evidence that another association
   route cannot exist. This packet ran no parser or HIR probe on the source.

2. **Resolved source to original semantic typing.** The same file's
   IdentifierExpression arm, lines 636–657, resolves actual lexical bindings
   or module definitions and stores the Name; its IntegerLiteral arm, lines
   659–664, stores spelling with the original scope. Neither arm constructs a
   whole typed arithmetic declaration. The Source Generalize §3.1
   Literal/authentic-primitive rule explicitly needs an actual declaration
   and its whole local typed relation. Its Name rule restricts a supplied
   same-value/provider certificate. Its Call rule consumes the original
   callee computation and inert whole argument with real entry/consumer and
   invocation return. The original Call introduction contract §2 assigns
   lexical evidence to resolution and semantic evidence to independent
   primitive/Call laws. Those schemas do not themselves instantiate the
   resolved subtraction declaration in `Γ_E;W_E`.

The latter is the **first missing semantic leaf** at the requested judgment:

```text
actual associated subtraction occurrence and actual resolution at Γ_E
  ↦ its real declaration/reference with a whole independently typed local
    contract at W_E, retaining operand telescope, guards, computation effect,
    provider/entry, admission, alternatives and future-use evidence
```

Its owner is original operator association/resolution followed by typed
source constraint generation under the declaration's independent local law.
The inspected lexical LocalSource owner and candidate planner are exact
nearby implementation owners; neither supplies that semantic constructor.
No specific subtraction DefId, operator provider, arity, curry tree or
primitive status is manufactured in this note. No claim is made that a
selected subtraction law is absent throughout the repository. The reported
absence is of the required instance in the inspected supplier chain.

## 4. Why nearby native facts do not discharge the leaf

`crates/yu-solver/src/candidate_source.rs:335–349` emits Int positive/negative
bounds and empty-effect bounds for already formed LocalSource Integer nodes.
These are candidate constraints. They do not supply the original literal 1's
joint-world/provider certificate or an independently typed whole subtraction
relation. The observation about these **literal** emissions assigns no empty
effect to subtraction.

The Name arm at lines 369 onward emits separate Name effect facts and actions
for its retained resolution. The Apply generation in the same `Work::Finish`
dispatch uses already formed callee and argument endpoints; it does not
resolve a flat infix spelling or prove complete original C0. No candidate
execution, propagation, replay, or completed publication was run or inferred
from these stored generation facts.

The selected literal checking definition explicitly fixes literal 0, native
id, its actual Int frame and independently supplied formation. Its use here
to type literal 1 at the resolved subtraction inlet would require a genuine
new instance with the actual declaration, port and world. Renaming the
integer or transplanting that frame's witnesses does not construct it.

The file titled native-complete-call-typing currently establishes a native
operation separation and a conditional original structural inversion. Its
§1 explicitly leaves authentic original formation and complete C0 open.
It cannot be used as a general complete subtraction Call constructor.

## 5. Complete Call remains intact at the stop

If actual association represents this operator use through Call, its complete
operation is required at its **actual source indices**, with no chosen
replacement association. Denote that required authentic operation reference
by `Q_sub`; this notation does not assert that it has been constructed.
The complete Call definition §2 requires all of the following together:

| Retained original field | State at this boundary |
| --- | --- |
| Callee computation for the actual resolved operator | Declaration/reference and whole typed local relation unconstructed |
| Whole inert argument carrier(s), with original operand incidence | Actual associated operand telescope unconstructed; no curry/tuple encoding selected |
| Actual returned provider, receiver, entry/role, receipt and designated consumer | Unconstructed; no provider or role chosen from scalar type shape |
| Invocation return and current joint world | Unconstructed at the same original dependent event |
| Returned provider and future-use interface | Required verbatim; not replaced by the result descriptor |
| Complete independent alternatives, guards and evidence | Required verbatim; not restricted to observed executions |
| Callee-pending and receiver-pending ordered suffixes | Distinct original suffixes required; receipt is not replayed |
| Independent complete C0 and complete Call contribution | Neither established by retaining the operation reference nor by candidate bounds |

For the **enclosing** `odd(n_E - 1)` Call, its whole delayed argument must retain
this exact source computation and its complete result/operation evidence.
The callee `O`, argument receipt, actual returned provider, receiver entry,
return/future interface, independent alternatives and both pending suffixes
remain required. This note supplies none of them by substituting a scalar
`T`, an empty effect, or separate marginal witnesses.

The approved E/O occurrence qualification is unaffected. When the authentic
native demand generates the retained polar pairs for argument parent `T`
and result parent `R`, its selected intrusion pairs are `C=T,D=R`. E/O
qualification does not establish the antecedent source judgment or generate
those authentic pairs merely from this notation.

## 6. Economy audit, falsifier and next action

Earlier exact-source elaboration stopped at a primitive/Branch premise; the
finite native intrusion derivation left the authentic argument/Call premise
untouched. This producer audit inspects the owning formation boundary rather
than adding another quotient calculation. Its outcome is a localized missing
constructor, not progress on the parent preservation theorem.

The genuine local typing/Call/effect premise is A/B: accepted output safety
and ordinary arithmetic inference require it. The evidence inspected here
does not show that a phase already constructed and then discarded this
whole semantic relation, so it does not justify classifying that premise as
reconstruction debt D. A retained association/declaration/source certificate
could make an eventual bridge direct, but cannot create the independent
semantic law. No new certificate or semantic layer is adopted here.

Falsifier: provide the selected original operator association, actual resolved
subtraction declaration and its independently typed complete local relation
at this exact `Γ_E;W_E` occurrence, with the literal-1 and Call interfaces.
A scalar builtin signature or a successful candidate comparison is insufficient.

One next action for the primary: assign the original operator/declaration
owner this exact formation instance, locating its selected law or proposing
the smallest missing local constructor through the existing authority/review
process. Continue at that producer before another conditional intrusion proof.

## 7. Checks, limits and commit packet

Checks performed: bounded rule/authority/source reads; read-only HEAD/branch
inspection; SHA-256 capture and exact-byte comparison of the direct dependencies
below against the pinned baseline. Every listed comparison matched. Initial
combined output was truncated, and a guessed `crates/yulang_*` search failed;
the primary authorized three additional narrow read batches after the original
four-read allocation. Conclusions rely only on the cited inspected sections,
not omitted output. No compiler tests, builds, runtime probes, semantic
checker, Git mutation, child dispatch or independent review occurred.

Resources: seven bounded shell read batches, sequential lightweight commands;
zero test/build/probe processes and zero children. CPU, peak RAM and exact
reasoning wall time were not instrumented; the assigned ceiling was 30 minutes.
Requested route: registered prover, configured normal GPT-6.1 Sol/high as
reported by the primary. Observed model/effort: unknown; runtime metadata was
not exposed. The role file omits model/effort pins; the live callable schema
supports prover. The inspected `.codex/config.toml` has primary defaults
`gpt-6-luna`/`high`; those bytes and a requested route in prose do not establish
the effective child settings. No Astra escalation was requested or run.

Direct dependency SHA-256 snapshot (all match baseline bytes):

```text
c47cf65821b1364ded2a1a9e29d89304ed03d629f696c2929bc80e9af6e8d285 notes/theory/2026-10-13-odd-even-intrusion-preservation.md
28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775 notes/design/2026-10-12-intrusion-value-type-association.md
7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd notes/design/2026-10-12-value-reference-copied-row-ownership.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
7bc73ee4921fc26f64ca31dc9eff609127d33ab589bc0b6a2c7e4b44201a3317 notes/theory/2026-10-12-odd-even-user-source-elaboration.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
1dcdfc40990a93c52ced1ae3ee11fd393014634864da8c480f8f943a2065ebc0 notes/design/2026-10-07-original-call-source-introduction-contract.md
4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e notes/design/2026-10-07-complete-call-contribution-definition.md
5a2b4c79e052408176f8650c98f08f060c7b81e6bc721fef09a4dadc429f1cb6 notes/theory/2026-10-09-native-complete-call-typing.md
e65be7638ed616f5a88ce7d7bc5fffa06a07ee634df3649bd83cf0a60410d39b notes/design/2026-10-09-native-literal-call-checking-definition.md
56cd8495ad0b14cddb4da9fa8088e43647ce4d522ffcab19a08857d2dda1c842 syntax-reference/en/src/expressions/operator-chain.md
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed crates/yu-hir/src/module/local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49 crates/yu-solver/src/candidate_source.rs
```

- Exact leased changed path: `notes/theory/2026-10-13-odd-even-source-subtraction-construction.md`.
- Baseline: `6b94eb84abd9a7857ff9629dc00ff3212ee9dbb2`.
- Changed dependency hashes: none; this worker changed only the leased note.
- Honest review status: unreviewed producer characterization; no self-certification.
- Proposed checkpoint: `research: locate exact odd-even subtraction source constructor boundary`.
- Shared deltas left to primary/curator: record the LocalSource infix cut separately
  from the missing original arithmetic local-law instance; retain the argument
  judgment, complete Call, preservation, soundness, required principality and
  F5 gates OPEN. No shared record or authority was edited.
- Unverified scope: other association/resolution routes or arithmetic declarations,
  literal-1 semantic formation, actual source reachability, recursive joint-world
  introduction, full interface/C0, execution/replay, transport and generalization.

Writes stop at handoff. Integration and independent review belong to the primary.
