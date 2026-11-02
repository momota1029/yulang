# Sprint R236 — direct canonical literal generator

Status: ADMITTED, primary-owned model construction. Baseline `52c8053d5` on
`yulang3`. The unchanged parent is
`YulangClosure.SourceProblem.InferenceSoundness` at
`Contracts.lean:128–130`; preserve every source form, arbitrary satisfying
assignment, original coordinate, and shared scoped witness.

## Fixed target

Use the pinned Simple-sub literal branch's actual shape: a literal produces a
canonical primitive type directly, without first allocating a variable and
solving reciprocal constraints. Extend this candidate to the eight literal
forms in the already user-approved L1 source rule. Build a payload-preserving
map from `OriginalSource.Literal` to the adopted `PaperTypes.Literal`, and a
source-indexed result carrying the exact original site, root, event, scope,
and witness alongside its canonical Paper type/value.

Connect that result to the actual original symbolic generator: R196's checked
`Build` equation emits a `literalDeclaration` atom containing the original
payload at the original site/context. Use that output as the consumer input.
Prove the all-eight type/value/coordinate equations without depending on a
chosen type assignment or native run.

## Authority and limits

The adopted L1 document fixes all eight type/value pairs, intrinsic empty
effect, same root/event/scope/witness and pure Return. The top-level algorithm
requires source types/constraints to be constructed before propagation and
forbids special solving during generation. The pinned Simple-sub branch
returns canonical `IntType` directly for its supported integer literal.
Extending that direct construction to the other seven forms follows the
adopted Yulang L1 rule as a candidate generator equation; fresh review must
check whether the selected algorithm authorizes that extension.

Do not define the generated output by invoking `OriginalSource.LiteralAtom`,
`Kernel`, an already-typed source judgment, or an assumed solver readout. Do not
invent a code-to-atom identity for `SimpleSub.Term.atom`. This sprint does not
identify the Paper execution carrier with the full source semantic carrier,
prove effect contextual admission, derive every satisfying assignment's
readout, instantiate a complete `SourceProblem`, or close its parent. If the
actual algorithm does not authorize the direct canonical form, stop at that
equation and report the exact missing owner; do not revert to R232 reciprocal
bounds or R235 quotient-only reasoning.

## Frozen dependencies

| Source | SHA-256 |
| --- | --- |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| R196 source generator equation | `69d551760efc1b40f9235e749c4d2edde3e439b2cb91655495bf1c22d7d55c7c` |
| `PaperExecutionSyntax.lean` | `d0dc9871c382ca945059167b8b9e05f8f672170208a994f081e29760a207b87d` |
| `PaperTypeSubstitution.lean` | `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861` |
| `PaperTypeFormation.lean` | `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13` |
| adopted L1 rule | `f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8` |
| top-level inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| pinned Simple-sub import | `cd2b84a84d16be8856766f0514a2f400cf224ac95b6e81e42d4a7a875036e113` |
| R235 outcome | `d0067f3881108f9e4a0caa3bba3d6c653ecba83d3b1fdcbb2e3c51ce570fdd30` |

## Leases and gate

Luna owns this contract, `notes/theory/lean/YulangClosure/CanonicalLiteralGeneratorR236.lean`,
`tasks/agent-loop/inbox/canonical-literal-generator-r236.md`, current state,
review receipt and outcome. No theorem or implementation worker is activated.
After definitions and pinned checking, one fresh nonauthor `spec_auditor`
reviews algorithm authority and source-to-generator conformance. Review must
attack all eight payload maps, direct-constant generation, exact source Build
consumer and scope/root/event/witness retention.

Use the existing pinned Lean 4.35.0 / Lake 5.0.0 project and existing `.lake`
only; no worktree, environment, target or new cache path. User authorization
allows cache growth, bounded to 64 MiB. No Rust/Cargo or general tests. Preserve
all UNKNOWN/quarantined paths and unrelated changes.

Success is a reviewed all-eight direct generator equation consumed at the
original symbolic literal Build node. Report parent-premise delta separately;
the theorem does not close `InferenceSoundness` without independent arbitrary-
solution carrier/readout and same-witness application. If it remains partial,
record the exact remaining source-to-solution edge without starting an
equivalent proof lane.
