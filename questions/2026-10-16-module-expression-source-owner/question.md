# Authentic module-expression source ownership

Question ID: 2026-10-16-module-expression-source-owner
Question revision: 2
Worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Baseline: 6e3eb6496; relevant production HIR/solver owners unchanged from 0a9af0da5
Task/thread locator: current API conversation; stable message URL unavailable
Status: independently reviewed revision 2; pending user decision; no approval presumed
Writer: questioning primary

## Why this decision remains

The user requests completing playground, inference and execution with proofs.
Bare module expressions already have source syntax and direct-root HIR, but
candidate source carriers and receiving APIs require a definition owner. The
October 12 record in tasks/current.md explicitly leaves the standalone
receiving context undecided. The ordinary binding-carrier approval excludes
this extension. Neither integer-only admission nor relaxing runtime rejection
constructs that owner; inventing a DefId or wrapper violates current authority.

AGENTS.md and rules/design-authority.md require approval before a new durable
API decision is implemented. Only this ownership extension awaits the decision;
ongoing native proofs and existing runtime work continue independently.

## Existing authority retained

- notes/design/2026-09-20-hir-direct-root-expression-slice.md: authentic direct
  expression occurrences, source order, no binding namespace or DefId ordinal.
- notes/design/2026-10-10-ordinary-hir-successor-carrier.md: atomic authentic
  binding carriers; direct expressions are outside that earlier scope.
- /home/momota1029/rust/yulang2-oracle-capture/spec/2026-06-13-mono-vm-contract.md,
  “Program と roots”, and the reviewed ordinary runtime simulation §module
  initialization: interleave computed bindings and expressions in source order;
  evaluate each expression; cache completed computed definitions. No final
  module-result value or expression selector is specified or added here.
- notes/design/2026-10-11-yulang-inference-top-level-principles.md and the
  approved occurrence-qualified extrusion/intrusion association continue to
  govern constraint generation, levels, copying and Value-reference SCCs.

## Recommended concrete extension

### 1. Authentic source root

Introduce privately constructed ExpressionRootId anchored to the existing
original direct-root HirOccurrenceId, and an honest tagged SourceRootId:

```text
SourceRootId = Definition(DefinitionRootId) | Expression(ExpressionRootId)
```

Only HIR formation of an actual direct root can construct its expression
identity. A child occurrence, caller ordinal or foreign-artifact handle cannot
impersonate it. Generalize carrier/local/parameter/Catch-binder/named-group
ownership where direct expressions may contain them. Preserve all existing
binding identities and equality relationships. Add an honest source_root()
accessor; definition-only accessors become partial where necessary or remain
restricted to definition-owned objects. Do not fabricate a binding or Lambda.

Form direct-expression carrier outcomes from the actual retained source plan,
without changing ordinary HIR items, occurrences, errors or diagnostics.
Supported, unsupported/recovered and genuine availability failures remain
separate. Publish each completed carrier atomically.

### 2. Nondefinition inference receiver

```text
SourceReceiver = Definition(DefinitionOrderId) | Expression(ExpressionRootId)
```

The batch validates each expression receiver against the original HIR and
retains its original occurrence, source schedule, value/effect components and
level. Use top-level body level 1, with unchanged nested-local level rules.
Do not generalize/export an expression result as a definition scheme. The
level/copy correspondence remains a proof gate before its dependent production
implementation; selecting this representation does not prove that gate.

Keep ordinary DefinitionUseId, target definition, original occurrence/cause,
use level and component positions. Generalize only the consuming-parent field
to SourceReceiver. Definition-to-definition uses retain the existing definition
SCC route. Expression-origin uses consume the actual published definition
interface through the existing capture/FreshUse owner when its target is
available. They are not synthetic definition-SCC members and introduce no
second Name-instantiation algorithm. Forward uses must retain their original
schedule and use identity until that ordinary target interface is available.

Register the direct root as its authentic occurrence-based expression Value.
Retain references and Apply associations through existing source construction.
Do not equate its receiver with a referenced definition. Definition SCCs and
occurrence-qualified Value-reference SCCs remain distinct relations.

### 3. Runtime handoff

SourceSite retains SourceRootId plus its original occurrence/range. Compile
expression bodies into the existing code arena. Form the execution list in
original HIR item order:

```text
ExecutionRoot = Definition(existing definition index)
              | Expression(original expression root, code label)
```

Include computed binding demands and all direct expression demands. Expression
completion discards its value and advances the root cursor without publishing
a global cache cell. SourceRootId records source provenance, not the dynamic
execution owner. Initial root execution and its scheduling suffix use ModuleRun;
genuine Calls, argument Force, body execution, handler installation, forwarding
and capture preserve the existing current Invocation/ModuleRun owner and return
rules. A handler inside an invoked relay therefore still belongs to that relay's
actual invocation. Definition completion keeps its existing cache owner. The separate resumed-definition-materialization decision
is not answered or changed here.

Keep --run selected-definition: execute ordered roots, then observe/materialize
that selected definition as today. Add no final module-value rule, implicit
exported scheme or new CLI selector.

## Implementation and proof gates

G1: independent review and approval of this ownership/API scope.
G2: direct-root carrier formation with original admission/identity preservation.
G3: receiver/use routing, published capture/FreshUse, level and Value-reference
association correspondence. Keep dependent production gates open until proved.
G4: mixed runtime roots with source-order, completion and owner correspondence.

Required evidence: authentic/cross-artifact root checks; unchanged binding
identities and ordinary output; original definition-use/FreshUse and level
invariants; exact copying-occurrence Values; complete mixed-root ordering;
no expression cache publication; correct root continuation and handler ownership;
whole-program classifier coverage of every new root. Focused cases include
Name/application/integer roots, forward references, mixed root order, nested
locals/parameters, recovered source and effectful expressions followed by the
selected definition. Tests alone do not close the corresponding proofs.

Stop the affected implementation if it requires fake definitions, loses original
occurrences, routes a use through an unauthenticated parent, changes existing
binding identities or fails the selected level/copy invariant. Do not silently
weaken the source domain to preserve a failed proof.

Cost budget: one owner/carrier/root record per relevant item and one use record
per actual reference; linear source compilation/root-list storage plus existing
constraint/copying costs. No per-transition source scans, benchmark campaign or
new production registry is selected.

## Alternatives and requested decision

1. **Approve this extension (recommended):** authentic expression identity and
   nondefinition receiver share the ordinary source/use machinery; direct roots
   can proceed through the listed proof/implementation gates. Existing definition
   APIs require honest owner-aware/partial accessors.
2. **Keep the existing binding-only ownership for now:** direct expression
   completion remains blocked; existing defined-root execution and independent
   native inference work continue. This does not meet the full requested scope.

Synthetic DefIds/wrappers contradict existing authority. Nullable definition
parents conceal the required owner/level/schedule. A second standalone Name
solver duplicates inference and is not proposed.

Read-only architect native_consumer_architecture supplied this scoped proposal.
Revision 1 received clean specification review from ordinary_carrier_contract.
Compiler-referee runtime_semantic_review found one major ambiguity: source-root
provenance must not replace dynamic Invocation ownership. Revision 2 explicitly
retains the established current-owner rules; focused compiler-referee review
is CLEAN and closes that finding. The primary accepts the reviewed proposal
for presentation only. Approval of G1
is not proof closure, production cutover or approval of unrelated semantics.

Requested answer: approve option 1 or retain option 2, or state a concrete
replacement ownership law. A direct conversational answer will be recorded
with provenance; no additional approval of the same choice will be requested.
Keep this entire pending directory unstaged/uncommitted. No answer bundle or
approval receipt has been fabricated.
