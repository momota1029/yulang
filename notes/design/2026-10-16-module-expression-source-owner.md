# Authentic module-expression source ownership

Status: Authoritative; G1 complete, G2–G4 implementation/correspondence OPEN
Scope: authentic direct-expression source ownership, receiver routing and ordered runtime roots
Approved-by: user, finalized module-expression-source-owner-a1 revision 1
Approved-at: 2026-10-16
Approval: [question revision 2 and approved answer](../../questions/2026-10-16-module-expression-source-owner/approved-answer.md), integrated at `f40e4235d`
Reviewed-by: `native_consumer_architecture` proposal; `ordinary_carrier_contract` specification review; `runtime_semantic_review` revision-2 ownership delta CLEAN
Supersedes: extends the binding-only carrier scope of 2026-10-10 without changing that earlier scope's completed claims; no source-order or dynamic-owner semantic change

## Approved scope and provenance

The matching question, byte-identical displayed draft and finalized answer were
validated and committed together. The recorded approval is `良さそう`, immediately
following the complete display of draft a1 revision 1 in the separate answering
conversation. Its stable message URL and exact timestamp are unavailable.
Question SHA-256: `25c9d591e35f5358cceffe95b83b4f4bca8f7d3a2ed3981b4b7b33425156c430`.
Draft SHA-256: `c270277112016b72980e603c67aa4c31729fb3bc7e1ba91626259019620fa97e`.

The user's `my _ = expr` comparison selects source-ordered evaluation and discarded
results. It does not authorize synthetic binding identities. The text below is
the approved question's existing-authority, concrete-extension and proof-gate
sections, preserved without a new technical decision. The separate resumed
computed-definition materialization laws remain unanswered. G1 approval does not
close G2–G4 proofs, full inference, runtime or production cutover.

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
