# Proposal: source ownership of a retained Lambda consumer origin

Status: **unadopted source-law completion proposal**. This document records a
bounded rule gap and an exact design question. It does not define language
semantics, amend the charter, approve implementation, or close a proof gate.
Owner: Luna. R68 is closed; no R69 work was activated or granted.

## Question

For the unchanged binding

```yu
my forward (t:[io] int): [io] int -> [io] int = t
```

what source rule, if any, introduces the occurrence-specific
`ConsumerOrigin(n,p,Comp(E_t,Int),profile,K,D,scope)` for the retained body
Name `n = Name(t)`? Identify the source occurrence that introduces demand,
the rule licensing it, and how its path, provider, profile, scope and joint
evidence are formed before whole-annotation checking.

The question must keep three stages distinct:

1. **Inert formation and lookup:** the formal is a retained computation; `Name`
   lookup and result synthesis preserve its carrier and provider.
2. **Demand introduction:** a source rule, if applicable, assigns the actual
   one-layer consumer origin to a source occurrence and typed path.
3. **Execution:** `Code-Consumer` interprets that already justified origin and
   carries its body, pending and invocation obligations.

A computation tag, a Name projection, a structural interface slot, or a native
recipe does not by itself move evidence from stage 1 to stage 2. Successful
execution or a successful target check cannot be used to invent its own prior
origin.

## Pinned evidence and exact boundary

The reviewed R68 packet is `notes/progress/2026-10-19-r68-closeout.md` and its
contract plus six frozen author outputs. R68 derives the formal and resolved
Name prefix and a conditional same-carrier RetainBind/Name projection from
independent carrier and receipt evidence. It stops at the retained
`Code-NameRetained = Data-Name + Code-Consumer` leaf, the authentic consumer
origin/body-check premise and complete invocation evidence. Both fresh reviews
found no blocking, major or minor issue; all 30 R68 source-dependency pins and
six output hashes matched.

The exact 41-file R69 candidate snapshot is
`tasks/agent-loop/sprints/retained-consumer-origin-formation-20261019-r69.md`
(SHA-256 `0a64e5b6841fa9d7219bfa25c58b4ed8b99212078a51bc670fc6ff0104fc2995`). Its source-boundary evidence establishes:

- Charter §§16–18: a computation formal retains its input; whole argument
  reification, lookup and computation-result synthesis are inert; execution
  requires an explicit consumer. These are settled source constraints, not
  an origin-introduction clause.
- Source-call scheduling §2: any elaborated force corresponds to an explicit
  source consumer; carrier passage/lookup/return alone is not elimination.
- Source Generalize §3.1 Lambda rule: an authentic Lambda derivation requires
  actual role/entry, captures, body checking, body consumer and complete
  invocation. The rule consumes those premises; it does not state how this
  retained Name's consumer origin is introduced.
- Source-input construction §3.1: `Code-NameRetained` requires
  `Data-Name + Code-Consumer`, and `Code-Consumer` requires the original
  `ConsumerOrigin`. This is the execution constructor and its premise, not a
  source syntax rule creating that premise.
- Draft source-computation-role §3 and §12: execution is conditional on an
  already justified consumer; raw-source derivation of known-interface demand
  and explicit consumer positions remains open. Its realization theorem
  assumes corresponding source consumers and therefore cannot supply their
  origin.

These clauses do not establish that no additional applicable source rule
exists. This is a bounded owner/source-law gap, not a counterexample, global
absence theorem, ambiguity result, or proof that a new semantic decision is
necessary.

## Annotation and source-owner boundary

A written `p_A` or `p_R` may be legitimate checking information if an
independently licensed bidirectional source rule permits it. This proposal
does not require annotation-blind elaboration. The rule must instead state
whether those target occurrences are premises, how they remain in the original
joint context, and why the resulting origin belongs to the body occurrence
before any successful target check, Function membership, or actual execution
is used. The target may constrain a source-directed body check; it cannot
circularly certify the consumer whose existence that check needs.

The exact candidate rule to evaluate is the source-owned Lambda/body-check
rule at `(d,L,n)`, with the actual formal `p_t`, distinct written whole
annotation positions `p_A/p_R`, incoming open `E_t`, captures, provider,
ordinary constraints and original scope. Any accepted rule must answer:

1. Does the body syntax `Name(t)` itself introduce an elimination at this
   point, or is it only inert carrier/result forwarding?
2. If the written expected result licenses a consumer, which source decision
   licenses that direction, at which exact annotation position, and with what
   typed path and occurrence owner?
3. What forms the original `ConsumerOrigin` fields before checking success?
4. Is the consumer a Lambda body demand, an invocation-result demand, or a
   later caller-owned demand? How does the chosen boundary preserve the
   one-invocation and ordered pending/resumption laws?
5. Which clauses are consequences of the settled charter and which would be a
   new source-semantic choice requiring user adoption?

## Candidate boundary readings and discriminators

These are alternatives to adjudicate, not proposed definitions:

| Reading | Consumer owner and effect | Discriminating behavior |
|---|---|---|
| Body-result demand | A licensed checking rule uses the written computation result interface to place the one-layer consumer at body `Name(t)`. The invocation executes the retained carrier as the body computes its result. | Calling `forward` on a requesting carrier emits during that invocation; an unused computation formal remains inert. A written target may guide checking, but must not be inferred from successful checking. |
| Invocation-result demand | Body `Name(t)` forwards the same carrier as inert data. The call/result boundary owns the consumer that interprets the declared computation result. | The call returns/forwards the carrier; no request occurs until the result is consumed. Storage or returning without later consumption remains inert. |
| Explicit body elimination | Name lookup and body result are inert unless syntax or a separately licensed construct explicitly eliminates the carrier. | The present body `= t` introduces no request; a distinct explicit consumer form is required to execute it. |

The existing decisions settle that lookup/return are inert, a computation
formal retains its carrier, and execution needs a source-designated consumer.
They do not, in the reviewed clauses, select which of these source occurrences
owns that consumer for this annotated Lambda. The smallest discriminators are
the original `forward` call with a requesting carrier, the same input passed
to an unused computation parameter, and a returned/stored carrier that is not
subsequently consumed. Their expected timing and multiplicity must be stated
before any implementation or test expectation changes. If an existing
user-selected source rule already determines one row, cite and derive it;
otherwise the choice remains unadopted for user decision.

## Required completion artifact

A source-law completion should supply one of:

- an exact applicable, already authorized source rule and a derivation of its
  full occurrence/path/provider/profile/scope/joint-evidence tuple for this
  binding, before whole-annotation success; or
- a minimal explicitly **unadopted** source-language decision object naming
  the missing premise, plausible owners, target-directed inputs, semantic
  consequences and discriminating program cases. It must preserve all current
  parent quantifiers and cannot alter the prior proofs silently.

After an applicable origin rule is established, a separate proof must still
show `Code-NameRetained`, body checking, independently formed complete
challenges, actual-provider acceptance, the full designated invocation and
all finite/pending/future observations. The R68 partial lemma can then supply
same-carrier projection under its original independent premises. R65, R64/R61,
actual Q, `Sol_src/Sol_nat`, full Corr and the original theorem remain open.

## Governance and adoption

R69 was evaluated but **not activated**: its 41/41 pinned bytes matched, yet
its named Generalize and source-computation-role clauses require an already
available consumer and do not introduce the occurrence-specific origin. The
proposed 2,400-second envelope was not granted. No worker or reviewer started;
no lease, code change, semantic adoption or test work followed.

The next action is Luna's source-law completion work on this exact question.
If that requires a new semantic choice, keep it unadopted and present the
concrete rule and consequences for user decision. Parent and Simple-sub A/B
remain OPEN 0→0; R50 remains NOT ADOPTED.
