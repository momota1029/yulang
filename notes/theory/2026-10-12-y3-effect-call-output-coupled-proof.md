# Y3 annotation, Call, output and residual coupling obstruction

Date: 2026-10-12
Status: frozen, independently reviewed bounded source obstruction; original source/consumer gate OPEN
Method: one direct constructor induction and static consumer trace
Baseline and inspected HEAD: `99cd86fd9a8733e45869eb1ea67a86aeb1e9ec55`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file; leaf, no delegation or Git mutation

## 1. Original claim and quantifiers

The assigned question is whether an actual reachable supported Y3 source
constructor supplies the coupled annotation/Call/output/residual relation
needed by the approved hygiene mechanism. Preserve the original supported
language domain, including ordinary nested annotations, calls, later source
constraints, copies and uses. Do not replace that domain by the historical
Oracle direct-formal spine or by a supplied algebraic template.

A construction witness must identify one actual resolved annotation occurrence
`a`, its resolved concrete set `S`, one fresh local attachment instance `i`,
its actual live source/call endpoints, and its actual output consumers. Its
required incidence is one jointly owned route:

```text
annotation a, S, i -> actual live attachment PUSH_i
                  -> actual resolved Call and its contribution/check route
                  -> both actual output components with the paired POP_i
                  -> each concrete residual constructor's own lineage
                     and exact source-feedback/gamma-to-tail relations
```

For every applicable current or future source lower and reverse constraint,
the route must retain that same instance and its check/subtraction/output
consequences. Independent same-family contributions and separately constructed
residual recipes must remain independent. A literal `SubtractId` is Oracle's
name for the identity; Y3 may use its selected private attachment identity,
but nominal family, row ID, source spelling or endpoint equality cannot
replace it. No total output-wrapper convention is assumed.

The original universal preservation obligation quantifies over all relevant
supported occurrences and uses. The existential question above asks whether
the current source implementation supplies even one required live construction
witness. This packet does not narrow the universal obligation to an easier
source fragment and does not assert that the current admission guard defines
the intended supported language.

Result: the current successor carrier cannot emit the first live PUSH for
the approved attachment route. Its source-owned metadata is present, but its
live words are structurally empty. This is a concrete current implementation
correspondence obstruction. It is neither semantic impossibility nor an
accepted-source counterexample to effect hygiene. Complete Call, coupled
current/future consumption and output preservation remain OPEN.

## 2. Authority and supplied established result

Governing sources read in full:

- [design authority](../../rules/design-authority.md) and
  [compiler engineering](../../rules/compiler-engineering.md);
- [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md);
- [residual lineage selection](../design/2026-10-10-contextual-residual-lineage-selection.md);
- [contextual attachment admission](../design/2026-10-10-contextual-attachment-admission-design.md);
- [pinned Oracle source transfer audit](../progress/2026-10-12-oracle-effect-source-transfer-audit.md).

The source transfer audit is evidence to check, not authority to assume a Y3
construction. The approved policy retains one identity per exact annotation
set with member ordinals, composed-polarity semantics, constructor-lineage
residual identity, all applicable future lower fan-out, and complete Call.
The retracted callback scheme supplies no expected output. General concrete
formal admission remains behind its selected later gate. Full abnormal-route
restoration is not made a general proof premise.

Only §§1,5–8 of
[the finite cycle observer note](2026-10-12-contextual-cycle-summary-proof.md)
were used. Its supplied finite-template equivalence requires grounded sharing,
actual node observations and separate contribution/lineage coordinates. It
does not generate dynamic residuals or prove actual Call/output incidence.
The count proof was not repeated. The current obstruction is independent of
the pending wrapped-extrusion endpoint decision.

## 3. Direct constructor induction: first failed premise

At this baseline, `candidate_context.rs:115–118` defines executable payload
words as:

```rust
left_word: [(); 0],
right_pops: [(); 0],
```

**Carrier lemma Z.** Every live `LocalWeight` at every successfully reached
current successor state has an empty left word and empty right POP word.
This statement includes newly allocated source weights, copied weights,
retained weights after failures and weights reached by later replay. It does
not claim that arbitrary relations are discharged or source constraints drain.

Proof by construction and transition preservation:

1. The initial weight store contains no counterexample. The only production
   allocation of a `LocalWeight` is `source_weight:2174–2195`, whose literal
   initializes both fields to `[]`. Independently, their Rust types admit
   only length zero, so a successful current constructor cannot insert an
   ID-bearing PUSH or POP there.
2. The annotation view owner `candidate_signature_view:733–774` calls that
   allocator. `candidate_signature_effect:1447–1578` constructs paired
   Support/Allowance endpoints and uses the same view for an annotation
   position. An omitted row, empty row or symbolic tail does not add a word.
   A composed-positive nonempty concrete annotation retains the exact source
   set, scope and ordinals; it still allocates only the empty executable words.
3. The formal constructor recurses through Int, Unit, Variable and Function
   at `candidate_formal_pair:1034–1052`. Function arguments reverse composed
   polarity and results preserve it. Its admitted positive concrete ports
   route through `candidate_formal_effect_port:1054–1070` to the same signature
   view owner. Its omitted and singleton-symbolic ports create ordinary rows.
   Neither branch emits an attachment word. The paired Value constraints and
   retained formal domain at `candidate_formal_annotation:1073–1111` do not
   change this conclusion.
4. Definition/local annotations and expression ascriptions use
   `candidate_annotation_pair:1202–1280`; positive and negative interfaces
   share view construction, then actual endpoint links are admitted. Empty
   negative attachment bundles are inert provenance, explicitly excluded from
   executable `ContextExpr` and endpoint comparisons (`candidate_context.rs:
   140–166`). Operation views do not gain source annotation subtraction
   authority (`candidate_signature_view:759–762`). Thus these alternate
   source producers also preserve Z.
5. Copying a view at `candidate_copy_effect_view:806–832` validates its
   payload and calls `candidate_signature_view` with retained source metadata.
   Remapping uses that same owner (`candidate_remapped_effect_view:832–847`).
   Scheme use maps context weights to these newly constructed views
   (`candidate_scheme.rs:1089–1107`); extrusion remaps views with selected
   tails (`candidate_extrusion.rs:265–318`). Their target payloads therefore
   satisfy Z. Truncating/removing weights on an abnormal path cannot introduce
   a nonempty word. Retaining existing weights cannot do so either.
6. Live context operations refer to those payloads and retained child
   contexts. Replay, Swap and result preservation do not allocate an executable
   word. Receiver validation at `candidate_zero_word_filters:2649–2655`
   explicitly requires empty words. Therefore later constraints or reverse
   replay cannot provide the missing first PUSH by transforming a previously
   admitted payload.

This is one constructor attempt, stopped at its decisive premise. It uses the
actual common payload owner rather than enumerating only a favorable source
spelling. It does not establish correctness of the rest of these operations.

`source_weight:2187` sets dormant `SourceUnitPush` only for a nonempty
composed-positive annotation. `materialize_unit_push:2200–2222` can construct
one `DetachedLeftEntry` with `DetachedAttachmentId(weight.0)` and count one.
It is private, detached, and has no non-test caller. Its comment excludes live
ContextExpr, relation, bound, registration or executable-word construction.
`evaluate_context:1487–1529` likewise requires a supplied detached weight table;
it has no production call site that installs its result in live inference.
The detached witness cannot contradict Z or supply a source witness.

Consequently, even for an admitted composed-positive annotation/ascription,
the earliest absent operation is its live attachment emission at the signature
view/payload boundary. For a composed-negative nonempty formal row, source
preflight fails earlier: `candidate_source.rs:98,117–130` rejects it;
`candidate_formal_pair:1035` and `candidate_signature_effect:1507` also reject
it. Those guards explain current implementation reachability, not authority to
restrict the intended language. Removing them alone would still preserve Z.

## 4. Actual Call and output equations inspected

The source Apply owner retains actual callee, argument, evaluation effects,
result and occurrence at `candidate_source.rs:394–412`. The Lambda source
owner schedules the exact formal annotation at `274–282`; Ascription schedules
the actual child's computation at `414–437`. Thus source metadata is not a
substitute for missing live operation emission.

For one actual Apply `k`, `shadow_apply.rs::admit_candidate_fact:1308–1447`
validates the retained source input against its recipe, allocates fresh
invocation effect `q_k` at the application level, and constructs the demand:

```text
callee_value <: Function-(argument_value+, argument_effect+,
                          q_k-, result_value-)
callee_evaluation_effect <: application_effect
q_k                      <: application_effect
```

The native interface records these actual endpoints. It supplies no concrete
formal call predicate containing the annotation instance `i`. Whole-argument
provider compatibility, full Call completeness and actual final output
publication are not inferred from the record or stored constraints.

For its enclosing Lambda `f`, `lib.rs::admit_lambda_fact:11233–11369` uses the
retained formal domain when available, takes the actual body Value, allocates
entry `u_f` and return `t_f`, and emits:

```text
u_f         <: t_f
body_effect <: t_f
Function+(formal_domain-, u_f-, t_f+, body_value+) <: lambda_root
```

The inferred entry origin is retained at its actual owner. It does not create
annotation subtraction authority. This producer emits no paired annotation
POP around the two actual body/output components. These equations identify
the actual consumers inspected; they do not assert a missing complete wrapper
convention or successful scheme publication.

Function child admission at `candidate_context.rs:2557–2608` carries the
actual parent's post-check context, swaps Argument Value/Effect and preserves
Result Value/Effect. Carrying an empty-word context is not a derivation of
the absent `PUSH_i`/`POP_i` incidence.

## 5. Current, future, residual and reverse consumers inspected

`candidate_context_source:2493–2501` seeds only a closed Allowance's zero-word
filter or identity. `candidate_context_execute_relation:2744–2813` registers
that Allowance on the actual lower, replays an existing bound when needed,
and retains a post-discharge context in `discharge_residuals`. The latter is
a relation-to-ContextId map, not a lineage-owned concrete-head residual recipe
with gamma feedback and exact gamma-to-tail projections.

`candidate_check_effect_operand:888–958` expands Support into concrete members
and its tail. An allowed concrete member succeeds; an unmatched member is
forwarded unchanged to an open tail, or mismatches a closed row. It is not
attachment-local subtraction. These concrete operations do not supply an
annotation identity in the subtraction sense.

The opposite-bound consumer at
`candidate_context_begin_replay:2911–3002` constructs children from recorded
lower/upper fibers, preserving ordered Replay dependencies. The subsequent
child driver at `3004–3110` retains queue/completion frontiers. This inspection
establishes those actual owner operations, not that every generated source
obligation drains. Their payloads still satisfy Z. No claim is made that
current/future residual fan-out, reverse gamma-upper feedback, qualifying
intrusion or omission soundness is complete; there is no concrete residual
construction from the required live attachment in the inspected chain to
which such a proof could currently attach.

The exact missing source/consumer premise remains:

```text
The owning source occurrence emits its genuine live attachment instance on
its actual Call/contribution route and retains the paired output operation,
with attachment-qualified concrete reduction and lineage-owned feedback/
projection consumers for every applicable current/future and reverse constraint.
```

The first clause is structurally absent. The subsequent clauses are OPEN,
not conditionally assumed established because the first clause might later
be implemented. The approved constructor-lineage policy is retained exactly.

## 6. Parent disposition and next action

Resolved portion: the current successor source/carrier cannot instantiate the
required live first-PUSH witness. The obstruction is grounded at the common
live payload constructor and its actual annotation/formal/copy owners.
No theorem about approved semantic infeasibility is proved or refuted, and no
source-qualified hygiene counterexample is claimed. The original A/B parent
gate remains OPEN with the source annotation/live relation owner responsible
for the missing construction, followed by Call, output and concrete residual
consumer owners for the downstream premises.

One next action: the primary should adjudicate this exact construction gap
with the existing independent design/proof path before authorizing any
dependent implementation slice. If a minimal provisional constructor is
needed as source evidence, it needs an explicit lease and authority, and must
retain the original parent gate OPEN. Repeating detached arithmetic or another
supplied finite observer cannot resolve this source premise. No new carrier,
semantic restriction, wrapper convention or production admission is adopted.

## 7. Checks, runtime and omissions

Static commands: `cat`, bounded `sed`, `rg`, read-only Git branch/revision/status
inspection, dependency byte comparison with `git show <baseline>:<path>`,
SHA-256 capture, and `git diff --check`. No tests, builds, executable probes,
benchmark samples, Git/index/ref mutations, delegation or writes outside the
lease. One lightweight foreground command at a time after startup; initial
independent document reads ran together and were immediately complete. No
heavy process ran. CPU/RSS and wall time were not instrumented. Truncated
initial document output was re-read in bounded chunks before reliance.

Requested launch: registered `prover`, reported by the primary as failing with
`Selected model is at capacity`. Actual lane: prover-equivalent generic worker,
not a custom prover execution. This worker has no observable launch model or
effort metadata; observed model/effort are unknown. No Astra execution, model
override or hot reload is claimed. The primary is the verification/integration
owner. A fresh independent `compiler_referee` M3 review passed with no
blocking, major, or minor finding. A second generic independent semantic
review of the exact committed artifact also found no issue. Both covered the
bounded carrier lemma and source/consumer correspondence only; global hygiene
and the original parent theorem remain OPEN. The producer does not certify
this obstruction. Runtime model/effort metadata was unavailable for both
reviews.

Omitted verification: source execution, accepted binary examples, general
negative-formal admission, full Call/provider compatibility, coupled output
publication, complete current/future draining, concrete residual lineage/fan-out,
reverse gamma feedback, all capture/generalization/extrusion/intrusion and
abnormal paths, Oracle global H, soundness, principality and cutover. These
omissions do not redefine the source domain. Oracle code was not re-audited;
its direct-formal construction in the supplied audit is comparative evidence
and does not transfer its quantifiers or printed mini-language to Y3.

## 8. Frozen dependencies and commit packet

Every dependency below was byte-equal to the stated baseline at inspection.
No dependency was edited. Current HEAD was that same baseline. The primary
must revalidate this dependency cone if HEAD moves before integration.

```text
e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1  rules/design-authority.md
4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9  rules/compiler-engineering.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98  notes/design/2026-10-10-contextual-residual-lineage-selection.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
f222d83d51af22f26b786bad6bc07d27a2b2fb5b97e0dadbada9159d667bbb32  notes/progress/2026-10-12-oracle-effect-source-transfer-audit.md
6e5561c8614148a8c19c72231cecb9706a64757c58d8fae7a23199591cc387c1  notes/theory/2026-10-12-contextual-cycle-summary-proof.md
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df  crates/yu-solver/src/candidate_effect.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411  crates/yu-solver/src/shadow_apply.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
```

Exact leased path:
`notes/theory/2026-10-12-y3-effect-call-output-coupled-proof.md`.
Baseline: `99cd86fd9a8733e45869eb1ea67a86aeb1e9ec55`.
Changed dependency hashes: none.
Review status: independently reviewed frozen producer obstruction; original parent OPEN.
Checks already run: static source/consumer trace, baseline dependency equality,
note whitespace check; no executable verification.
Proposed subject: `research: localize Y3 coupled effect construction obstruction`.
Shared-record delta for primary/curator: link the exact live payload construction
gap, retain annotation/Call/output/residual and current/future parent gates OPEN,
and distinguish absent Y3 construction from Oracle local pairing and supplied
finite observer results. No shared tasks, index, theory-map, question, policy,
compiler or test files were edited by this lane.
