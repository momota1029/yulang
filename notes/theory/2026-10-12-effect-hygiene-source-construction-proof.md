# Effect hygiene: source construction and the first negative premise

Date: 2026-10-12
Status: frozen unreviewed research characterization; original hygiene/inference gates OPEN
Claim class: constructive static source facts, reuse of reviewed conditional clauses, and an exact unsupplied construction premise
Baseline: `research/simple-sub-intrusion`, `1f6ea89bffc69dfe614d5b20d25a353b9ea52a34`
Oracle read baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, `/tmp/yulang2-oracle-read`
Exclusive lease: this note only; proof leaf, no delegation

## 1. Frozen objective, quantifiers and exclusions

The governing meanings are [annotation hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5 and [residual lineage selection](../design/2026-10-10-contextual-residual-lineage-selection.md),
“Selected policy” and “Preserved contract and open obligations.” Composed
covariance grants concrete allowance; composed contravariance permits local
subtraction at that occurrence. Ignoring variables in a concrete atom set
preserves their connections and applicable later concrete checks. Separately
constructed residual recipes retain their lineage when their source rows become
equal. Applicable current and future lowers must reach each retained recipe.

The assigned conclusion remains a construction/consumer theorem for each
concrete annotation occurrence, with its original owner, lexical scope,
binders, composed Function path and resolved operands: preserve symbolic flow,
implement the appropriate allowance or attachment-local subtraction, and retain
independent same-row contributions through their selected residual lineage.
Every actual use/copy and applicable Call route remains in the parent scope.
No typed-view map, active-consumer preservation, endpoint transport, attachment
judgment, or source admission is supplied as a new hypothesis.

Original [H](2026-10-11-oracle-global-effect-hygiene-proof.md) §1 retains every
successfully lowered Oracle source program, negative occurrence, original scope
and binders, actual copy/instantiation, and actual function Call/output route.
The local source facts below neither narrow those quantifiers nor prove H.
Complete Call preserves the whole argument, callee computation, actual returned
provider/entry, future use, and independent alternative evidence, as specified
in [complete Call contributions](../design/2026-10-07-complete-call-contribution-definition.md)
§2, “Complete Call case.” A local allowance comparison is not that operation.

For the static facts fix a successfully formed `SourceAnnotation` a, its
`DefinitionRootId` d, an exact retained row position p, the actual formal
parameter q if applicable, and its `AnnotationScope` s. These objects are
distinct: d is not a dynamic receiver; p is not a canonical solver row; s is
not a provider identity. Let C be the row's resolved concrete operands, and x
its retained symbolic name when present. Current executable concrete operands
are nullary `SourceEffectId { module, declaration }`. The original obligation
is not restricted to this implementation alphabet.

Static constructor results require normal completion of the named fallible
owner calls and valid branded inputs. They concern the construction epoch;
they assume no subsequent copy/equality/transport law. The reached-consumer
clause explicitly assumes reaching that consumer; it supplies no all-history
activation theorem. Source availability and completion are conclusions still
to establish for the missing negative case, not assumptions hiding it.

Exclusions: the withdrawn callback expected scheme; runtime subtraction or
handler selection inferred from an allowance; independently chosen marginal
witnesses; Oracle H completion; arbitrary source admission; complete replay,
capture/generalization, parent/copy preservation or endpoint transport; global
soundness, principality and F5 cutover. The controlling [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5 require meaningful successful inference and safe nonpublication, without
a blanket exact-state rollback premise.

## 2. Actual formation now retains the inputs

The historical owner-gap table in hygiene integration §4 predates the concrete
carrier. At this baseline, annotation retention and concrete endpoints exist.

`yu-hir/src/module/source_annotation.rs:349–574` retains a's owner/position,
the recursive Function tree, p, C and symbolic names. `parse_row` places a
sigil identifier in `variables`; a concrete identifier must resolve to exactly
one declaration and is stored as its `SourceEffectId`. No variable is inserted
in C. Unsupported parameterized syntax has no construction theorem here.

`module/local_source.rs:730–788` retains the actual parameter annotation and
local parameter owner. `candidate_source.rs:184,274–282` selects the local
annotation scope, records the actual parameter level, and schedules
`Action::FormalAnnotation` before the body; `:663` dispatches the real action.
This is a producer/dispatcher chain, not proof that every source passes its
earlier preflight or that the action completes.

### Composed polarity at the actual owners

Let a retained Function-tree path w use A for an argument descent and R for a
result descent. With root sign v, its row sign is

```text
sign(v,w) = v · (-1)^(number of A descents in w).
```

This is the existing polarity lemma, now checked against all three owning
recursions at the pinned source. Induction on w has the empty-path base v;
`A` flips both the running sign and parity, while `R` preserves both.
`preflight_formal`/`preflight_annotation` (`candidate_source.rs:117–133`),
`candidate_formal_pair` (`candidate_effect.rs:1034–1052`), and
`candidate_signature_value` (`:1392–1444`) each implement exactly those two
steps. Formal construction starts Negative (`:1091`); general annotation
checking/exposure retains a separate source `variance` parameter. The paired
positive/negative endpoint signs do not replace source variance.

For example, a formal's Function result row is Negative; its Function argument's
Function result row is Positive; adding another argument descent returns to
Negative. These are position calculations, not executed fixtures or inferred
schemes. The arithmetic and corresponding current recursion supply no runtime
subtraction conclusion. The reviewed [conditional contravariant proof](../progress/2026-10-10-contravariant-effect-conditional-proof.md)
§3 already establishes this arithmetic; it is not counted as a new proof gate.

## 3. Positive and variable clauses, frozen at their owners

The reviewed [actual formal-port bridge](2026-10-11-oracle-effect-hygiene-source-bridge.md)
P/Q is retained at its original 56-position source envelope, with its successful
replay-setup/enqueue and reached-consumer premises. Its five decisive source
files below are byte-identical to that note's recorded fingerprints. This
packet does not rerun or promote that proof. Direct inspection yields the
following constructor/consumer facts for the specified completed calls.

| Case | Actual constructor or consumer consequence |
| --- | --- |
| Formal port with no row | `candidate_formal_effect_port:1054–1071` allocates a shared effect row; it does not introduce a concrete atom. |
| Formal row with C empty and one x | Both interface terms refer to `candidate_formal_effect_variable(s,x,level)`, independently of variance. The `(s,x)` registry reuses the same scoped coordinate, rather than emptying it. |
| Composed-positive row with concrete C and at most one x | The paired calls to `candidate_signature_effect:1447–1576` use the same Positive variance and p-keyed view map, with opposite endpoint signs. The view retains C and the actual symbolic tail. Positive installs `Support(view)`; Negative installs `Allowance(view)`. |
| Reached `Support(view)` comparison | `candidate_check_effect_operand:894–916` enqueues each `AnnotationMember(view,ordinal)` and the actual symbolic tail separately. |
| Reached concrete atom z versus `Allowance(view)` | `:919–948` compares the resolved effect. A member of C succeeds; an unmatched effect forwards the same z to the retained tail, or records mismatch when no tail exists. Success is an allowance check, not removal of z from complete output. |

The variable connection follows from the actual key and returned live terms
(`candidate_effect.rs:979–997`), not from treating x as a concrete atom.
The positive concrete constructor's `allowed.extend(row.concrete)` and separate
tail lookup make that distinction explicit. A forwarded Contribution or
AnnotationMember keeps its endpoint identity; no new independently chosen
contribution is substituted. Forwarding to a tail does not establish that the
tail's later constraints accept every atom.

`candidate_signature_view:733–782` retains annotation owner, p, allowed members,
tail and source provenance. `views[p]` shares the paired interface's view, while
different source row keys are not merged merely because their sets/tails agree.
Within one completed action, repeated `(s,x)` uses share a coordinate. This
does not prove independence across later uses or canonical row quotients.

The retained P/Q route establishes its local insertion/replay consequences;
neither this table nor stored bounds establish complete activation for every
source lower, current memo validity, or a negative residual consumer.

Oracle inspection confirms the distinction, without extending its operational
bridge. `infer/src/lowering/mod.rs:571–663` reverses Function arguments and
preserves results. `lowering/signature_effect.rs:78–107` retains positive row
variables/tails; `:319–370` uses the named tail or emits actual bidirectional
tail links; `:453–460` omits variables only from concrete grant collection.
`constraints/machine/bounds.rs:3213–3255,3285–3360` installs retained filters
and invokes their routines on existing/future lowers, recursively retaining
the obligation at variable encounters. Those facts do not supply a successor
attachment judgment or its Call/output interpretation.

## 4. First unsupplied negative construction clause

For every retained concrete row with C nonempty that the formal-tree recursion
reaches with Negative variance, `preflight_formal` returns false at that node
(`candidate_source.rs:117–121`). Its Boolean conjunctions propagate false to
the formal root. `preflight` returns `CandidateError::Unsupported` for that
formal (`:98–100`). Thus ordinary admitted formal construction supplies no
such negative transition. This is a direct static counter-premise to claiming
that the current source constructor emits the required negative view; it is
not a refutation of the annotation policy or an H counterexample.

Bypassing that first guard would still not supply the transition:
`candidate_formal_pair:1035` returns an error for the same concrete-negative
row; `candidate_formal_effect_port:1060–1070` has no concrete-negative case;
`candidate_signature_effect:1507–1509` independently rejects it. The general
annotation preflight also rejects concrete-negative rows (`candidate_source.rs:123–133`).
These internal errors are not proved public type errors. No source rejection
or acceptance theorem follows from their names.

The minimal retained tree exposing the formal guard is a Function with a
row-free Unit argument and a Unit result carrying C = [E]; its formal root
and result descent are Negative. An optional symbolic x does not avoid the
concrete-negative test. This tree is a constructor input description, not a
new successful parse/lowering/run claim.

The exact missing sequent is:

> From the actual resolved a,p,C,x,s,q at composed Negative, construct its
> authentic occurrence-local attachment set and executable subtraction view,
> with connected symbolic coordinates; submit the actual relation to the real
> typed consumer, preserving the exact applicable contribution and residual
> lineage for current/future lowers.

No such conclusion is obtained by reusing the supported positive pair. In
particular, `candidate_context.rs::source_weight:2174–2197` stores attachment
provenance with empty executable left/right words. Its `SourceUnitPush` flag
is prepared only for a Positive nonempty set. `materialize_unit_push:2200–2217`
is explicitly detached and does not form a live context, relation, bound or
registration. These records are not a reached subtraction transition.

The full attempted construction stops at this sequent. It does not proceed by
assuming attachments, maps or a complete consumer.

## 5. Residual lineage and the economy audit

Selected residual identity supplies a necessary preservation rule: identifying
source row coordinates must retain each recipe's original constructor lineage,
attachment/filter/origin/context, and fan every applicable lower to each recipe.
It does not construct an actual recipe or derive attachment independence from
equal or unequal row/operation IDs. `AnnotationMember(view,ordinal)` and a
Contribution instance are also different facts from a residual recipe.

The reviewed conditional contravariant proof §§4–7 already proves exact
contribution filtering with supplied attachments and complete-image premises.
Its two-contribution same-family example explains why projecting first cannot
justify deleting a whole support point. That algebra remains conditional here.
No new set-difference or row-quotient induction is used to simulate source
progress; actual recipe construction and all-path fan-out remain OPEN.

Two different prior methods left this same supplier untouched: the conditional
transport/filter proof supplied attachment and consumer hypotheses; the actual
P/Q bridge constructed positive views and located the negative guard. Applying
`compiler-engineering.md`, “Natural compiler behavior and proof-obligation
economy,” now yields:

- The negative constructor/consumer agreement is required A/B: selected hygiene
  and ordinary inference cannot be replaced by positive-only admission.
- Reconstructing attachment or recipe identity from equal rows/support is D
  debt. HIR and the formal action already possess p, C, x, s and q; their
  owning transition must preserve those inputs. Real contribution/Call evidence
  must still come from its separate owner.
- Another proof with supplied attachments cannot fill the source sequent.
  No obligation is downgraded or closed by this classification.

The smallest next **authorized internal transition** is the coupled negative
annotation constructor and its live attachment-local residual/check consumer,
using the selected private carrier of [contextual attachment/admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–4. Its output must retain one occurrence-owned set with member ordinals,
resolved operands, scope and symbolic connection; its actual emitted relation
must carry that evidence into exact residual/gamma obligations rather than
reuse positive allowance or publish dormant metadata. Establish the decisive
local invariant at these owners before a larger dependent implementation.

This is an owner handoff, not a new representation decision or enabling patch.
That design's §§5–6 explicitly keep general concrete-formal admission disabled
until the later admission/lifecycle/source gate. The existing guards cannot be
removed as this proof's repair. The next packet can construct the selected
internal transition without promoting ordinary source admission; if it needs
authority beyond that gate, the primary resolves that exact seam. Complete
Call and actual contribution attachment remain separate requirements.

The [same-task route audit](../progress/2026-10-12-oracle-same-task-route-audit.md)
§§3–4 and [typed-boundary adequacy attempt](2026-10-12-oracle-typed-boundary-adequacy-proof.md)
§§3–6 retain their distinct unsupplied Oracle seed/selected-map/attachment/force
join. This packet assumes none of that join and makes no H completion or
source-qualified hygiene counterexample claim. The Value-reference transport
choice is likewise not used.

## 6. Checks, coverage, dependencies and resources

Checks performed: bounded `cat`/`rg`/`sed` reads; read-only `git status --short
--branch`, `git rev-parse HEAD` and Oracle revision lookup; Python SHA-256 and
`git show` byte comparisons of the 16 Y3 and three Oracle dependencies below.
All matched their pins. Aggregate reads that truncated were followed by narrow
reads of the governing clauses and decisive owners. Final leased-file link,
whitespace and dependency checks are recorded in the handoff.

No compiler/test/shared-record edit, build, test, Oracle invocation, executable
probe, Git mutation, child dispatch or external contact occurred. Five
lightweight read shells were launched in the initial independent batch;
subsequent decisive source reads and hash checks were sequential. Heavyweight
processes, experiments and measurement samples: zero. CPU/RSS and total
reasoning wall time were not instrumented; one proof attempt stayed within the
45-minute packet bound. Document integrity checks are not semantic tests.

Requested routing: normal `gpt-6.1-sol` / `high` proof leaf. Config registers
prover, supplies those defaults, and its role file omits model/effort pins.
The live callable schema lists prover. Effective runtime model/effort metadata
is unavailable, hence unknown; no override, Astra execution or hot reload is
claimed. Independent review is pending. This producer cannot certify closure.

| Direct dependency | SHA-256 |
| --- | --- |
| hygiene integration | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| residual lineage selection | `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98` |
| contextual attachment/admission | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| concrete covariant implementation | `3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae` |
| top-level inference principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| complete Call contributions | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
| original H | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| reviewed actual formal-port P/Q | `f61b3a4f720c120a0a25681cbc4160e162e13b32066198b3f07e460fbfa2f7ae` |
| conditional contravariant proof | `faeaffecbd2aa6a50e4d82bc8924870148f784448d29aa893e9f5ddb89cb2ef9` |
| same-task route audit | `ffeaed5b1a3b55bb8d27a7918e8a851f750f40e93ec8d6026b796fa48733cc39` |
| typed-boundary adequacy attempt | `ff7d26f7a057988812ea1a86a586bf23b556113725e5b61afddff1f0374709cb` |
| `crates/yu-hir/src/module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| Oracle `infer/src/lowering/mod.rs` | `244e5f8ea339d2e24aa1f8456e99072e4a491b97da58348a4e79eed188ce61a1` |
| Oracle `infer/src/lowering/signature_effect.rs` | `9eec35dcbe721cec20b8cab302c409ec0bc014781a36d5287a781a6cb9fe50ce` |
| Oracle `infer/src/constraints/machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |

One next action: the primary assigns the exact internal negative
constructor/consumer sequent in §4 under the selected private carrier,
preserving the later admission gate. Review this frozen characterization with
the complementary source audit before adopting any implementation handoff.

## Commit packet

- Exact leased changed path: `notes/theory/2026-10-12-effect-hygiene-source-construction-proof.md`.
- Baseline SHA: `1f6ea89bffc69dfe614d5b20d25a353b9ea52a34`.
- Changed dependency hashes: none; pinned byte comparisons above, with final
  stability recheck reported at handoff.
- Review status: frozen unreviewed source characterization and obstruction;
  reused conditional clauses retain their stated review/scope. No established
  new global theorem, implementation authority or parent-goal closure.
- Checks already run: narrow static owner reads and dependency byte/hash checks;
  final document integrity check at handoff. No tests/builds/Oracle execution.
- Proposed one-line checkpoint: `research: pin effect hygiene negative construction premise`.
- Shared-record deltas left for primary/curator: link the current retained HIR
  annotation and concrete Support/Allowance owners; retain reviewed P/Q rather
  than reprove it; record the exact negative preflight/constructor sequent and
  dormant provenance. Keep full hygiene, source admission, residual fan-out,
  complete Call, soundness/principality, Value transport and F5 OPEN. No shared
  record was edited. Writes stop at handoff.
