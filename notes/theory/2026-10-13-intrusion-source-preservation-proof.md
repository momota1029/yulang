# Occurrence-qualified intrusion: native equality lift and source-scope obstruction

Date: 2026-10-13
Status: unreviewed constructive research; original preservation theorem OPEN
Baseline: `bf0420584b190654eca081257c9d7698361210f0`
Branch: `research/simple-sub-intrusion`
Reference: `9bae772624c23b52a93c1b226157e16898b4d9db`
Exclusive lease: this file; proof leaf, no further delegation

## 1. Frozen original statement

For **every supported original source program**, every lawful finite
Simple-sub construction history, and every actual retained extrusion
occurrence e, retain e's actual origin and receiving source Values and every
actual polarity-specific parent/copy pair produced by e. Qualification is
equality of the two Values' components in the approved source-reference
graph. It equates precisely e's retained pairs. Fresh use is not extrusion;
copying descriptions does not copy or retarget source references.

Required conclusion: the resulting inference preserves original source
typing conclusions and required principal coverage, soundness, ordinary
inference progress and termination. The comparison retains original lexical,
type and event scopes, recursive monomorphic sharing, generalization and
lawful uses, complete Call, effect hygiene and all correlated source evidence.
It ranges over the original supported domain, including its ordinary natural
programs. A source-qualified counterexample may refute the conclusion.

Source binders, declaration/provider identities, captures, whole arguments,
receivers, actual events, guards, attachments, witnesses and residual recipes
keep their original meanings. Joint evidence is chosen once at its original
scope. No arbitrary old solver assignment, independently chosen marginal
witness or changed source domain is added to the required conclusion.

Hypotheses are the independently applicable original local source laws and
the approved occurrence/Value-graph rules. Missing source laws are reported
as missing premises, never presumed true. The event qualification does **not**
require a separately constructed source term for a native copy, a source
`Desc` for every native coordinate, or Source-Generalize component `K_g`.
`K_g` is needed only when applying source publication/allocation to the actual
history. Neither `K_g` nor a fixed/template classification is inferred from
a Value SCC or a numeric level.

Exclusions from claimed closure: arbitrary assignment preservation, altered
ordinary inference, new source restrictions, an adopted scheduling/encoding
policy, compiler implementation, production/F5 cutover, and independent
certification. These exclusions do not remove any case from the parent claim.

**Outcome.** A direct native-constructor argument gives a pointwise diagonal
extension for each finite extrusion at an unextruded demanded-comparison cut.
This is a conditional local derivation, pending review. It does not establish
a source-admissible strategy through publication and use. The first missing
semantic premise is that the generated equalities have a lawful joint lift
at the original source scopes, including independent description frames and
all fixed source dependencies. No original-scope proof or genuine full-Yulang
counterexample is established. The parent remains OPEN.

## 2. Governing sections and inputs

- [Top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md), §§1–5 and Authority and integration: native generation, accumulation, propagation, levels, extrusion, intrusion and generalization; no typing search or unconditional rollback objective.
- [Selected operation](../design/2026-10-10-parent-copy-scc-intrusion.md), Selected operation and compiler responsibility; Value-reference SCC clarification; Apply-result source-fragment ownership; Nested Apply membership; Definition-root Value ownership; Retained boundary.
- [Occurrence qualification](../design/2026-10-12-intrusion-value-type-association.md), Approved extrusion-event qualification; Definition-root origin for nested call-demand extrusion; Qualification; Implementation and proof boundary. The odd/even event is `(E,O)`, with actual pairs `C=T` and `D=R` when those copies are produced.
- [Copied-row ownership](../design/2026-10-12-value-reference-copied-row-ownership.md), Decision and Scope and proof boundary.
- [Source Generalize](../design/2026-10-08-source-generalize-definition.md), §§2–5, selecting [construction](2026-10-08-source-generalize-definition-and-proof.md) §§3–5; especially local schemas §3.1, typed owners §3.3, Build §4, fixed closure §5.1 and allocation §5.2. The construction's §8 states its source-principality and production exclusions.
- Original paper `/home/momota1029/rust/simple-sub-reference-paper.pdf`, §§3.5.1–3.5.2, Figs. 6–9, §5 introduction/footnote 15, §§5.2–5.3; pinned original `shared/src/main/scala/simplesub/Typer.scala` and `syntax.scala`.
- Earlier [odd/even inference](2026-10-12-cross-level-odd-even-inference-derivation.md), §§1–7; [native pair derivation](2026-10-12-odd-even-parent-copy-scc-derivation.md), §§2–5; [copy-qualification note](2026-10-12-odd-even-copy-qualification-proof.md), §§1–3 and its applicability correction. Its type-copy nonreachability application is withdrawn, not reused.
- [Publication incidence](2026-10-12-intrusion-publication-incidence-bridge.md), §§3–5; [quotient correspondence](2026-10-12-quotient-solution-correspondence-proof.md), §8's level/generalization discriminator; [qualified odd/even](2026-10-12-odd-even-qualified-intrusion-derivation.md), §§1–3; [correlated-helper search](../progress/2026-10-12-intrusion-occurrence-counterexample-search.md), §§1–3.

Method: derive equal-copy extension from the **actual native extrusion
constructor**, then locate the missing step in source completeness induction.
Falsifier: a supported source derivation whose qualified equalities reject
its lawful typing or lose required principal coverage, or an intrusive accepted
result with no original lawful source derivation. No supplied checker or
test run is offered as proof of source generation or consumer activation.

## 3. What original Simple-sub principality supplies

The original paper states soundness and completeness/principal schemes in
§5.3. Its proof sketches explicitly restrict to the **non-let-polymorphic**
algorithm (§5 introduction). Footnote 15 proposes separately relating let
polymorphism to use-site duplication. It is not a printed proof of the leveled
extrusion/generalization extension, and none of it proves occurrence-qualified
intrusion, complete Yulang Call or effects. The implementation supplies exact
native constructor evidence, not that missing theorem.

In the non-let completeness sketch, a source derivation is accompanied by
a substitution `rho`; induction constructs a new substitution `rho'` preserving
the source environment and covering the source conclusion. Thus completeness
permits changing internal assignments. It does not require preserving every
assignment of an unconstrained pre-intrusion store. A principality argument
for intrusion must extend that *source-derived* substitution/strategy step.

The native let algorithm has a deliberate additional responsibility:
`freshenAbove` copies above-boundary variables with one coherent map and keeps
lower variables shared. The paper §3.5.1 explicitly uses extruded one-sided
approximations to permit independent subsequent instantiations within shared
bounds. Equating an approximation with its parent can affect this independence.
Baseline principality cannot be imported to justify this new transition.

Source Generalize supplies a separately reviewed source-lawful subsystem
construction relative to local laws. It retains all source clauses and scopes;
its §8 does not prove all-language source principality or extrusion coverage.
Neither imported result closes the parent theorem.

## 4. Direct native extrusion derivation

Fix one completed finite invocation of original `extrude(t,p,l)` and its
pre-extrusion bound store sigma. This section is about ordinary algebraic
type values at a **single pointwise constraint cut**. It does not treat a
numeric level as a source dependency telescope or quantify away source scopes.

Assume a valuation rho satisfies every old bound in sigma. When this extrusion
is used to rewrite a demanded comparison, assume rho also satisfies that
**original unextruded comparison**. This is an explicit antecedent; rho is
not an arbitrary solution of old bounds without the source demand. Deriving
such rho from a complete Yulang source judgment is the separate bridge below.

For each actually allocated polar copy c of old variable a, set

```text
rho*(old a) = rho(a)
rho*(new copy(a,p,l)) = rho(a).
```

All copies created by that invocation, including opposite-polar copies of the
same parent, are assigned jointly by this one rule. Their recorded identities
and polarities stay distinct. The claim is:

```text
rho*(extrude(t,p,l)) = rho(t),
rho* satisfies every bound directly introduced/copied by this invocation,
rho* satisfies each of its parent/copy equalities,
and rho* satisfies the rewritten demanded comparison.
```

**Derivation from `Typer.scala:134–159`.**

1. At an already acceptable level, extrusion returns the original term;
   Primitive is also unchanged. Interpretation is identical.
2. Function recursively extrudes the argument with flipped polarity and the
   result with unchanged polarity. Record recursively extrudes each field.
   If the child interpretations agree, the rebuilt constructor's interpretation
   agrees, including the Function's contravariant argument meaning. There is
   no independently selected argument/result valuation.
3. At a wrong-level variable a, a new c is allocated and the polar memo is
   populated **before** its selected bound list is traversed. c has exactly
   rho(a) by the displayed construction.
4. Positive extrusion appends `a <: c` and copies the selected lower list of
   a to c after recursively extruding its entries. Negative extrusion appends
   `c <: a` and copies the selected upper list. Each direct link holds by
   reflexivity under rho*. A selected entry need not predate this invocation:
   recursive traversal may already have inserted a link for the other polarity.
   Distinguish its two possible origins. A pre-existing lower b belongs to
   sigma, so `rho(b) <: rho(a)`; a pre-existing upper b gives
   `rho(a) <: rho(b)`. Recursive extrusion preserves its interpretation under
   the same simultaneous substitution, including memo hits as in step 5.
   Fresh additions to an original variable's lists are exactly this constructor's
   parent links; copied selected bounds are installed on fresh copies. Thus a
   newly selected lower d of a is an earlier negative copy with `d <: a`, and
   a newly selected upper d is an earlier positive copy with `a <: d`.
   Both endpoints map to rho(a), so these selected bounds hold under rho*
   without an old-bound premise in sigma. Such d is at target level l;
   recursive extrusion returns d unchanged. For example, positive extrusion
   of `Function(a,a)` can first insert `c_minus <: a` in its argument traversal
   and then copy c_minus into c_plus's lower list in its result traversal.
   All three coordinates map to rho(a), so `c_minus <: c_plus` holds as well.
   This covers both pre-existing and freshly inserted selected bounds jointly
   throughout the recursive traversal, with the shared polar memo in step 5.
5. Memo hits return the same c. Cyclic bound references are discharged by
   simultaneous substitution, not induction down an infinite unfolded type.
   Interpret each finite structural bound term under the one variable
   substitution; replacing any memoized variable leaf c by its parent a
   leaves that term's interpretation unchanged. This handles shared parents,
   both polar keys and finite cyclic bound graphs without assuming independent
   witnesses for recurrent occurrences.
6. The rewritten demanded comparison has the original interpretation, so its
   antecedent gives satisfaction. Any selected subset of these fresh pairs,
   including the actual occurrence-qualified subset, is already equal under
   the same extension. SCC membership is unnecessary for this local algebraic
   existence fact; it remains necessary for deciding what the algorithm does.

This proves more than an equality quotient of an already supplied store:
the actual extrusion recursion generates constraints for which a lift of a
solution of the **original demand** is explicitly constructed. No comparison
is required to succeed at generation time. Nor does this prove operational
completion: ordinary opposite-side replay must still run, a rewritten demand
must actually be installed, and pending comparison markers must remain valid.

The same constructors give a local soundness direction without diagonal
assignment. In every satisfying interpretation of their retained links,

```text
interpret(t) <: interpret(extrude(t,+,l)),
interpret(extrude(t,-,l)) <: interpret(t).
```

For a variable this is its directly inserted link. Function reverses its
argument order, exactly matching the flipped recursive polarity; Record
preserves field order; acceptable terms are reflexive. Consequently a stored
negative-extruded upper demand implies the original upper demand by
transitivity, and a stored positive-extruded lower demand implies the original
lower demand. Adding any qualified pair equalities retains these implications.
Thus the actual local constraints neither need arbitrary-assignment
preservation for soundness nor justify losing the completeness obligation.
This is constraint-meaning soundness at that cut, not compiler/source
soundness: canonicalization must retain all clauses, and complete source
Call/effect meaning must still correspond to them.

The same local construction can be composed over a finite list of extrusion
invocations **if** the current joint valuation satisfies each original demand
at its cut. That if is material. It is not evidence that a source derivation
produces one admissible valuation/strategy through every publication, use and
effectful event of an arbitrary history.

For native Function/Record/Primitive constraint satisfaction, old retained
bounds and the rewritten comparison are all checked above. No theorem for
Yulang effect Allowance/Support, contextual replay or source witness binding is
deduced from those three native constructors.

## 5. The exact missing source completeness step

The local extension is pointwise. A source derivation is scoped: a description
choice may depend only on its original telescope; a Shared choice is made
once; independent incoming frames have separate eligible descriptions;
aliases and recursive occurrences share their prescribed tuple. The value
`rho(a)` in §4 can therefore be unavailable to a copied coordinate at its
actual source scope, or vary between client frames while that coordinate is
shared. Equality of two Values' SCCs supplies neither dependency permission
nor a typing derivation for the reverse of an approximating inequality.

The **first missing induction premise**, at a qualified App/Call-demand
extrusion e, is this:

> Invert the actual complete source rule generating e's demand and its native
> coordinates. For every lawful source derivation needed for required typing
> coverage, construct one joint source-admissible description/evidence
> strategy satisfying the same rule and every selected pair equality, at the
> original scopes. Preserve its complete external conclusion, fixed source
> fields and all dependent evidence. Show that its stored relation and lawful
> independent-use allocation preserve those same incidences. This strategy
> may change internal type assignments; it may not change the source provider,
> original scopes or the required source conclusion.

This is a localized missing source-to-operational completeness premise,
not an extra adopted success axiom, a reconstruction layer or a substitute
definition of source legality. It is needed where the native completeness
induction would extend `rho` to `rho'` across the selected intrusion transition.
It has not been established by the authority documents or inspected producers.

There are two separable duties. The native source-demand correspondence must
first establish the actual complete constraint/evidence clause and scopes;
the equality lift must then be proved lawful for that clause and allocation.
An event record supplies activation and pair provenance, not the latter
semantic result. Source-Generalize `K_g` and typed publication dependencies
are inputs to the second duty; they are **not** additional qualification tests.

### The existing correlated helper pinpoints the scope failure

Use the existing original-reference source, without inventing new clients:

```text
let rec f = lambda x.
  let g = lambda y. (lambda z. y) (f y)
  in {a = succ (g 0), b = g true}
in f
```

Native introduction gives level-1 monomorphic o and level-2 B for y and R
for `f y`. Demand extrusion produces actual `(C,B,+,1)` and `(D,R,-,1)`.
Definition roots give `F -> G -> F`; origin G/receiver F qualifies the event.
The wrapper's returned-input correlation is retained; its discarded recursive
result and its actual Call have not been erased.

The already derived ordinary history uses distinct B0/S0 and B1/S1 after
boundary-1 freshening, sharing C. It generates

```text
int <: B0 <: S0 <: V0 <: int,
bool <: B1 <: C,
B0 <: C.
```

The ordinary algorithm replays these successfully. If the source equality
relation routes `B0=C_base=B1` through both lawful use frames, it additionally
requires `bool <: int`, a primitive failure. At a single initializer cut §4
can choose `C=B`; it cannot use that same shared choice as both independently
refined B0 and B1. Pointwise diagonal completion and scoped allocation are
different proof steps.

This is the established **conditional discriminator**, not a newly certified
Yulang source counterexample. Source admission, complete Call/effects and the
actual publication dependency record must determine whether C is that shared
base incidence, an internal coordinate carried with a whole component frame,
or another lawfully classified occurrence. The operation's activation is
already settled. Lowering numeric metadata to 1 does not establish this source
classification. Nor may the proof choose the convenient classification.

The quotient correspondence note §8 independently shows that raw numeric
freshening and quotient-first numeric freshening need not commute. Settling
before publication avoids a stale view of the quotient; it does not prove
preservation of required ordinary source typings. Settling after allocation
requires lawful handling of existing frames. No schedule is adopted here.

## 6. Exact odd/even discriminator

Keep the original source and scopes:

```yulang
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

O/E are the original definition Values; a/b are distinct outer/inner formal
binders, with b shadowing a. O is active and monomorphic during E's initializer.
The inner body belongs to E. E publishes at the enclosing boundary 1 and O
eventually at 0. Arithmetic, comparison, the original test and ordered arms,
the actual declaration of `true`, providers, complete Call and effect clauses
remain present. No Call-only source is substituted for this text.

The approved origin is E and receiver O. Original root incidences give
`O -> E -> O`, so this occurrence qualifies. Let T be the actual subtraction
result and R the inner Call result. Native negative demand extrusion produces
`T_plus=extrude(T,+,1)` and D from R. If T is a high variable, it produces C
with parent T; otherwise no invented C/T variable pair is added. This is the
actual argument occurrence, not automatically the formal B.

At a pointwise native cut where a lawful original demand valuation is given,
§4 sets `C=T` and `D=R` jointly and satisfies the demanded comparison and
copied selected bounds, regardless of existing bounds. This shows why a
ground arithmetic/boolean case need not exhibit the correlated-helper conflict.
It does not provide the missing exact-source Branch/operator/Call derivation.

The separate qualified odd/even note uses an eleven-App reference elaboration
with expressly supplied `le:Int->Int->Bool`, `sub:Int->Int->Int` and the
reference polymorphic `if` builtin. Under its explicit quotient, level and
pending-cache transition, it derives the same simplified `int -> bool`
as stock inference. Those are **conditional reference premises**, not authority
that this is the exact Yulang Branch elaboration, or a general principality
proof. In particular its resumed cache cannot simply retain the canonicalized
in-process comparison: that could skip demand insertion. This operational
issue is independent of the semantic equality-lift premise.

Thus odd/even supplies a useful positive finite discriminator and authentic
pairs. It proves neither the all-source statement nor a source-qualified
failure. Exact current source admission is also incomplete in the prior HIR
audit; this is a bridge gap, not a permitted narrowing of the parent domain.

## 7. Actual owning construction and consumers

The following are inspected source owners at the pinned baseline. They are
not a complete successful intrusive source history.

| Responsibility | Exact owner and observed behavior | Remaining bridge |
| --- | --- | --- |
| Native recursion, Call demand and local publication | Reference `Typer.scala:48–83`: recursive placeholder, monomorphic lookup, Lambda, App demand; boundary-carrying scheme | Complete Yulang source rule/Call/effect correspondence |
| Native guarded accumulation/replay | Reference `:88–127`: cache before extrusion; insertion followed by all opposite bounds | Intrusion-aware validity of pending/cache work; complete successful replay |
| Actual native polar copies | Reference `:134–159`: memo before selected-list copying; opposite-side parent link | Original source telescope and publication incidence of each generated coordinate |
| Native independent instantiation | Reference `:166–188,201–207`: one memo per freshening; low rows retained; monomorphic lookup unchanged | Correspondence with source whole-frame allocation and fixed dependencies |
| Apply source occurrence | `candidate_source.rs:394–411`: `ApplySourceInput` has definition owner, callee/argument, level, result and effects | The owner is not a complete retained extrusion-event record with actual receiver and all produced pairs |
| Native demand | `shadow_apply.rs:1335–1385`: argument Value/effect, invocation effect and result Value are retained separately | This four-port projection is not the original complete Gen-Call-0 rule |
| Wrong-level rewrite | `lib.rs:12412–12454`: candidate extrusion rewrites the comparison and enqueues the rewritten demand | Source occurrence transport and all pending continuations |
| Candidate copies | `candidate_extrusion.rs:21–163,224–250`: row/structural memo, fresh target-level copy, parent retention, link insertion, selected bounds; four Function ports with correct polarity | Complete source clause and scope bridge; effect view/capture behavior lies outside §4 |
| Parent record and qualification | `candidate_intrusion.rs:23–28,171–220,358–488`: `Parent` stores copy/parent/polarity/target; SCCs are built on solver endpoints/bounds/ports and compare copy/parent representatives | It does not implement approved origin/receiver Value-SCC qualification |
| Actual merge and replay | `candidate_intrusion.rs:513–605`: transfers both bound sides and origins, combines minimum levels/non-generic flags, redirects representatives, canonicalizes context, reopens root and replays lowers | Not a proof of original source typing, complete contextual activation, or source lawful allocation |
| Contextual opposite-bound replay | `candidate_extrusion.rs:763–804`: creates lower/upper input keys, begins and drives contextual replay | Stored constraints alone do not prove return/discharge or all future recipe consumers |
| Later Function consumer | `lib.rs:12493–12536`: argument Value/effect and result Value/effect comparisons remain separate | Complete Call/effect/attachment/witness correspondence |
| Source local boundary | `candidate_source.rs:254–328`: nested initializer increases level; installation separates one-shot initializer effect | Numeric boundary is not Source-Generalize typed dependency classification |
| Live local scheme installation/use | `candidate_scheme.rs:1316–1334,1362–1382`: root/boundary installed and live graph captured for use | Full source `ScopedClosure`, validating component and allocation correspondence |

`candidate_call.rs:91–130` explicitly retains a list of missing original
Gen-Call-0 inputs and states that a negative Function/scalar provenance is not
original typing. The producer/consumer trace therefore exposes concrete
owners rather than assuming the projected native demand supplies complete Call.

The merge moves actual context provenance rather than licensing its erasure.
This note does not identify equal row representatives with equal attachment,
provider, witness or residual-recipe identities. Their original correlated
obligations remain part of the required source theorem.

## 8. Progress, termination and obligation economy

Original extrusion visits each applicable polar variable once in its local
memo and each finite structural occurrence in the traversed bound payloads;
memo hits terminate cyclic variable traversal. This is a finite-local-extrusion
argument. A fixed finite set of rows also permits only finitely many successful
representative identifications. Neither fact bounds rows created by subsequent
extrusion/freshening, repeated source events, contextual replay or invalidation.
The paper's non-let constraining termination sketch does not settle that
combined history. No all-source termination conclusion is claimed.

Ordinary progress additionally requires the rewritten demanded comparison
and all retained continuation obligations to activate. The inspected enqueue,
reopen and replay owners identify where that must be proved. A satisfying
pointwise lift or a parent record is not proof that they complete. Successful
suspension retains its accepted facts and continuation under the top-level
principles; complete failure restoration is not imposed here.

The earlier fixed-anchor native rejection attempt and the publication-incidence
attempt left the actual source clause/dependency/allocation premise untouched.
Apply the existing proof-obligation-economy audit before another variant:

- Equality preservation, scope-safe source adequacy and inference progress are
  A; required lawful independent-use coverage/principality is B. Keep them OPEN.
- Recovering event endpoints and dependencies from row IDs or bounds is D.
  App/Call-demand, extrusion and registration must retain their own known
  construction evidence. That can remove reconstruction debt; it cannot make
  an unjustified equality source-complete.
- Preserving all arbitrary old solver assignments is C without a separate
  source contract. It is not added as a cutover prerequisite.

Section 4 is a different, direct attack on the native equality step, with
an explicit generated-constraint lift; it **does not** count the unchanged
source premise as parent proof progress. Another pointwise quotient lemma,
larger finite search or different obligation wording would not discharge it.
No third equivalent proof route is proposed.

**One next action:** at the actual App/Call-demand and recursive-registration
owners, construct the complete source clause and publication record for the
existing correlated helper, including its original parameter declaration,
event pairs, typed recursive edge and fixed dependencies. Apply the already
selected Source-Generalize allocation and decide whether the two genuine g
uses share C. This directly determines whether the existing conditional
`bool <: int` rejection is source-qualified or whether a lawful whole-frame
lift resolves it. Retain original scopes and complete Call/effects; neither
classification nor a chosen convenient allocation is evidence.

## 9. Checks, resource use and frozen dependencies

Evidence: bounded `cat`, `sed`, `rg`, `pdftotext -layout ... -` reads, original
constructor hand derivation, SHA-256 reads, read-only branch/revision inspection
and exact-note whitespace inspection. Some large initial captures truncated;
all decisive rule, source and theorem sections were reread in bounded windows.
No builds, tests, inference executions, executable probes, benchmarks, network
lookups, Git mutations, external messages or child assignments occurred.
Primary owns verification, integration and independent review.

One reasoning lane, up to four concurrent lightweight read commands in an
initial batch; no heavy process, inference/performance sample or measured CPU
or RSS. Work is bounded by the assigned 45-minute limit; exact reasoning time
was not instrumented. Requested routing: Sol `gpt-6.1-sol/high`. Observed
assignment: `/root/prove_intrusion_source_preservation`; effective runtime
model/effort metadata: **unknown**. `.codex/config.toml` registers prover and
normal Sol/high defaults; `prover.toml` has no model/effort pins. Those facts
do not establish effective execution settings. No Astra or hot reload claimed.

Direct dependency SHA-256 snapshot:

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| `notes/design/2026-10-12-intrusion-value-type-association.md` | `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775` |
| `notes/design/2026-10-12-value-reference-copied-row-ownership.md` | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/theory/2026-10-12-cross-level-odd-even-inference-derivation.md` | `839e80f5c1426531bb761d9ae6ef9475d8f89104e766a5973c356656f89ae41c` |
| `notes/theory/2026-10-12-odd-even-parent-copy-scc-derivation.md` | `238e21c0a027aa9f0ca14c563c3fbaa11188ee268e8b819a049f81dd6afd5830` |
| `notes/theory/2026-10-12-odd-even-copy-qualification-proof.md` | `efffb130ce708d6cbe89a42a0b482d62c9dd93dceedb345fd084ad6370cc3bae` |
| `notes/theory/2026-10-12-intrusion-publication-incidence-bridge.md` | `5ce57b450d52cf575aed227d943b7856a8cf1a77d73c067df8f043f3201be94a` |
| `notes/theory/2026-10-12-quotient-solution-correspondence-proof.md` | `5c93588f2fce49ce2dad6ece1c7265a61b8bac7f648263c098ba2c5746443711` |
| `notes/theory/2026-10-12-odd-even-qualified-intrusion-derivation.md` | `2ad8de75a5ab2da68128db01b9a98c193eaba8ccf5e36e7411d5720425248cb9` |
| `notes/progress/2026-10-12-intrusion-occurrence-counterexample-search.md` | `ef308b68e967d916278b2d6e106731c723368f0477ecc947a12eb99c7f17a956` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/candidate_call.rs` | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| `crates/yu-solver/src/shadow_apply.rs` | `cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| Reference `Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| Reference `syntax.scala` | `f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f` |
| Reference paper PDF | `5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698` |

No dependency was edited. A read-only `git diff --name-only` against the
pinned baseline returned no changes for the listed repository dependencies.
An earlier note's different `shadow_apply.rs` hash was not used as this
packet's baseline; the current hash matches the pinned baseline. Integration
must still revalidate any subsequent concurrent changes.

## Commit packet

- Exact leased/changed path: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` only.
- Baseline SHA: `bf0420584b190654eca081257c9d7698361210f0`; reference SHA: `9bae772624c23b52a93c1b226157e16898b4d9db`.
- Changed dependency hashes: none caused by this leaf; direct snapshot above. Integration must revalidate any concurrent dependency changes.
- Claim/review: unreviewed local native equality-lift derivation and bounded owner/obstruction characterization; original all-source theorem, source counterexample and production correspondence remain OPEN. No independent review or self-certification claimed.
- Checks already run: exact original/rule/consumer reads, hand native extrusion derivation, branch/reference identity and dependency hashes, note whitespace inspection. No tests, builds or executable inference.
- Proposed checkpoint message: `research: derive native intrusion equality lift and isolate source scope premise`.
- Shared-record deltas left to primary/curator: record the native pointwise lift separately from source-scoped completeness; imported paper principality excludes let-polymorphic proof coverage; qualify the old helper rejection by actual source publication/allocation; keep complete Call, effects, source adequacy, soundness, required principality, ordinary progress, termination and F5 gates OPEN. No shared record was edited. Writes stop before frozen review.
