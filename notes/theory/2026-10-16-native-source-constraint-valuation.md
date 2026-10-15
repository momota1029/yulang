# Native first Call: simultaneous constraint valuation and its source boundary

Date: 2026-10-16
Status: bounded constructive derivation of the actual scalar generator equations;
source semantic extension unresolved; independently reviewed local result.
Native baseline supplied by primary: `0a9af0da5080469f930da0032aa96d7d89d358c5`.
Exclusive output lease: this file only.

## Integration review and consumed next action

Independent compiler-referee `ordinary_carrier_semantic` reviewed the producer
artifact at `e977c90d0d85b025ec9a73a0aebfb93293dee902e68818ea785472a53c297c0a`
and returned CLEAN. The primary accepts the local equation/nominal-consumer
result only. The historical producer packet below retains its original scope.

The primary consumed the remaining premise by changing method: the
[consumer audit](../progress/2026-10-16-native-call-correlation-consumer-audit.md)
first tested a concrete discrimination attack; its missing source observation
is now supplied by the independently reviewed
[received-root instance](2026-10-16-native-returned-callable-incidence-instance.md).
The next active work traces that actual admitted pair through native consumers,
not another conditional interface-formation lemma. FIRST-RESULT-ADEQUACY and
its original universal quantifiers remain OPEN.

## 1. Frozen target

The source remains

```yu
my receive (f: () -> 'a) = { my g = f(); g() }
```

The original [classification](2026-10-15-callback-result-exposure-classification.md)
§1 fixes the receiver, formal, annotation scope, callback view, first Call and
pending Bind. Quantify over every original `xi=(nu,K,D)` and every returning
witness `z` of that complete first Call. Its actual packet `W_z` and matching
callee-result packet `F_R,z` are projections of the same `z`, with the same
provider, arguments, challenges and scopes. The required native interpretation
must admit that same return and both tagged images

```text
M_W* W_z  union_tagged  M_res* F_R,z
```

at the actual Apply result occurrence, with the original `nu,K,D` and matching
result paths. It must also satisfy the generated native predicates whenever
the corresponding original source obligations hold. Unsolved obligations stay
predicates; there is no requirement that every `xi` solve them unconditionally.
A source-indexed label placed on a row without interpreting its incident
constraints does not meet the target.

This pass concerns generation at the formal annotation and first Apply, plus
the Effect/Allowance consumers needed to give those constraints meaning. It
does not select handlers, implement receipts/resume, prove all native models
source-realizable, or close full B, hygiene, soundness or principality. The
second call's current scoped collector limitation does not narrow the source
quantifier. No additional seed, annotation or source restriction is allowed.

## 2. Authority and method

Governing source rules are typed-boundary §6, typed computation core §§3,6,9,
callback-context-delivery §§2,2.1,4, concrete-compatibility-boundary §1, and the
top-level inference principles §§1–4. In particular:

- a complete Function/Call view is compared in one endpoint-dependent query;
- successful concrete comparisons do not compose transitively;
- argument and result effects retain their joint source assignment/evidence;
- a typed packet belongs to a view and retains its original lineage;
- ordinary inference generates and accumulates unknown constraints.

The reviewed [source-origin construction](2026-10-15-native-call-result-source-interpretation.md)
and [static attack](2026-10-16-native-result-origin-falsification.md), integrated
at `f75299ea4`, establish source attribution and structural Result wiring, not
a source constraint model. The new
[activation note](2026-10-16-native-result-replay-adequacy.md) was read at the
supplied hash below. Its new claims were under review when this pass began; the primary subsequently
reported clean independent review and integration at `419c801bd`, with only
header/review prose changed. None is assumed as a semantic transitivity theorem
here. The consumed body hash and final integrated hash are recorded below.

The changed method is direct symbolic valuation of the actual generated
terms. It exposes a simultaneous solution schema for the scalar equations,
then checks whether that schema supplies the original packet/Call meaning.
It does not infer an interpretation from solver success or introduce a new
compiler relation. This is one bounded constructive pass, not another search
for an inverse from a bare row.

## 3. Actual common equations: a derived local result

Use `p` for the formal parameter row, `a` for the scoped annotation value
variable, `e_A,e_R` for the two omitted annotation effect ports, `r` for the
first Apply result row, `i` for its fresh invocation-effect row, `j` for its
application-effect row, `d` for the argument's effect row and `c` for callee
name evaluation effects. Signs below are actual endpoint polarities.

`candidate_effect.rs:1118–1160` recursively produces the paired formal terms

```text
F+ = Fun+(Unit−, e_A−, e_R+, a+)
F− = Fun−(Unit+, e_A+, e_R−, a−).
```

This is not an asserted source interpretation. It follows from the constructor:
Function argument variance reverses, result variance is preserved; each
omitted effect port is one freshly allocated row reused at both polarities;
the variable `a` is interned by `(AnnotationScope,name)`, separately from effect
variables. `candidate_formal_annotation:1185–1224` then admits exactly

```text
slot 43: F+ <: p−
slot 44: p+ <: F−.
```

`formal_domains[p]=F−` records the actual negative term. The source scheduler
calls this owner through `execute_candidate_action`, `candidate_source.rs:1302`.
This source case has no explicit outer computation-effect annotation requiring
`FormalEntry`. That separate owner at `candidate_effect.rs:1170–1183` equates a
symbolic entry tail at slots45/46 and explicitly does not turn concrete local
handling permission into a closed supplied-computation upper bound.

`shadow_apply.rs:1548–1625` creates

```text
D− = Fun−(u+, d+, i−, r−)
slot 0: p+ <: D−.
```

Here `u` is the actual collected Unit argument component. Its evaluation is
pure; generation may retain the component row and its bottom lower bound,
so literal equality of that row with the Bottom endpoint is not assumed.
The result `r−` is both actual demand field3 and retained
`NativeInterface.result`. This constructor does not copy the expected formal
into the demand. The same owner admits the two application-effect links
following slot0: callee evaluation `c+ <: j−` and invocation `i+ <: j−`.
There is no new result-profile seed from this explicit formal annotation.

When the ordinary variable-bound meeting actually pairs the slot43 lower
Function with the slot0 upper Function, `lib.rs:12590–12618` forms these
children from their actual fields:

| Field | Generated endpoint predicate |
| --- | --- |
| Argument | `u+ <: Unit−` |
| ArgumentEffect | `d+ <: e_A−` |
| ResultEffect | `e_R+ <: i−` |
| Result | `a+ <: r−` |

Meeting slot43 with slot44 yields the corresponding reflexive paired-field
predicates. This is elimination at the shared variable `p`, not composition
of two successful concrete Function comparisons. No unconditional assertion
that any particular replay executes is needed for this generation table.

### A simultaneous scalar extension, without solving unknowns

For the local table, let `A` be any interpretation of the one shared value
variable and `E_A,E_R,C` any effect-support sets. Give `d` empty support, `i`
support `E_R`, and `j` support `C union E_R`; leave `E_A,E_R` unknown symbolic
parameters. Give `p` the paired Function term above and give `r` the same
scalar value interpretation `A`. Every child predicate in the table is then
satisfied by Unit compatibility, empty-effect inclusion, or equality. The two
application-effect inclusions are simultaneously satisfied. Slot44 adds only
the same paired-field equalities. All uses of `a`, `e_A` and `e_R` use the same
assignment; there is no separately selected witness on either side.

This proves a local scalar extension schema, not the original theorem. In
particular it neither picks `E_R=empty` nor claims all native solutions have
this shape. If other accumulated constraints restrict these variables, those
constraints remain conjuncts of the model predicate. The schema alone does
not prove compatibility with an arbitrary surrounding native graph.

The proof is useful because there is no local contradiction caused merely by
the two annotation edges, omitted effect ports or fresh Apply row. It also
locates precisely where a source semantic interpretation must enter: `A`
must denote the original annotated view under `nu`, and the paired Function
and its `E_A,E_R` must denote the original complete callable view under the
same `xi`, rather than an arbitrary four-field product.

## 4. Effect and Allowance have a concrete native interpretation

A nominal support interpretation can be defined without a source oracle.
Its atoms are the actual contribution and annotation-member occurrences,
each carrying its retained `SourceEffectId`. Effect rows denote sets of such
atoms. Bottom denotes empty support. For view `v`, `Support(v)` is its
annotation-member atoms together with its tail support; `Allowance(v)` accepts
exactly atoms whose effect identity occurs in the view's executable allowed
list, or which satisfy its tail predicate. EmptyNegative accepts no atom.

These clauses are derived from `candidate_check_effect_operand:967–1030`:
Support enumerates every member and its tail; Contribution/AnnotationMember
against Allowance tests `allowed.contains(effect)`, routes an unmatched atom
to the tail if present, and otherwise records mismatch. Against EmptyNegative
it mismatches. Thus the interpretation covers actual atom comparison and
Support expansion; it is not a claim that a family match selects a handler.

For the executable zero-word fragment, a relation context contributes the
conjunction of the exact Allowance predicates of its validated filters,
together with the residual context predicate. `candidate_zero_word_filters`
checks owner, position, closed-weight identity and empty words before exposing
the filters (`candidate_context.rs:3075–3155`). The live consumer at
`3190–3289` applies each resulting `lower <: Allowance(view)` constraint, or
replays an already registered bound with this occurrence's origin. It retains
a residual when needed. Value tasks cannot be interpreted as if they had
consumed these Effect checks. Non-executable fragments returning availability
failure are not successful semantic discharges.

A source-owned view and its weight are constructed at
`candidate_effect.rs:747–795` and `candidate_context.rs:2401–2427`. Owner,
position, allowed members, optional lexical attachment and tail are retained.
This permits a compositional *nominal predicate* for these consumers. It does
not yet identify that predicate with the full source typed-boundary predicate
in `K,D`. The weight's words are literally empty; dormant unit-push preparation
is not a live source-semantic proof.

In particular, replacing an original dependent source request by just its
family in the interpretation would be an unjustified quotient. The native
nominal predicate is a projection of the requested source domain. Its ability
to be lifted back to that domain is the semantic question, not a consequence
of the membership code.

## 5. Exact unresolved law; why the scalar construction does not close it

The required domain must contain complete source value views and complete
computation/Call observations, indexed by the original source binding and
`xi`. Typed request atoms retain their dependent arguments, `K,D`, packet
paths, scopes and pending continuations. A native relation occurrence denotes
an endpoint-dependent predicate on those objects; a native row variable has
one common assignment across all its incident relations. Copy maps, when
reached, must reindex that assignment by their actual retained maps. Raw Term
identity cannot equate different typed views. Native effect support is only a
projection of this domain.

The smallest unresolved generation law is at the paired formal constructor
and its first Function decomposition:

> Given the original complete callable view for `f: () -> a` under `xi`,
> construct interpretations of the paired formal terms and the shared
> omitted ports `e_A,e_R`, using that original view's role and entry, such
> that the actual Function child predicates denote its complete Call
> obligations, and its Result child admits both tagged images of the same
> return `z`, jointly with the Effect/Allowance predicates under the original
> `K,D`.

This is a semantic formation/decomposition law for this local source formal,
not a general composition law for concrete successes and not arbitrary-native-
model equivalence. The whole source domain of `a`, including callable returned
values, remains in scope. The law must be uniform over all original `xi,z`;
choosing new marginal providers for the two result inputs is insufficient.

The preceding scalar proof does not establish this law. Assigning `r=A`
satisfies `a <: r`, but does not define the two typed result views, their tagged
maps or their shared dependent predicates. Interpreting `r` afterward as the
source answer merely repeats the already accepted source-origin labeling.
Likewise, the nominal support domain proves membership checks but cannot by
itself interpret the original Call's dependent challenges or the matching
callee-result packet. Choosing universal effects would make the local scalar
clauses easy and still would not establish that interpretation.

The selected contract itself identifies this seam: callback-context-delivery
§2 fixes complete-interface formation and says its final inequality is an
obligation, not a defined port rule; §5 says `Force(D) >>= B` does not license
independent port subtyping or unconditional row union. Concrete-compatibility-
boundary §1 requires the two effect descriptors to be compared jointly under
the original assignment and leaves their source interface bridge as a proof
obligation. Therefore replacing the complete callable view with the four-field
nominal model above would add an unapproved semantic law. The actual generator
builds exactly those four terms; its retained source input and parent edges
identify where the required law applies, but do not establish that law.

This is a tight obstruction to *this proof method*, not a demonstrated compiler
counterexample or an impossibility theorem. No pair of source-qualified
indistinguishable packets was found. Forward model extension may exist. This
pass has not established it, and absence of a previous published interpretation
is not used as a falsifier.

## 6. Economy audit and next owning action

The unresolved law is the original A/B source-generation adequacy premise.
It is neither retired as stronger characterization nor reclassified as
reconstruction debt. Existing source inputs, same field3, original formal
registration and ordered parent records remain available. No actual discarded
source certificate has been demonstrated, so this result does not justify
adding metadata, runtime packet evaluation, a registry, or rejecting source.
A third replay-only or source-origin decoder proof would leave the same
semantic premise untouched.

Next action: at `candidate_formal_value_pair` / `candidate_formal_effect_port`
and the four Function children, derive the complete role-indexed interface
formation law for this source formal from the selected source Call rules,
including an explicit interpretation of the omitted AE/RE ports and the
Result typed-view maps. Check its Effect predicates against the nominal
Allowance projection above under the same `xi`. This is a source semantic
proof task before any new code strategy; it is not a request to execute or
solve source packets during inference. If those source rules do not determine
the law, the primary must adjudicate that exact specification seam rather than
silently choose independent-port semantics.

FIRST-RESULT-ADEQUACY, full B, hygiene, soundness and principality remain OPEN.
The scalar schema and nominal consumer characterization can be consumed as
local evidence, subject to independent review; neither closes their parent.

## 7. Checks, resources and commit packet

Read-only commands: bounded `sed`, `rg`, `cat` and dependency `sha256sum`.
No Git operations, compiler edits, tests, builds, executable probes, delegates
or other output paths. One bounded constructive pass; no runtime measurements,
seeds, samples or heavy processes. Wall-time budget approximately 15 minutes;
CPU/RAM uninstrumented. Requested routing: normal Sol/high per primary packet;
observed effective model/effort metadata unavailable. No override requested.

```text
deee5a0892b02bc9ee23a1f2a35c76175094c558ed7dfb2cf55a7e115ac54225  crates/yu-solver/src/candidate_effect.rs
9f71c8c40d6850bffccb27d7393bf6219f0ceca5cf1fe1e738073ea943706083  crates/yu-solver/src/candidate_context.rs
270ee70b331e4095f404fafafdf0731b57dd451c130cdf251aea2b5944d7cc6c  crates/yu-solver/src/shadow_apply.rs
a37c0c605802fc482c20a59199eea7a09b56ab966454db2b11dfe2d62b1dead7  crates/yu-solver/src/lib.rs
75c4f8d923b95b55b27e849aa32c2fb37ed7db854b18e97712a945146ba95c52  notes/theory/2026-10-16-native-result-replay-adequacy.md (body consumed)
b5473ec1e22b53395c1bcc73c38c4b723f8ac769ac1ababf041aaed76c887d0f  notes/theory/2026-10-16-native-result-replay-adequacy.md (final integration; primary supplied)
```

- Lease / changed path: `notes/theory/2026-10-16-native-source-constraint-valuation.md` only.
- Baseline: `0a9af0da5080469f930da0032aa96d7d89d358c5`, supplied by primary.
- Changed dependencies: none against the supplied native inventory; no direct
  Git baseline comparison performed. Consumed Astra dependency hash matched its
  packet; final header-only hash update is supplied by primary.
- Claim class: derived local scalar extension and nominal consumer predicates;
  original source semantic extension unresolved. Fresh independent review pending.
- Proposed checkpoint message: `research: derive native first-Call valuation equations`.
- Shared-record delta left to primary/curator: record exact formal-interface
  formation/decomposition law as remaining owner action; preserve all parent
  OPEN statuses and distinguish the scalar result from source-model adequacy.
