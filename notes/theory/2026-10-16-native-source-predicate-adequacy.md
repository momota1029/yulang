# Native Result predicates: same-witness projection and declared-support boundary

Date: 2026-10-16
Status: bounded constructive predicate analysis; original adequacy NOT proved.
Independent review CLEAN for the bounded conclusions below. Baseline supplied by primary: `1e62dfdc3` plus the
frozen G3 source hashes in §8. Exclusive lease: this note only.

Independent review: compiler-referee `ordinary_carrier_semantic` returned CLEAN
at producer SHA-256
`bfd285fcf0a2eaf0d37bee0c6fa9ab8c29573f10e6810fa5a9ebbc13588b1a7b`.
Accepted results are the exact native member/tail obligations, retained
zero-word check/residual factorization and correlated source projection,
including operation result consumption. Observation-only justification does
not supply the declared-Support clause; this is neither a compiler
counterexample nor impossibility of a richer valuation. The original
whole-descriptor-to-native member/tail/Result implication remains OPEN.

Subsequent consumed correction `cfded839e` and the independently reviewed
[annotation type-flow correspondence](2026-10-16-native-annotation-flow-correspondence.md)
supply the local declared-Support formation premise from already approved
target exposure. The event-only method's failure below does not require a new
envelope decision. Full dependent source/native adequacy remains OPEN.

## 1. Statement fixed before the derivation

The original program is

```yu
my receive (f: () -> 'a) = { my g = f(); g() }
```

Keep the original scopes, formal, first Apply, return binder and pending Bind.
For every original xi=(nu,K,D) and every original complete first-Call returning
witness z, preserve the same actual returned value/provider W_z and matching
callee-result packet F_R,z, jointly as

```text
M_W* W_z union_tagged M_res* F_R,z.
```

Private captures, immutable environment, original predicate identities,
receiver/receipt coordinates and admitted future challenges remain those of
that same witness. No new provider, marginal packet, xi or seed may be chosen
for a child port. Unknown source constraints remain predicates; arbitrary xi
need not satisfy them unconditionally. The required conclusion is that the
corresponding complete original source obligations imply the actual incident
native Result predicate jointly with the same Function parent's argument/entry,
ResultEffect and reached post-check context predicates, under that one xi.

This packet attempts a direct predicate interpretation at the actual consumers.
It does not assume native G is satisfied, define Function as an unrelated
four-field product, restrict the quantifiers to the captured/direct fixtures,
or compose successful concrete comparisons transitively. Nor does it assert
all-native-model completeness, runtime receipt execution or default cutover.

## 2. Accepted inputs and unchanged operational owners

The top-level inference principles require direct generation/accumulation and
reuse of established hygiene. The CLEAN
[outer-use construction](2026-10-16-native-outer-use-source-witness-transport.md)
§6 identifies the precise remaining correlated predicate, after its joint
packet reindexing. The reviewed
[result source interpretation](2026-10-15-native-call-result-source-interpretation.md),
[source constraint valuation](2026-10-16-native-source-constraint-valuation.md),
and [received-root interpretation](2026-10-16-native-received-root-interpretation.md)
supply source origin, native field equations and the original local receiving
semantics. None is used as a complete native constraint valuation.

Reinspection of the frozen owners finds the same four actual Function children
at `lib.rs:12624–12665`: reversed Argument and ArgumentEffect, preserved
ResultEffect and Result, using the actual parent fields. The old native proofs
apply to these exact clauses, not to all files merely because their historical
baseline is familiar. The G3 delta adds authentic SourceRootId ownership and
expression scheduling; the Result field selection, FunctionPort context action,
Support expansion, nominal member checks and discharge clauses inspected below
remain the clauses used by the earlier native proofs.

`candidate_function_port_admit:3001–3064` retains the processing parent, actual
child pair, FunctionField and Swap/Preserve operation. Result and ResultEffect
inherit that parent's post_check_context; Argument/AE use Swap. A child-local
source prefix is placed before that inherited operation. Original source
evidence is retained. Existing scoped demand handling is checked separately;
it is not silently assumed enabled for this unscoped universal claim.

## 3. Direct same-witness source projection, including both producer cases

Apply contextual Function membership §2 to the original actual value and its
original independently admitted complete challenge. The constructor supplies
actual-U acceptance of that same whole carrier and the complete observation
contract for that same provider, including pending and compatible future
developments. The positive formal Function at native slot43 is an annotation
view. It is not an executable provider; Act(v,U,r) comes from this original
source membership/witness. A positive native term cannot choose a convenient U.

The actual source Apply fixes its argument, current configuration and original
result binder. There are two needed producer cases, without changing z:

- A closure executes its original entry, typed rebind, body and return. Value
  entry forces the original whole carrier once; a retained-computation entry
  binds that same carrier. Body/result views belong to that one invocation.
- An operation's native body can return MakeRequestThunk. Its declared result
  consumer, inside ExecuteCallable, performs the designated request/response
  computation. The source first-Call return z is after that consumer, not the
  raw native return. Request-bind preserves the same response binder, current
  resumed state and suffix through this consumer before returning a callable.

These are the actual source rules in typed-core §§3,6,9 and the selected
Call/source-interface constructors; Lambda/body projection alone would omit
the second case. No original provider alternative is excluded for lacking a
literal Lambda body.

For Return, typed-boundary §6 now constructs exactly the tagged two-input
packet above. For a Request prefix, the same rule is suspended under the
original response binder and pending suffix; resumption retains that binder
and takes the current state. Binding installs the same returned value at g,
and Name/future invocation uses its hereditary certificate. The receiving
and hygiene results preserve original profiles, K/D incidences and activity
conditions. They do not create a grant from an equal family or row.

Thus the source judgment determines a correlated tuple

```text
(original provider, whole carrier, entry observation,
 complete invocation observation, W_z, F_R,z, pending/future obligations).
```

This is a constructive source projection at the actual parent/first-Apply
origin, not a valuation of the native predicates on that tuple. In particular
it does not identify the full source descriptor with the set of requests
actually emitted by this single returning invocation.

## 4. Actual native predicate obligations, derived from the consumer

One can construct the following finite symbolic obligation evaluator directly
from the native consumer, while leaving row variables and source K/D unknown.
It is a characterization of the native checks, not a proposed compiler layer.
An obligation is a formula; it need not already evaluate to true.

For view v write Members(v) for its actual ordered allowed list, Tail(v) for
its retained tail predicate, and family(x) for the retained resolved
SourceEffectId of an atom. Preserve atom origin as an index; Contribution and
AnnotationMember are distinct introductions even when their family is equal.
The clauses forced by `candidate_check_effect_operand:971–1041` are:

```text
N(Bottom, upper) = true
N(Support(v), upper) =
    (and over EVERY j in Members(v) of N(AnnotationMember(v,j),upper))
    and N(Tail(v),upper)                    if a tail is present
N(atom, Allowance(w)) =
    family(atom) in Members(w) OR N(atom,Tail(w))
N(atom, EmptyNegative) = false.
```

The Allowance list is read through its validated closed weight when present.
With no tail, the second Allowance disjunct is false; an absent Support tail
adds no conjunct.
The `OR` branch describes the code's unmatched-atom tail forwarding, not an
independently chosen source witness. Unknown row/row bounds remain symbolic
obligations and accumulate; generation does not solve them. This evaluator
does not erase K,D from the packet interpretation; rather it displays exactly
which nominal predicates must additionally follow from that interpretation.

### Exact executable-context factorization

For each successful zero-word extraction at relation rho, the actual context
walker returns distinct validated weights F and an exact retained residual k.
PrefixLeft walks its input; Replay visits both children; Swap/WithoutLeftFilter
are retained directed residuals. Owner, position, closed-weight identity and
empty executable words are checked (`candidate_context.rs:3070–3153`). The
walker does not supply a live source interpretation for an arbitrary context.

For an Effect lower l, the discharged part is exactly

```text
Checks(rho,l) = and over w in F of N(l,Allowance(boundary(w))).
```

`candidate_context_execute_relation:3226–3301` admits those actual checks or
replays their already registered exact bounds with this occurrence's origin.
It records discharge only after those operations, stores nonidentity k, and
returns consumed only when an extracted boundary matches the original exact
Allowance endpoint. The checked-bound guard at `:3307–3338` gives the exact
allowance child Identity context while retaining its Derived parent. Hence
the syntactic obligation decomposition is

```text
checks retained at their exact allowance bounds
  AND original task under residual k.
```

`post_check_context:2799–2805` returns that residual after discharge and the
original context otherwise. This is an exact predicate-factorization property
of the executed native check construction. It is not the claim that either
conjunct is entailed by the original source witness. In particular a mismatch
may already be retained; marking the check discharged does not mean true.
Value/Function parents do not consume these Effect filters, as established by
the reviewed Replay/Value nondischarge result. Result inherits its parent's
remaining context, not a fabricated successful residual.

The Result Value obligation remains the actual field3 pair under that retained
parent/context and actual use Transport. Its evaluator must use the same
provider/tuple as §3 and the same xi used for Checks. Replacing its predicate
by the entire source premise would make every arbitrary child adequate; it
is not done here. Removing the actual Result edge or changing field3 breaks
this source/native clause association, even though the unrelated source
Apply judgment still exists.

## 5. Decisive failure of the observation-only extension

The attempted valuation was to assign AE/RE and residual effect predicates by
projecting the original witness's actual entry/body/request observations,
while assigning Result its same-z two-input packet. This keeps correlation;
nevertheless it is insufficient at one explicit actual constructor.

At Support(v), the evaluator in §4 demands every declared AnnotationMember,
not only members for which this z contains an event. Native Support expansion
does not inspect z, check a runtime request or wait for one. Contribution and
AnnotationMember use the same nominal contains/tail branch but have different
source justification requirements. This coverage fact follows directly from
the loop at `candidate_effect.rs:979–993`.

A source-qualified discriminator for this proof method is an independently
typed immutable factory whose body purely returns a callable W, viewed through
a covariant concrete allowance containing e. The selected covariant policy
allows e; it does not require this factory to emit e. Its complete actual
Unit invocation can return W with no e event, retaining the same provider and
packets. The actual/native annotation constructor can still contain the
declared member e. An observation-only projection assigns no event to that
member although Support expands it. Adding an empty target allowance exposes
the difference between the vacuous event check and the nonvacuous native
member check. This is a discriminator of the proposed projection, NOT a
compiler counterexample: the original whole-descriptor inclusion into that
empty target might itself be false. No source admission for that entire
comparison is asserted.

The same issue occurs with operation-valued f returning a callable: projecting
only the raw native return would additionally omit the designated consumer's
request and suspended suffix. §3 repairs that producer omission, but it does
not turn every allowed declaration member into an actual observation of z.

Consequently the exact additional source implication to establish is:

```text
original whole same-provider descriptor/inclusion obligation at rho under xi
  => each declared member/tail check generated by Support and each extracted
     allowance check under that SAME xi,
     jointly with the actual Result field3 packet predicate for z.
```

It must use the independently fixed original descriptor and complete challenge
domain, not just the actual trace of z; its fixed actual provider W_z must not
be replaced by a provider that happens to exercise a missing member. If a
separate universal descriptor argument uses auxiliary admitted challenges,
their original admission and correlation must be proved rather than inferred
from a family name or from the allowance list alone.

## 6. Exact remaining source rule and why reuse does not discharge it

The first new failure in this attempted direct evaluator is the pullback of
`Support(view) -> Allowance(target)` at a Function child's actual inherited
context. Its smallest concrete owner is the full-member loop above, reached
from the same-parent FunctionPort RE/AE or an extracted filter. The associated
source owner is the original endpoint-dependent complete Function/annotation
comparison, with its whole descriptor and original K/D action. On the Result
side the matching owner remains candidate_function_port_admit(Result), whose
typed two-input maps must be evaluated in that very same comparison.

The existing source rules supply actual-U acceptance and complete observation
safety, complete source-interface placement, preserved same-z packets and the
local annotation allowance/permission policies. Typed-core §6 explicitly
leaves symbolic endpoint/complete-invocation constraints as obligations; §9
does not define J_call as a union of outward rows. The contextual Function
membership definition retains independent complete descriptor admission and
observation relations. The reviewed transport theorem reindexes already valid
predicates and retains K identities; it does not identify these particular
native member and Result predicates with those independent source relations.

In particular, neither complete source membership for one provider nor every
actual observation of this z alone proves the whole-member implication in §5.
Conversely, a proof of the original whole endpoint-dependent inclusion might
prove it; this pass has not derived that embedding. The code's nominal test
cannot be adopted as the missing source law, and the inert detached evaluator
is not a source semantic consumer. No data-loss, metadata insufficiency,
architecture choice or actual compiler misbehavior follows from this gap.

This remains category (a), an already selected source predicate whose native
interpretation has not been constructed. It is not repaired by assuming all
native G, independent port subtyping, or a new interpretation defined to equal
the desired source premise. The attempted actual evaluator has precise checks;
the original source entailment of those checks remains unproved.

## 7. Economy audit, handoff and original residual

The source projection and discharge factorization are bounded local results.
The observation-only extension is refuted as a proof method by the authentic
declared-member/actual-event distinction. The original FIRST-RESULT-ADEQUACY
theorem is neither proved nor refuted here. No well-typed source-qualified
counterexample to its complete original claim has been established.

Prior passes already tried source-origin reconstruction, scalar valuations and
joint coordinate transport. This pass changed method to the actual consumer
predicate and attempted same-witness source projection. The original semantic
premise survives, now with a precise declared-support coverage requirement.
Do not schedule another decoder, census, marginal scalar model or transport-
only lemma as if it could discharge that premise. No additional compiler
metadata or source restriction is justified by this result.

Next owner action: establish or refute the original whole-descriptor-to-native
atom/tail implication at the positive annotation/signature constructor and
its reached Support consumer, using the actual independent source descriptor
admission/observation relation and the endpoint-dependent comparison. Keep
Result, RE, entry and pending Bind in the same query. If a source comparison
can pass while one of those actual member checks fails, exhibit its complete
source derivation/provider/challenge/xi; if it cannot, derive the member and
Result clauses from that whole source comparison. This is a semantic proof
action, not permission for a new mechanism, tests or default cutover.

The original all-xi/z parent, full B, hygiene, soundness and principality stay
OPEN with the primary. Fresh independent review is required for these local
claims and this exact residual; this producer does not certify its own note.

## 8. Frozen dependencies and commit packet

| Actual source/dependency | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `199963ac9cd13eebca44c4881b859eeb1f801259cc944bf1d5a57df78dc0c070` |
| `crates/yu-solver/src/candidate_context.rs` | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| `crates/yu-solver/src/candidate_effect.rs` | `a330100b418f14be1c8f600c62970efdb4859818b603190846796de39fa8cef2` |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `crates/yu-solver/src/candidate_call.rs` | `cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1` |
| `crates/yu-solver/src/candidate_scheme.rs` | `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e` |
| `crates/yu-solver/src/shadow_apply.rs` | `357b274d0de509931bda3015a99b1a1cf2ac86d75a45d230d62ab456c56740ba` |
| Native Call result source interpretation | `593d424e5db01f58f171983e6d8a4551381e54455b19dbb6469e13993e860390` |
| Outer-use source-witness transport | `90a02bdf7a6a2e241bce968e77df12b67f29419cf9c7b6c78f8965636f36ba23` |
| Source-constraint valuation | `161cdecc91fe04714f8ae7f8f0f71cf06d52400114abbaa3255df41da616cdff` |
| Received-root interpretation | `5ccc9cce1ec6f8626276f1b9d214524b1bf30ab1a8ac9430b805a57df96d7b71` |
| Contextual Function membership definition | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| Call source-interface definition | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| Top-level principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

Authority read: top-level principles; contextual Function membership §2–4;
Call source-interface constructors §2–4; typed core §§6,9; typed-boundary §6;
concrete-compatibility §1; approved Function-effect-row answer; annotation
hygiene integration §§1–4, with the existing source hygiene/receiving results.
No unapproved draft claim outside its selected subsection is adopted.

One bounded static pass, 25-minute allocation. Commands: bounded rg/sed/cat and
hash reads. No tests, builds, executable probes, Git operations, delegation,
compiler changes or shared-record writes. Only this leased note was written.
Zero measured samples/heavy processes; exact elapsed/CPU/RAM uninstrumented.
Normal Sol/high requested; observed model/effort metadata unavailable.

Commit packet: sole path
`notes/theory/2026-10-16-native-source-predicate-adequacy.md`; baseline
`1e62dfdc3` plus actual source hashes above; independent review pending.
Proposed checkpoint:
`research: isolate declared-support obligation in native Result predicate adequacy`.
Shared-record delta for primary/curator: retain the original parent OPEN; record
the actual predicate factorization and declared-support coverage failure of an
observation-only interpretation, not a compiler counterexample or completed
semantic bridge. No shared record was edited.
