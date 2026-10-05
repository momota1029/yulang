# Int literal: the local source-to-view derivation boundary

Date: 2026-10-05
Status: unreviewed conditional derivation; research only
Baseline: `b35803eb6bc8c028510c61aa05d7e95a865ad664`
Scope: one scalar actual at a known source call, and its placement in an Int-valued callback body
Implementation authority: none
Independent review: pending; the producer's source reading is not independent review

## Objective and authority

Determine what a scalar literal supplies before a complete Function interface
and its independent admission judgment have been formed. The result is a
constructive local skeleton under supplied profile/path premises. It does not
derive the missing whole-interface interpretation by assuming that a source
application is already admitted.

[Callback context delivery](../design/2026-10-03-callback-context-delivery.md)
is **Authoritative** within its declared bounded scope: §§2–2.1 require
independent endpoint synthesis and one completed-interface comparison; §4
preserves an existing Pure value's role and entry under a callback slot view.
[Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
is **Draft**, including its §6 application construction. The
[source-generated theorem package](../design/2026-10-04-source-generated-callback-structural-theorems.md)
is a **Reviewed conditional theorem package**; §2.1 explicitly supplies the
decorated owner/view kernel rather than deriving every decoration from syntax.
[Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
is likewise **Reviewed and conditional**, with concrete clauses still Draft:
§2's active constrained-root interpretation and §3's descriptor typing lemmas
are additional hypotheses; §§5–7 do not supply them for arbitrary source views.

The accepted user decisions recorded in [the pinned task](../../tasks/current.md)
select production basis **A**: restrict complete `Rel_C` tuples by independently
interpreted endpoint/role/path/origin/continuation/scope/authority/dependency
constraints, with separate comparison-independent hole-context admission.
Approved production **Option 2** permits conservative root members without a
source-constructor witness. Neither decision selects the remaining concrete
formation clauses. This production basis A is distinct from the permitted
B-equivalent scheduling optimization called A in callback-context §2.1.
Whole-argument reification and result forwarding use the user decisions in
[charter §§17–18, 21, 24](../design/2026-09-29-scc-intrusion-redesign-charter.md);
the charter's general Reviewed header does not turn its other proposals into
Authoritative rules.

## Explicit hypotheses and exact claim

Use proof notation `0`, with the independently known scalar primitive
signature `type(0)=Int`. The same argument applies to any literal covered by
that signature; no integer range, overflow, or lexical elaboration claim is
made here.

Fix these inputs before considering any enclosing Function query:

1. A resolved source occurrence for the literal, its lexical environment,
   original binder scopes and stable source labels. For a call, supply its
   resolved callee or declared callable hole `H`, with a known instantiated
   signature and original static slot/profile `(beta,Slots(beta))`.
2. One jointly well-formed nonempty fiber `xi=(nu,K,D)` and a compatible
   current configuration `C`. Keep every original dependency operand and
   identity. Joint well-formedness alone is not a certificate connecting this
   literal occurrence to this formal.
3. The Draft typed-core construction as the candidate derivation framework,
   and the independently interpreted exact scalar leaf relation: introducing
   `0` is inert; consuming its ordinary value result returns `0` without a
   request or source store/activity change. A conservative scalar primitive
   relation would need its own local certificate instead.
4. **For the conditional call reduction only**, the original typed
   correspondence between the whole argument/result port and the known
   formal, including its profile, receipt/rebind path and any contract
   obligations. Also supply the source owner/view kernel that implements
   activation and receipt. These are premises, not consequences of item 2 or
   of a pending comparison's success.

Under items 1–3 the literal has a uniquely determined local interface/result
tag and finite data/computation skeleton. With item 4 and an independently
supplied actual entry, its argument-entry segment has the reduction below,
preserving the supplied decoration coordinates. This is a **conditional local
derivation**, not a production admission theorem. It yields neither
`Admit_F(F,h;xi)` nor full `DescMem(F,O,w;xi)`.

## Derivation and smallest source-shaped witness

The scalar leaf is the smallest witness. Typed-core §6 gives

```text
I_0 = Value(Int)
d_0 = literal(0)
n_0 = Normalize(Value(Int),d_0) = result(literal(0))
Result(I_0) = Comp(empty,Int).
```

Here `empty` is the pure result computation allowance, not a value bottom,
`never`, an inferred Function inlet, or a statement about the whole callback.
Typed-core §3 gives `V[d_0]=0` and `X[n_0]=Return(0)`.
The exact local source relation is therefore the Return image of that same
scalar leaf at `C`; its observable data type is Int and its local request
contribution is empty. The approved typed observation may erase the numeric
identity while preserving Int and the retained `xi` operands. Such erasure
does not manufacture a receipt, path or capture grant.

Place the leaf in the smallest call skeleton:

```text
call(result(name H), result(literal(0))).
```

Given the known callable declaration and item 4, typed-core §§3, 6 construct
the inert whole argument `t=Delay(Return(0), lexical references)` after callee
evaluation. Its construction executes no argument prefix and freezes no live
handler state. The application result skeleton is
`Computation(E_call,A_call)` with symbolic endpoints constrained by the
complete call relation. It does not solve `E_call` or `A_call`.

For an actual `Value(Int)` entry, the source schedule is

```text
activate the actual receiver; receive t;
Force_argument(t) >>= typed rebind >>= body >>= result consumer/return.
```

The Force of this exact scalar carrier returns `0` in the current
configuration without a request. By the ordinary Return/bind equation, the
entry segment reaches the same typed rebind and subsequent body with `0`.
This is a reduction of a supplied valid typed path, not a proof that the path
is valid. For a retained `Computation(empty,Int)` entry, receipt retains the
same carrier without entry Force; later consumption is a separate body
derivation. Neither case permits recursive forcing by solved runtime shape.

An Int-valued literal callback body has the same leaf:
`lambda(x,result(literal(0)))`. For plain `x`, charter §21 and typed-core §6
generate fresh `A`, entry `Value(A)`, and body result `Comp(empty,Int)`;
ignoring `x` does not remove the entry Force. In a known callback position,
callback-context §§2–2.1 select Handler and the supplied static boundary before
body synthesis. Outside that position an ordinary unannotated literal is
introduced Pure. The parameter endpoint is not assigned Int merely because
the body returns Int. `Fun(P,Result(I_body))` is the source body/result
**skeleton**: typed-core §9 explicitly separates it from complete `J_call`.
Complete Function formation and the final `F_lit <: F_cb` remain obligations.

## Which decorations are derived and which are supplied

| Field or relation | Local result |
| --- | --- |
| Literal interface, result tag and local return | Derive `Value(Int)`, `Comp(empty,Int)`, and the exact scalar Return image from the signature and candidate constructor rule. |
| Literal source occurrence | Retain the given occurrence; finite skeleton construction can name child links. It does not infer a production occurrence-to-endpoint map. |
| Whole argument and order | Construct its inert Delay and source call/entry links; Value versus retained entry follows the actual supplied entry or the selected parameter syntax. |
| Int-valued callback body/result | Derive the scalar body/result skeleton and, for plain `x`, the fresh parameter endpoint and Value entry. |
| Callback role and static boundary selection | Derive Handler selection for an inline unannotated callback literal from the independently supplied expected context. An existing Pure value keeps its actual role/entry. |
| Original slot/profile and instantiation | Supplied by the declaration/use. The literal does not derive them. |
| Actual receiver activation and receipt | The source schedule specifies their creation at execution, using the supplied owner/view kernel and typed correspondence. No dynamic boundary is minted by static literal synthesis. |
| Receipt/rebind typed path and contract satisfaction | Remain premises. An Int result tag and a well-formed `xi` do not connect this occurrence to that formal. |
| `d-`, `d+`, `b+` identities and their `K,D` incidence | Remain the original supplied maps. If supplied, this scalar Force has no request event to project at `d+`; this creates neither an event incidence nor a global empty output bound. |
| Live owner, `Flow`, event-specific `Observe`, operation witness, continuation, capture authority, subtraction attachment | The literal supplies no new such witness. Existing supplied relations remain joint; the call/body can require them independently. |
| Complete `J_call`, descriptor satisfaction, independent hole-context admission | Not derived. The body, result consumer, callee evaluation and ambient view retain their own obligations. |
| Production-only Option 2 alternatives | Uncharacterized here; the local source Return relation does not account for or exclude them. |

This table uses source-generated theorem §§2.1–2.3: primitives cannot
manufacture a handler, receipt, typed path or capture grant. Typed-core §9
derives interaction directions along already corresponding typed paths; a
direction does not supply a missing path or establish a joint inclusion.

## Exact first blocker and stopping point

If only a known signature/profile and well-formed `xi` are supplied, the
derivation stops when relating `Comp(empty,Int)` at the argument occurrence to
the formal's **whole typed carrier interface**. Typed-core §6 states that
relation as an obligation but does not define its endpoint/path translation.
It is therefore invalid to introduce `Comp(empty,Int) <: P` as an established
ordinary query rule, or conclude source admission from its proposed success.
The already reviewed [inlet/admission audit](2026-10-05-production-function-inlet-admission-audit.md)
identifies precisely this Draft boundary.

Supplying the local path permits the entry reduction above. The first
remaining whole-interface formation premise is then a constructor typing
lemma for this call/callback in the active constrained presentation: it must
expose the actual ordinary descriptor membership and independent admission
clauses at the retained incidences, on the same tuple and scopes. Source
contracts §§2.2, 3.5 and 5.1 require that lemma and actual `DescMem` clause
exposure; its source allocation and complete-query arguments in §§6–7 do not
derive it from matching endpoints. This note stops there.

The [effect-descriptor derivation](2026-10-05-function-effect-descriptor-derivation.md)
similarly establishes a conditional Value-entry execution skeleton while
leaving complete descriptor satisfaction open. The present scalar derivation
removes the literal's result-role and exact local execution premises only.
It does not prove a new mixed-row rule, callback containment, Theorem C's
production correspondence, resolver completeness, or common-allowance
principality. Production is not identified with `P_ref`.

## Evidence, resources and proposed shared-record delta

Method: direct source correspondence and constructor reduction. No executable
checker or independent Oracle was used. The proof shares the stated exact
scalar relation and supplied owner/view kernel with the candidate translation;
it is not independent validation of those source rules. The quoted source
decisions govern scheduling; the Draft constructor rules remain conditional.
No seeds, numeric enumeration ranges, mutations, tests or builds apply.
Failure conditions are a wrong scalar signature, a missing or incompatible
path/profile, an invalid joint fiber, a changed entry, unproved adaptation, or
a production formation clause that fails to retain the required incidences.

Reads used pinned `git show` snapshots and narrow section/header extraction,
plus the three assigned rules. No Git mutation, child delegation, production
edit or shared-record write occurred. Commands were lightweight and
sequential, with at most one local process job; no heavyweight compute.
Wall time, peak memory and cumulative CPU were not instrumented. Some broad
combined output was truncated; the governing derivation sections were then
read narrowly. No complete repository search is claimed. The primary owns
dependency revalidation and whitespace checks.

Recommended next action: obtain a narrowly specified, comparison-independent
constructor typing clause for this single scalar call that connects the
original carrier/result occurrence to the formal and exposes its complete
admission/membership leaves. Review that clause before widening the case.

Proposed delta for the primary/curator, intentionally unwritten: record that
the scalar literal/result and conditional entry segment are derivable under
the Draft core, while occurrence-to-formal typed-path translation and complete
Function formation remain open. Keep all current theorem classifications and
implementation gates unchanged; do not promote the note before review.

## Commit packet

- Exact lease: `notes/progress/2026-10-05-int-literal-local-view-derivation.md`.
- Baseline: `b35803eb6bc8c028510c61aa05d7e95a865ad664`.
- Review status: frozen unreviewed conditional research artifact; no independent certification.
- Checks already run: pinned source/status inspection and direct derivation only; no tests/builds/probes. Primary dependency/whitespace checks pending.
- Dependency changes: none made; live dependency changes not audited by this worker. Pinned input Git blob IDs below permit the primary's revalidation.
- Proposed commit message: `research: derive the conditional Int-literal local view skeleton`.
- Shared deltas left for primary/curator: task/theory/index status entry described above; no authority change or gate closure.

| Pinned dependency | Git blob ID |
| --- | --- |
| `tasks/current.md` | `8b3e7363d7f15e3fbe791457e1acc833dd10f538` |
| source contracts | `1c2b1a579a9cc7a51d98a4fda755838decb96d07` |
| callback context delivery | `eeed5c2b5dd38404a4c774cda486864a63992fad` |
| source-generated theorems | `ab212217cd404991cded2b8fd529a1e731a806b3` |
| effect-descriptor derivation | `cec362a02150a505aa900e3ba7048ae9a2ff3e6c` |
| typed computation core | `d0948191bbc2d1eb10a7e6e360dc8852a185db1d` |
| redesign charter | `4a6db32d07ae23a18669a62b5ea25d1d19383c14` |
| inlet/admission audit | `b87fb96ded029deaa6efdc419e323a4c31191bb9` |
