# Returned callable: a concrete received-root incidence discriminator

Date: 2026-10-16
Status: independently reviewed constructive finite source instance; native parent OPEN.
Native baseline supplied by primary: `419c801bd`, native owners unchanged from
`0a9af0da5080469f930da0032aa96d7d89d358c5`.
Exclusive lease: this file only. No native acceptance or execution claim.

## Integration review and separate executable evidence

Independent compiler-referee `ordinary_carrier_semantic` and specification
reviewer `ordinary_carrier_contract` reviewed the producer artifact at
`2fa15ceb0049e83fdce2a8774816cf3a993fcdd23a5586c3edf18139ae03b5fd`.
Both returned CLEAN. The primary accepts the concrete incidence contrast and
same-return transport construction; universal native adequacy and complete
direct negative eligibility remain OPEN.

Separately, at `f8c7a8a13` the primary ran the actual playground candidate on
both source variants with `CARGO_BUILD_JOBS=2 cargo run -q -p yu-playground --
--intrusion SOURCE`. Each process had a 60-second cap and exited 0; Cargo
processes were serialized. The exact temporary inputs were
`/tmp/yulang-native-result-captured.yu` (SHA-256
`79acf8f07fa97b19aa6082d066a78cffc1c0fa3d8072fe0ad6c013066729612a`)
and `/tmp/yulang-native-result-direct.yu` (SHA-256
`b68813827a55b0b332b976eb5adf4e0fa69e70602a1236b1f5438a11d87d66a9`).
They instantiate the source below with layout differences; the selected
factory is their sole behavioral difference. Adjacent `.log` files contain
9220 and 7630 bytes respectively. Both parse/lower/infer successfully; their
outer native graphs differ. No native projection equality, scoped-experiment
acceptance, runtime result or proof follows solely from those successes.
There were two executable source-admission processes, zero timing/RSS samples,
and no solver code change. The producer's historical no-probe statement below
continues to describe its own packet.

## 1. Fixed instance and conclusion

The following is source-constructor notation. Its exact parser acceptance has
not been checked in this packet.

```yu
act signal:
    our ping: () -> int
act write:
    our put: () -> int

my receive (f: () -> 'a) = {
    my g = f();
    g()
}
my outer (thunk: [write] int) = {
    my captured (u: ()) = thunk;
    my direct (u: ()) = signal::ping();
    my factory_captured (u: ()) = captured;
    my factory_direct (u: ()) = direct;
    catch receive factory_captured {
        signal::ping(), _ -> 1,
        v -> v
    }
}
my answer = outer(signal::ping())
```

The counterpart changes the actual source use to `receive factory_direct`.
Both factory declarations and both returned providers remain in the same
immutable source environment. They are two actual provider choices in two
complete challenge/return witnesses, never a provider replacement inside one
witness. All names denote their original resolved declarations. In particular,
the two effect declarations are distinct: `signal != write`.

For each branch separately fix the original joint `xi=(nu,K,D)` and its first
Call return witness `z_s`, where `s` is `captured` or `direct`. Retain both
`W_s` and the matching `F_R,s` from that **same** `z_s` through result, `g`,
Name `g` and the future Unit invocation. The source observation derived below
has the following coordinate at the signal Catch candidate `H`:

```text
captured branch: Inc(q_c,H,b_outer,RootComp) = true
                Grant_from(b_outer,q_c,H) = false

direct branch:   Inc(q_d,H,b_outer,RootComp) = false.
```

The actual events `q_c,q_d` are different events in their respective branches.
This is not equality of event IDs, complete descriptors, scalar projections,
solver results or native acceptance. The contrast is at the same original
RootComp schema and matching source candidate position. Each execution has
its own fresh receiving boundary instance.

The universal FIRST-RESULT-ADEQUACY parent remains OPEN. This concrete
instance supplies a required complete-observation coordinate for that parent;
it is not its restriction to two providers or one challenge.

## 2. Selected constructors and complete challenge qualification

This derivation uses the approved production Function denotation and inlet
context decisions, the function-effect-row answer, and the Authoritative
contextual-Function/source-interface constructors of 2026-10-08. These fix
complete typed observations under the original `xi`, independent checked
challenges and actual-provider preservation. They permit the finite source
instance below without defining a new exhaustive Function denotation.

The independently declared primitive interfaces are:

| Source item | Original interface and operational obligation |
| --- | --- |
| `()` | Value(Unit); pure Return of that same Unit and current world |
| integer `1` | Value(Int); pure Return of that Int |
| `signal::ping` | Original Unit parameter, Int response, resolved family signal; native request carrier followed by its designated consumer |
| `write::put` | Original Unit parameter, Int response, resolved distinct family write; unused by the displayed execution |

Ground Unit and Int require no selected family-argument variance law. The
operation declarations retain their original request/response contracts and
pending continuations. This is the ordinary declaration contract, not a rule
that family identity alone licenses a response, handler or dependency.

Construct the complete interfaces by IF's actual declaration, Name/capture,
Lambda, Return, Delay, Bind, Call and designated-consumer clauses. This gives:

- the outer formal's `Computation(E_t,Int)` interface, with E_t open;
- `captured`'s Value(Unit) entry and Int body result, with the exact captured
  binding `thunk -> V` and its RootComp consumer in its latent body interface;
- `direct`'s Value(Unit) entry and Int body result, with its actual signal
  operation/consumer and no reference to `thunk`;
- each factory's Value(Unit) entry and actual returned closure/provider,
  including that provider's original latent/future interface;
- the actual receive use, its first whole-Call result and dependent second
  Call suffix.

These are complete interfaces, not just the printed `Unit -> Int` skeleton.
For example, the callable frame has the whole-carrier inlet, actual role and
entry, Force/rebind/body sequence, typed request/response and pending/future
coordinates, immutable capture references and current-world/activity fields.
The Return/future coordinate of each factory names its actual returned
provider. `captured` and `direct` are not cast to one another because their
printed result and argument types coincide. The annotation result variable
is instantiated at its original receive-use scope with the corresponding
original returned interface and all its retained dependencies. No equality
between the two complete provider interfaces is needed or claimed.

### The concrete challenges

At each of the first factory call and later returned-callable call, the actual
argument is the ordinary `Delay(Return Unit)` with its original formation
origin. Its capture graph is empty. It is formed inertly, supplies a whole
carrier, and has pure designated execution returning Unit. Thus its carrier
admission follows from the original Unit/Return/Delay clauses, before testing
any Function comparison or desired observation. This discharges admission
for these **particular** challenge members; it does not redefine `D_F`.

The punctured caller context is the displayed original source continuation:
for the first call it is the Bind of the returned value to `g`, then the
second Call, with the enclosing receive/outer/Catch frames; for the future
call it is the current suffix under that same Catch. Other bound values are
exactly the independently formed immutable closures above, with the original
received root `V`. IF-Insert/IF-Use retain their actual declarations and
references. The contextual challenge constructor combines that context,
those registered actual hole values, and the just-derived whole-carrier
admission into `d_1,s` and `d_2,s`. Its clauses contain no desired Inc result,
Q, successful Function comparison or replacement provider.

Both whole invocation contracts retain **all** independently admitted
challenges and observations, not only these two members. The generic
Value-entry clause remains `receipt; Force(D_arg) >>= rebind >>= body`, with
the original whole `D_arg` and every admitted pending/future development.
For these actual arguments, the Force returns Unit before the body starts.
The primitive returned result is Int in either branch. Any pending prefix
or response stays in its original source relation; no unconditional effect
row subtraction or independent port-subtyping rule is used to construct this
challenge. In particular, this packet does not set `D_F` to a singleton or
claim a complete characterization of its other members.

The formal's written `[write] int` is deliberately not a closed upper bound
`E_t subseteq {write}`. The selected negative annotation policy constructs
RootComp protection plus local write permission and admits additional effects.
It therefore does not reject the actual delayed signal computation merely
because signal differs from write. This is the reviewed RootComp construction,
not a new rule for the example.

The two branches may have their corresponding original scoped instantiations
of receive's result variable. Comparisons here never equate those instances
or require choosing a common scalar solution. Within each branch, every
packet map and future challenge retains its own one original `xi,z_s`.

## 3. Actual outer entry and immutable closure environment

The outer call reifies the complete `signal::ping()` computation as inert
carrier `T`. No request is emitted by reification. At genuine outer retained
entry `o`, instantiate the reviewed explicit-ground schema:

```text
Gamma(thunk) = Computation(E_t,Int)
b_outer = fresh(o, original thunk formal, original [write] row, RootComp)
Gamma_b: Protect(RootComp), Admit(RootComp)={write}
V = received view of T
chi(V) = inherited-image(T) union {(RootComp,b_outer)}
Receive(o,thunk,V,Id).
```

The boundary protects the received position, including signal. Its permission
is separately write. The original outer receiver remains live while its
Catch scrutinee is running.

Lambda formation restricts the immutable environment along actual lexical
dependencies. `captured` retains the original binding to `V`; `direct` retains
its signal operation declaration, with no read/capture dependency on `thunk`.
Factories retain references to the corresponding original callable values.
Returning a factory result does not reconstruct its captures or change their
view packets. Even if an implementation stores a larger lexical map, no
source observation edge arises from an unused cell in that map.

This is a concrete immutable environment, not an assumption that a closure's
printed type reconstructs an arbitrary private store. Public callee evidence
is not pasted onto all private bindings; private captured packets are likewise
not indiscriminately pasted onto public profiles. The relevant evidence will
come from the actual later read of `V`.

## 4. First Call, both packet inputs, Bind and Name

At the first call inside receive, `f` is the actual factory selected by this
branch. The whole Unit carrier is forced at its original Value entry; its
body then reads the corresponding immutable closure binding and returns it
inertly. In the captured branch this actual value/provider is `captured`, and
in the direct branch it is `direct`. The first call emits no signal merely
by returning either closure.

Fix its actual complete return `z_s`. By the selected source Result and the
reviewed returned-exposure construction:

```text
P_return,s = M_W,s* W_s union_tagged M_res,s* F_R,s
P_g,s      = Id_* P_return,s
P_Name(g),s= Id_* P_g,s.
```

`M_W,s` is the whole actual returned-value correspondence. `M_res,s` strips
exactly a matching Result prefix and retains only existing typed paths.
Both inputs are indexed projections of `z_s`; they are not independently
chosen marginal packets. `K,nu` and the dependent `D` predicate references
remain those of `z_s`. The pending Bind binds that same returned value in its
actual current world. Neither factory return nor `g` binding reads `thunk`.

These maps retain the returned provider/future interface. They do not paste
the completed factory CallView's observation onto its future invocation.
Any nested profile independently present in either actual input stays carried
with its own source tag; an unrelated first-Call effect position has no
invented Result image. The absence of a *new* seed at `g` does not erase any
input. By the reviewed constructor classification:

```text
NewSeeds_from_return_bind_Name = empty.
```

At the second Call the actual Name `g` selects that same returned provider.
Its own whole Unit carrier is separately reified, received and forced.
Consequently this future Call is tied to `z_s`'s actual output provider, rather
than choosing a provider having the same endpoint type. These are the required
two packet inputs and same-return binding, independently of native replay.

## 5. Captured branch: construct all witnesses of b_outer incidence

After the future Unit force, `captured` executes its original body Name
`thunk`. The source interface of that binding is Computation(E_t,Int), so
source normalization selects its designated RootComp consumption. The actual
immutable read returns the original received view `V` and creates a read
receipt for the currently executing captured invocation. It does not mint a
new receiving boundary or replace the original receiver of b_outer.

Executing this exact RootComp opens `T`, whose whole body is the original
signal operation/consumer. That consumer emits fresh event `q_c` with Unit
payload and its original Int response/pending continuation. There is a new
observation at the actual executing view:

```text
Observe(q_c,V,RootComp,o_read)
chi(V)(RootComp,b_outer)
Receive(o,thunk,V,Id).
```

The first line is derived by executing that root; it is not inferred merely
from storing `V`, equal effect families or a completed factory observation.
The last line is the **outer entry receipt**, distinct from the read receipt
owned by captured. The same-view join is allowed and required by typed-boundary
§6 and the independently reviewed different-receipt construction. An observer
need not have the candidate's owner. Actual Name consumption preserves this
view; no pointer-only substitution between different view packets is used.

These witnesses give `Path(q_c,o,b_outer,RootComp)`. When the search reaches
outer's Catch candidate `H`, `H`, `owner(H)=o` and `b_outer.receiver=o` are all
active. The captured invocation and receive invocation have been unwound on
this outward search; their completed views/observations do not stay active.
The factory already normally returned before `g` was called. None of those
expired receivers is reactivated. Thus the definition gives

```text
Inc(q_c,H,b_outer,RootComp) = true.
```

The original event observation persists while activity is tested at this
candidate configuration. Its owner need not still be active.

`H` covers signal, but this boundary's local contract admits only write.
Therefore `Grant_from(b_outer,q_c,H)=false`. For this explicit single-formal
outer invocation, b_outer is the only annotation boundary introduced with
receiver o: local Lambda declarations and Catch installation create no such
boundary; receiving other values creates receipts, not boundaries; the
incoming carrier predates fresh o and cannot already contain an o-boundary.
Consequently no other boundary local to o can grant signal, so `Grant(q_c,H)`
is false for this constructor instance. Since Inc already makes Protected
true, the selected visibility formula excludes this H. This is a source
eligibility conclusion, not a native handler-selection execution.

## 6. Direct branch: absence of this boundary's observation path

After its own future Unit force, `direct` executes the original signal
operation/consumer. It emits fresh `q_d` without a read or execution of
`thunk`. Its constructor graph has no Name, argument or designated consumer
edge entering `V.RootComp`. Its Unit argument was `Delay(Return Unit)` and
has no dependency on `V`. The returned direct callable has its original
capture graph, not captured's graph or a union of both providers' captures.

Thus no executing view exposing `q_d` is reached from b_outer's one RootComp
position through a matching source typed-flow/Observe chain. The graph may
contain `V` in the surrounding immutable environment and outer still has its
entry receipt, but neither is an Observe edge. Returning through both actual
packet maps does not create one from a private cell that this provider never
uses. The only introductions of b_outer were on the received `V` in §3;
receipt, result, Bind and Name do not invent a new such source route.

By inversion of the finite constructor graph for this event there is no
`Path(q_d,o,b_outer,RootComp)`. Hence

```text
Inc(q_d,H,b_outer,RootComp) = false,
```

even though H, o and b_outer are active. This is actual absence of the required
observation coordinate for this boundary, not an inactive-boundary shortcut.

This negative is boundary-specific. A full `Protected(q_d,H)=false` or actual
selection conclusion also needs the complete live profile inventory of the
direct event, including any independently justified inherited/callback
profiles. This packet does not silently set that inventory empty. Intermediate
factory/receive/future-call receiver instances are expired at H and cannot
supply live incidence, but that alone is not a general completeness proof
for all other source profiles. The proved discriminator is the stated
b_outer incidence contrast.

## 7. What this instance requires of native interpretation

The two complete observations differ at a coordinate required by the selected
production denotation: source typed observation and receiving incidence under
the original `xi`, not outward signal support alone. Both are derived from
original constructors and admitted Unit challenges. No exhaustive descriptor
basis, singleton `D_F`, scalar projection equality or native acceptance was
assumed.

Any adequate native interpretation of the first Call and its returned callable
must retain enough original provider/capture, Result/Bind/Name and future-use
meaning to represent this difference. In the captured witness it must keep
both same-z packet inputs and the original private `V` read; in the direct
witness it must not manufacture that read from the other closure or a public
profile. This is a concrete falsifier for an interpretation that equates the
two observations solely from their Unit/Int endpoints and outward signal
support. It is not evidence that actual retained native artifacts make that
equation. Their scalar equality, native acceptance and full adequacy remain
separate questions.

Next action: inspect the actual native first-Result/local-use/future-call
interpretation against these two source-qualified provider/capture histories.
Require the same-z two-input result image and the b_outer observation coordinate;
if a proposed interpretation yields identical incidence, exhibit its exact
erasure at the owning constructor. Native source admission/parsing can be
verified independently by the primary; it is not a premise smuggled into this
source derivation.

## 8. Checks, dependencies and commit packet

Method: bounded source-rule instantiation, actual Name/receiving correspondence
inspection and dependency hashing. No parser, compiler, VM, tests, builds,
executable probes, Git operations, delegates, network or other writes.
Native runtime/solver code was not changed. Zero heavy processes or measured
samples; approximately 15-minute packet, CPU/RAM uninstrumented. Requested
normal Sol/high; effective runtime model/effort metadata unavailable.

```text
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c  notes/design/2026-10-08-call-source-interface-definition.md
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0  notes/design/2026-10-08-contextual-function-membership-definition.md
d98e1a4e5d93f807d77c88dcf6138924e7a2b0bd2f9af031caa58bd7c79047c0  notes/theory/2026-10-15-root-computation-profile-source-construction.md
ae05faea870634f7cd8cceac9515537d59427c08ae74940c7da70b1f89f45e8b  notes/theory/2026-10-15-runtime-receiving-view-construction.md
6f2bc05137e451c38391655bb2d45e9224f12eebf7d58c7f5a78c8abd69c93f4  notes/theory/2026-10-15-callback-result-exposure-classification.md
7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a  questions/2026-10-05-production-function-denotation/approved-answer.md
032849b8bc8e9398889ed589be9e7598252f53924346de31175538e533bee997  questions/2026-10-05-function-effect-row-denotation/approved-answer.md
9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3  questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md
```

Changed path / sole lease:
`notes/theory/2026-10-16-native-returned-callable-incidence-instance.md`.
Baseline `419c801bd` supplied by primary; native dependency delta none reported,
no direct Git comparison performed. Claim: concrete source incidence instance,
not universal native adequacy. Fresh independent review pending; producer has
no certification authority. Proposed checkpoint message:
`research: construct returned-callable received-root incidence instance`.
Shared-record delta for primary/curator: consume this concrete discriminator,
retain FIRST-RESULT-ADEQUACY/full B/hygiene/soundness/principality OPEN, and keep
boundary-specific direct non-incidence separate from global negative-profile
completeness. No existing proof or shared record was edited.
