# Neutral Result rows: atomic source interpretation and same-return transfer

Status: independently reviewed constructive mathematical interpretation and
bounded actual row-fragment proof. FIRST-RESULT, complete forward/reverse
Call adequacy, principality, copy/intrusion and implementation parents remain
OPEN. No production or source-semantic change is proposed.
Baseline: `2e25a510dac2cc70c85b067de8dd1485edf0ed84`; native production is the
primary's frozen `35e87f844` inventory apart from reported cfg(test) changes.
Exclusive lease: this note only; bounded normal Sol/high leaf.

Independent mathematical review: compiler-referee `ordinary_carrier_semantic`
returned CLEAN at producer SHA-256
`13400553f6c52c82bd9159482f90f01df1afa470641721aa037ffaa8a94dd4fb`.
Independent scope/conformance review: spec-auditor `ordinary_carrier_contract`
returned CLEAN at the same frozen version. The primary accepts the atomic
interpretation, row-rule preservation and same-z transfer under their explicit
MODEL, CanonicalEq, typed-correspondence and source Return premises. Neither
native solving nor row equality establishes those premises automatically.
Complete RE, copied-context applicability and both full parents remain OPEN.

## 1. Original statement, fixed coordinates and scope

Keep the original source:

```yu
my receive (f: () -> 'a) = { my g = f(); g() }
```

For every original joint assignment xi=(nu,K,D), fix its original f member,
provider, annotation scope S, shared alpha, first Apply u1 and original result
positions A1/E1, local binder g and pending Bind. Quantify over every original
complete returning first-Call witness z for an independently admitted source
challenge at this provider. W_z and F_R,z are projections of that **same** z;
entry, current state, dependent arguments, receipts, future histories and
lineage are not selected independently. Request prefixes retain the original
response binder and Bind suffix; no fresh return is postulated for them.

The local native input is the actual Result child `a+ <: r−` of the canonical
slot43/slot0 comparison, where the constructor decoder selects original alpha
at a and original A1 at r. This packet interprets the plain Value-row fragment:
identity context and default scoped action, no child-local weight, no copied
endpoint requiring an unproved reindexing. Other constraints remain incident
conjuncts under the same valuation; they are not declared satisfied. The
already reviewed route evidence supplies this neutral case when reached.
This is a local subtheorem; the original source domain is not restricted to
identity contexts, direct providers, closed alpha or terminating challenges.

Required local conclusion: in the atomic interpretation defined below, the
actual row predicate is precisely existing full same-value VIncl(alpha,A1).
Native row storage/replay/canonical renaming respects that predicate. Combined
with the independent original source Call/Return certificate, it transfers the
same complete returned value/provider/dependent tuple to A1, with exactly the
existing two-input result view

```text
J_z = (M_W)* W_z union_tagged (M_res)* F_R,z.
```

It does not establish E1's complete computation check from nominal RE inclusion.
It neither constructs the source challenge nor proves the entire native graph
has a model. Those distinctions are part of the statement, not hidden lemmas.

## 2. Existing carrier and source selectors

Typed-core §7 defines VIncl(A,B) as inclusion of the **same decorated values**.
Its decorations include original source profiles, typed-path correspondences,
joint K,D and lineage. Typed-boundary §6 defines a typed view and the transported
packet `(v,t,chi,K,D,L)`; equal underlying values may have different views.
Typed-core §9 retains complete dependent challenges, the actual provider,
entry/body/designated consumer and their complete result guarantees. These
supply the carrier here; four independent Function fields do not define it.

For fixed xi write Omega_xi for that existing carrier of complete decorated
source values/observations, retaining their actual source view indices and
complete dependent certificates. Source occurrence/interface indices are
retained as indices of observations, not erased to a runtime pointer or effect
family. Membership is the existing source Value-interface judgment. Its
Function case uses that original source complete-interface meaning, including
all admitted challenges and guarantees; no new Function semantics is supplied.

For an original value endpoint A at its original typed occurrence kappa, write

```text
Sel_(kappa,A)^xi(w) := w satisfies the existing source Value(A)
                      judgment at kappa under xi.
S_(kappa,A)^xi      := { w in Omega_xi | Sel_(kappa,A)^xi(w) }.
```

`Sel` is notation for the existing source membership judgment. It is not a
new solver predicate/registry, an effect-family selector, or the proposition
that the desired two packets happen to pass. It may inspect the full original
complete certificate and K,D. The typed correspondence of the original
representation-preserving checking edge specifies how that same decorated
object is viewed at its two positions. It neither executes a conversion nor
allocates a boundary. If such a correspondence is not independently available
for an edge, that edge is outside this plain identity interpretation.

Consequently existing VIncl on this edge expands to

```text
forall w in Omega_xi:
    Sel_(kappa_alpha,alpha)^xi(w) implies Sel_(kappa_A1,A1)^xi(w).
```

Both selectors are fixed by original xi and source coordinates **before z is
chosen**. In particular S_A1 is not chosen equal to S_alpha, to the successful
returns, or to a union of W_z/F_R,z. It remains the original target predicate,
including when it rejects some w or the generated constraints have no model.
This explicitly removes the freedom used by the earlier scalar extension.
The relation is same-object inclusion; it existentially chooses no replacement
provider, profile, challenge or dependent witness on the right.

## 3. Atomic native interpretation and the explicit MODEL invariant

Term storage (`term.rs`, Term/LiveVariableView and term views) supplies arena
identity, component kind, polarity, row ordinal and structural child handles.
It supplies no completed source denotation. The following is a mathematical
interpretation of the actual Value-row fragment, rather than an assertion that
those storage fields already implement a semantics.

Let sigma assign **one** subset of Omega_xi to every native value-row class.
Every incident occurrence uses this same assignment. Original source anchors
impose sigma(a)=S_alpha and sigma(r)=S_A1 at their original indexed checking
edge; other genuinely fresh rows may be variables over subsets. Both polar
occurrences of a row read its one sigma. Native polarity controls the direction
of inclusion and never allows independent lower/upper source witnesses.

Define the meaning of a plain row task and of physical bounds by:

```text
[[ Value(row x)+ <: Value(row y)− ]]_(xi,sigma) := sigma(x) subset sigma(y)
[[ owner y, Positive, bound x ]] := sigma(x) subset sigma(y)
[[ owner x, Negative, bound y ]] := sigma(x) subset sigma(y).
```

Thus `[[a+ <: r−]]` is exactly the displayed existing VIncl(alpha,A1), by
expanding the fixed selectors. The definition applies uniformly to all row
pairs, before source Return or a particular z appears. It is not defined as
“both result packets succeed” or as satisfaction of an opaque entire G.

Here is the required, explicit fragment MODEL invariant for a retained state H:

1. Original source anchors read their fixed selectors under the same xi.
2. Each retained original/submitted plain row inequality holds under sigma;
   every physical bound denotes that same oriented inequality.
3. For every canonical equality used to identify rows x,y, sigma(x)=sigma(y).
   Canonical representatives therefore read the same set as their originals.
4. Provenance, source occurrence/view indices and K/D references remain attached
   to the original edge; representative equality does not identify typed views.
5. Only the stated neutral context/default scope fragment is interpreted here.
   General contexts need their own source operation, not this inclusion clause.

MODEL is a concrete conjunction, not assumed automatic after a drain, memo
completion or lack of diagnostics. In particular it need not be inhabited for
a fixed original xi. Submitting a genuinely new source checking constraint
restricts its models; propagation derives consequences of already retained
constraints. One must not confuse these operations.

## 4. Actual field-3 selector correspondence

The independently reviewed source-origin interpretation supplies the finite
decoder, not the value-inclusion truth. Actual constructors justify its anchors:

- `candidate_effect.rs:1037–1056` keys the original annotation variable by its
  AnnotationScope/name. Paired formal construction at :1118–1164 puts its
  original value pair in Function field3, independently of field2 RE.
  Formal annotation admits the positive target through slot43 and its paired
  negative target through slot44 (:1191–1231). It does not select a provider.
- `candidate_source.rs:1011–1051` retains the original first Apply's children,
  source registration, checking occurrence and result component. The demand
  constructed at `shadow_apply.rs:1553–1599` has that exact result component
  in field3. Its corresponding source coordinate is original A1, not alpha.
- `lib.rs:12628–12660` reads lower.3 and upper.3 and emits Result with preserved
  direction. It does not read field2 or invent a result type after observing z.
- `candidate_function_port_admit` (`candidate_context.rs:3020 onward`) gives
  Result Preserve, not Swap; with local/inherited identity its context remains
  identity. Result's scoped transformer is zero and the demand is consumed.
  The inspected code agrees with the previously reviewed actual Replay route.

Therefore the selected plain child is the source **value** checking edge from
original alpha to original A1, interpreted by §3. This is selector/coordinate
correspondence, not a theorem that arbitrary successful Function decomposition
proves complete Call inclusion. In particular no denotation for a general
native Function was introduced to make that implication tautological.

## 5. Direct insertion, retention, propagation and canonicalization

### Submitted bound means the submitted inequality

`candidate_apply_value` (`candidate_extrusion.rs:845–880`) canonicalizes the
actual pair. Equal representatives return reflexively. For distinct rows it
chooses Negative on the lower owner when the upper's level is no greater;
otherwise it stores Positive on the upper owner. Both physical encodings in
§3 denote **the same** sigma(lower) subset sigma(upper). This row-to-row branch
does not manufacture a structural Function copy or perform a source operation.

`candidate_insert_bound_with_evidence` (:442–545) validates/canonicalizes both
endpoints, retains the BoundKey and its admission cause, appends the row to
actual direct_lower_rows/direct_upper_rows, then emits its physical slot and
capture/evidence record. The physical storage and evidence record encode the
same endpoints/polarity. Duplicate retention is logical idempotence; it does
not create another source witness. Resource/availability failure does not
constitute successful logical discharge.

For a submitted new inequality p, the precise semantic update is
`Models(H+p)=Models(H) intersect [[p]]`, with all original selectors fixed.
This is not a proof that p already followed from H. In particular actual
field3 generation creates a real constraint, whose source truth must hold in
a satisfying interpretation; execution of insertion does not prove it true.

### Replay soundness

`candidate_opposite_count/opposite_bound` (:612–667) reads the actual opposite
side of that canonical owner. `candidate_replay_bound` (:799–842) orders the
inserted and opposite input lower-first and upper-second regardless of which
polarity was just inserted. In the plain row case the two retained premises are

```text
sigma(l) subset sigma(o)    and    sigma(o) subset sigma(u).
```

The emitted task is l <: u. For each same complete decorated object w,
membership propagates first to o and then to u, so it holds in every MODEL of
both premises. This proves actual replay-step soundness by inclusion
transitivity. It uses one sigma/xi, not independently chosen intermediate
providers or marginal packets. Retained Replay parents/BoundKeys authenticate
the two premises; identity/default replay supplies no additional transformation.

Hence every finite sequence of these actual insertion encodings and replay
steps preserves exactly the submitted model conjunction, adding only implied
replay constraints. This does not assert that every pair will be replayed,
that a suspended replay completed, or that row-only chains are eagerly
materialized as every transitive edge. Those completeness/activation claims
are unnecessary for this soundness result and remain separate.

### Canonical equality is an obligation, not inferred source equality

`lib.rs:11562–11568` reads the intrusion representative for a row.
`candidate_intrusion.rs:518–605` merges copy/parent representatives, transfers
both bound sides and their origins, sets the representative and canonicalizes
bounds. For the present fragment, under the explicit CanonicalEq conjunct
sigma(copy)=sigma(parent), replacing either endpoint by its representative
preserves every inclusion. Copying both bound sides onto the representative
also preserves their conjunction. Repeated identical bounds remain idempotent.
The corresponding retained view/source indices are not renamed to one view.

If CanonicalEq has not been justified at its actual source-qualified intrusion
owner, this theorem supplies **no** reason to identify the selectors. With
fixed original alpha/A1 selectors that disagree, an equality constraint can
make the fragment unsatisfiable; neither selector may be rewritten to rescue
it. The proof establishes canonical quotient soundness conditional on its
explicit equality constraints, not all-source intrusion, extrusion or FreshUse
adequacy. Fresh maps likewise require their original joint reindexing premise;
this identity-row proof cannot silently supply it.

## 6. Source Return certificate and transfer of the same z

Take the independently valid original member f of its original complete source
interface and an independently admitted original challenge at u1. No Unit
admission is derived from a written `()` or from native scalar success here.
Apply the existing complete source Call law to the same provider/challenge and
its actual returning z. Its original result guarantee supplies membership of
the complete returned decorated value at alpha under this xi. Entry, body and
the designated result consumer are all included; a native operation's raw
carrier return is not substituted for this complete return.

Typed-boundary §6's existing result theorem and the reviewed source Result
classification construct from this z exactly

```text
J_z = (M_W)*W_z union_tagged (M_res)*F_R,z,
M_res(Result.q,q) only at matching existing typed paths.
```

This theorem supplies the maps and the two original tagged inputs. The present
atomic interpretation creates neither. It retains actual returned-value
evidence even when the callee-result contribution is empty; conversely it
retains a matching declared result contribution without copying a call-effect
annotation onto a latent path. Both remain in the same source record w_z in
Omega_xi, with their original predicate ledger K, dependent D and lineage.
Thus the independent source result certificate gives Sel_alpha(w_z).

Now let sigma satisfy the explicit plain-row MODEL including the actual
Result inequality, with its original anchors. Then

```text
Sel_alpha(w_z)
-> w_z in sigma(a)
-> w_z in sigma(r)
-> Sel_A1(w_z).
```

No existential witness is introduced in this chain. The underlying value,
provider, dependent arguments, source receipts/scopes, actual W_z and matching
F_R,z are unchanged. Evidence-preserving value checking retains J_z through
the original typed correspondences; it does not execute a cast or allocate a
new profile. This is the full same-decorated-value transfer to A1, not nominal
support inclusion or scalar type compatibility. In particular it covers both
existing tagged image inputs jointly because the carrier member is the one
complete decorated returned value, not separately selected packet marginals.

Ordinary Bind then binds this actual returned value/view to the original g;
Name g reads that binder by identity. Native Install/Local routes retain the
actual initializer endpoint and original local slot (`candidate_source.rs`
Install/Local actions; `candidate_scheme.rs:1475 onward`), and incoming local
freshening still needs its separate original map theorem. Neither source Bind
nor Name creates a replacement value, receiver or outer-formal seed.
For a Request prefix the original response binder and pending Bind are kept;
the argument applies to each actual later complete return z, without pretending
that a pending request already supplied a returned value certificate.

This transfer is uniform over the original xi and z. It is a genuine application
of the independently admitted source Call/Return theorem and the new atomic
row interpretation. It is not a derivation of source Call or MODEL satisfaction
from the mere presence/completion of the native relation.

## 7. What is closed locally and what remains

Submitted local results: an explicit source-indexed atomic row interpretation;
actual field3/source-selector correspondence; direct-bound representation,
finite replay-step and equality-respecting canonicalization soundness; and
same-z full value/result-view transfer using the existing source Return inputs.
These remove the scalar-only interpretation gap for this neutral row fragment.
They require no new source constructor, Function product definition, registry,
endpoint equality strengthening or source restriction.

Remaining exact premises for the original parent include independently admitted
input/challenge construction, source-compatible joint satisfaction of all
incident generated constraints, complete effect/context checking and actual
copy/FreshUse/intrusion reindexing where reached. This packet constructs no
model of arbitrary native G and proves no global model extension/principality.
Original alpha/A1 remain fixed throughout even when that makes a conjunction
unsatisfiable. General contexts are not silently interpreted as identity.

In particular native `e_R+ <: i−` still has its separately established nominal
Support/Allowance projection. The present value inclusion does not turn that
projection into CIncl(Comp(E_R,alpha),Comp(E1,A1)) or establish the original full
two-input **computation** check. Complete forward and reverse FIRST-RESULT,
full B, negative coverage, lifecycle and principality remain OPEN.

Next owning action: combine the independently reviewed inlet construction with
this fixed-selector value fragment and prove the actual RE/context predicate's
source interpretation at the same xi/z. Its nominal family predicate cannot
replace complete source computation membership. No production change is
justified by this mathematical packet alone; fresh independent review is required.

## 8. Freeze and commit packet

```text
term.rs f3a0c3875ba1ba8c80ee48a405faf3dad22b57cba8930394f99181201bc58f60
lib.rs 199963ac9cd13eebca44c4881b859eeb1f801259cc944bf1d5a57df78dc0c070
candidate_source.rs efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38
candidate_effect.rs 44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9
candidate_context.rs 72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6
candidate_extrusion.rs 2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b
candidate_intrusion.rs 2158e7377686189ed90d8b8d8803dbb446368abb52b7e0cb24b2282ebe41007c
candidate_scheme.rs 2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e
shadow_apply.rs 357b274d0de509931bda3015a99b1a1cf2ac86d75a45d230d62ab456c56740ba
typed-boundary §6 1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb
typed-core §§6–9 0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e
first-result-source-judgment-preservation.md 168075a1c6e5b77df844a258165cec1b1f383cc7f84f11843deb6c3e28853946
native-call-result-source-interpretation.md 593d424e5db01f58f171983e6d8a4551381e54455b19dbb6469e13993e860390
```

Native paths are under crates/yu-solver/src; design/theory paths are the named
notes. The Unit-inlet producer's pending conclusion and unstable metadata
were not consumed as proof inputs. Its eventual reviewed conclusion may
discharge the independent source challenge premise;
this packet does not claim that already happened.

Checks: bounded static authority/actual-source reads, direct hashes and artifact
whitespace. No tests/builds/probes, source/Git/shared-record edits, delegation or
measurements. Requested normal Sol/high; observed runtime model/effort unknown.
Review pending; no producer certification.

Commit packet: sole new lease
`notes/theory/2026-10-16-neutral-result-row-source-interpretation.md`; baseline
2e25a510dac2cc70c85b067de8dd1485edf0ed84, dependencies above. Suggested checkpoint:
`research: interpret neutral Result rows over complete source values`.
Primary shared-record delta: consume the atomic row/source-selector and same-z
value transfer results after review; retain RE/context, model extension,
copy/intrusion, complete forward/reverse and original FIRST-RESULT parents OPEN.
