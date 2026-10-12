# Nested recursive f: exact L4 constructor instance audit

Date: 2026-10-12
Status: frozen unreviewed research; bounded static characterization and local obstruction
Parent inference / complete Call / intrusion theorem: OPEN
Baseline supplied by primary: `d35fe74182dbe36e6dd976dc16ecaeaa0d58740e`
Branch supplied by primary: `research/simple-sub-intrusion`
Producer: leaf `/root/nested_recursion_l4_proof`; no delegation
Exclusive write lease: this file only
Authority: existing selected source definitions; no new semantic selection
Budget: one direct constructor-instance attempt; 30 minutes; static source/math only

## 1. Frozen question, hypotheses and quantifiers

The assigned source is

```yulang
my answer = {
  my f x = {
    my g y = { my drop z = y; drop (f y) };
    my first: int = g 0;
    g ()
  };
  f
}
```

For its actual inner Call occurrence `c = f y`, determine whether the
**selected** recursive-pair or captured-step constructor gives a finite
derivation of the actual hereditary f binding and joint current world needed
by Source Generalize L4. Supply every genuine local premise, or identify the
first unavailable judgment by mapping this source to those premises.

Fix the resolved source graph S and original binder tree T, one original
`xi=(nu,K,D)`, the source declaration/entry/role records, and the actual
outer initialization event b. Preserve one whole scoped assignment and
witness strategy. Static lexical correspondence is taken from the frozen
[complete f-y construction](2026-10-12-fy-complete-call-construction.md)
§§2–3; its recovery-free-source qualification remains. Neither this note nor
that correspondence supplies semantic admission or a successful execution.

The required local conclusion, when c has an actual source event e, is

```text
ValueMem_A_f(v_f,r_f,e)
JointWF(C_e,w_e)
the original shared binding/provider/root/capture/event incidences.
```

Here A_f is f's original complete interface endpoint, not a demand-selected
replacement. The conclusion is hereditary: uniformly over every independently
admitted f challenge, every genuine actual-provider decomposition, all finite
initial, administrative, pending and complete developments, and compatible
future restrictions at the original telescopes. Description choices precede
their challenges. EventProof choices depend only on preceding event inputs.
Every shared coordinate has one assignment. There is no termination premise
and no fabricated result for a divergent entry or invocation.

Independent primitive, annotation/profile, entry-carrier, checking, immediate
guard and compatible-history laws remain required at their actual incidences.
Their names, positive occurrence, native constraint origins or stored clauses
do not establish their truth. The attempt does not add them as blanket
success assumptions to finish the original claim.

Exclusions: no new source restriction or annotation requirement; no changed
Call, provider, entry, effect, admission or principality meaning; no solver or
compiler implementation; no parsing, tests, builds or executable inference;
no Git operation; no proof-status promotion or independent certification.

**Result class:** bounded static characterization of two selected constructor
applications, with an exact missing original local judgment. No complete L4
derivation or source-qualified counterexample is established. This is not a
source rejection, an impossibility theorem or a refutation of accepted source
behavior. The parent universal inference/Call claim remains OPEN.

## 2. Exact governing constructors and consumers

[Source Generalize selection](../design/2026-10-08-source-generalize-definition.md)
§§2–3 selects [source rules](2026-10-08-source-generalize-definition-and-proof.md)
§§3–5. Its §2 L4 requires the **actual joint original member/world**
introduction. §3.1 Name restricts an existing certificate; Lambda checks its
body under actual formal entry; Recursive introduction needs a simultaneous
constructor with all original conjuncts. §3.3 `MemberEntry/Live/Internal`
records come from that introduction/registration and do not prove it.
§5.2 allocation cannot manufacture a recursive introduction law.

[Immutable input realization](2026-10-08-call-semantic-input-realization.md)
§§4.1–4.2 is the direct consumer. Its Lemma W restricts ordinary hereditary
binding evidence at a capture/Name; typed Return/rebind installs a supplied
actual result. Its exact Return rule is

```text
ReturnMem_A(Return(v,r,C_e,w_e)) iff
  JointWF(C_e,w_e) and ValueMem_A(v,r,e)
  and the original result/provider/root/world incidences.
```

This rule explains why raw Name resolution and raw Return cannot introduce
f membership. Theorem R subsequently consumes that same f value/world plus
the genuine VIncl and whole-carrier checking at the actual CalRet event.

The two candidate introduction owners are:

| Selection | Actual selected mathematical owner used here |
| --- | --- |
| [Native recursive interfaces](../design/2026-10-08-native-recursive-interface-definition.md) §§2–4 | [Original embedding](2026-10-08-recursive-original-interface-embedding.md) §§2–5,6.3–6.4; O-pair consumes the exact Knu source graph and independent original fields |
| [Contextual Function selection](../design/2026-10-08-contextual-function-membership-definition.md) §3 | [Simultaneous introduction](2026-10-08-simultaneous-immutable-root-introduction.md) §§2–4; the positive Phi clauses and exact two-value-hole Knu argument |
| [Captured closure selection](../design/2026-10-08-captured-closure-constructor-definition.md) §§2–4 | [Captured introduction](2026-10-08-captured-call-closure-introduction.md) §§2–5, Theorem Step in §6; complete Strict composition, singleton H and ordinary captured-f input |

The [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
govern native Simple-sub behavior and proof direction. None of these selections
changes accepted ordinary recursion or permits replacing it with eager solving.

## 3. This source's bindings, events and world incidences

Use distinct source roots `r_f,r_g,r_drop` and formal binding origins
`q_x,q_y,q_z`. Name resolution is

```text
c.callee f -> r_f                 c.argument y -> q_y
drop.body y -> q_y                g 0 / g () -> r_g
answer.final f -> r_f.
```

No occurrence of y denotes z; f inside g is the enclosing live monomorphic
root, not an independent published instance or an outer formal. The formal x
is distinct from all three. Aliases retain the same whole certificate.

The actual closure providers and scopes differ from static source root names:

| Original position | Runtime value/world incidence and binder order |
| --- | --- |
| f initialization under answer | One actual f closure `v_f` and provider at b, with its recursive reference; `A_x` is declared before f's challenge |
| f's admitted invocation h_f | Receipt, designated Force, actual x Return/rebind if it occurs, then the f-body world; no g value exists before its own Lambda initialization |
| g initialization in that f body | A new `v_g[h_f]`, provider/allocation at that actual body event, capturing the same `v_f,r_f`; g's description region and `A_y` remain before its own challenge, below the enclosing f-body dependencies |
| g's admitted invocation h_g | Receipt/Force and actual y Return/rebind; y gets the certificate for that same returned value in that actual world |
| drop initialization in that g body | A new `v_drop[h_f,h_g]` with capture of that exact y; `A_z` precedes drop's challenge, below this construction event |
| outer Call `drop (f y)` | Callee Name returns this drop; its argument is inert reification of the whole inner Call code, not immediate execution of f y |
| actual inner event e of f y | Under a designated execution of that whole argument, including drop's Value-entry Force on the source diagonal; after drop receipt and before any z Return/rebind supplied by this inner computation |
| recursive f invocation from e | Another f receipt/entry/body event; its own nested g allocation is indexed by that new event, not by h_f |

The original body constructor tree, suppressing profiles and full interfaces
but preserving code occurrences, is

```text
Lambda x:
  Bind g (Result(Lambda y:
    Bind drop (Result(Lambda z: Result(Name y)))
      Call(Result(Name drop), whole-argument[Call(Name f,Name y)])))
    Bind first (actual int check of Call(Name g,0))
      Call(Name g,())
```

The whole-argument notation records the selected inert reification; it is not
an additional source wrapper or consumer. In particular c's **static** g-body
occurrence and its **actual** delayed execution event have different roles.
The inner argument to f at c is itself the whole Name-y carrier. A designated
execution uses the current world; no creation-time configuration or exited
activation is restored. A pending drop argument Force retains c and the
remaining actual z-rebind/drop-body/invocation-return suffix. It supplies no z
before a Return. A latent body proof must cover c uniformly even if no whole
outer invocation ever returns.

At e the relevant installed/captured bindings share the same actual event
history and `xi`; worlds are not selected separately to validate f, y and
drop. Whether particular old bindings are exposed by a capture projection is
the original dependency-closed projection, not permission to remove their
world/certificate dependencies. Mere numeric inference levels do not identify
these worlds, event witnesses or introduction premises.

## 4. One direct application attempt, including the first failed premises

### 4.1 Unify this source with O-pair/Knu

The actual selected Knu constructor (§2), retained by O-pair (§3), requires

```text
v_a = Closure(Pure,ValueEntry(u),Result(Name b),eta_a)
v_b = Closure(Pure,ValueEntry(v),Result(Name a),eta_b)
eta_a(b)=v_b; eta_b(a)=v_a
eta_K(a)=v_a; eta_K(b)=v_b
```

Its complete invocation is receipt; Force; actual formal rebind;
Return(Name opposite); original invocation return. O-pair's source-owned
guard proof (§5) reads the concrete fact that each body contains one Name/
Result and creates no new closure. Both actual values are the original
simultaneously installed K nodes. Its two holes are those exact values and
lawful restrictions, not additional future allocation families.

Try `a=f,b=g`. The first raw constructor premise fails to unify:
`code(v_f)` has `Bind g` and two g Calls, whereas the required code is
`Result(Name g)`. Moreover there is no preinstalled actual `v_g` captured by
f at b: `v_g[h_f]` is created only inside the later f-body event. The second
required code is `Result(Name f)`; the actual g code is Bind drop followed by
Call drop whose delayed argument contains Call f. These differences are
actual owning code, allocation and capture premises, before any independent
guard truth is considered. Alpha renaming, complete typed-copy transport,
equation registration or provider-name equality does not change them.

Thus O-pair's actual source premise has not been produced for this source.
Its ME-pair finite-prefix witnesses likewise expand the fixed
`Rebind; Result(Name opposite); EndInvocation` suffix and do not expand this
Bind/Call/allocation suffix. This conclusion is about theorem instantiation;
it does not prove that a different direct coinductive proof cannot exist.

### 4.2 Unify g formation with captured Step

The selected Step source (§2) is exactly

```text
lambda(formal_f,
  bind(step,result(lambda(formal_x,call(name formal_f,name formal_x))),
    result(name step)))
```

Attempt the most favorable local renaming: Step's captured value f becomes
the candidate's recursive f; Step's new step becomes g; Step's inner x
becomes y; the outer post-entry event becomes this actual g-construction
event. This preserves the desired callee and carrier identities.

The exact first unavailable **semantic** input is then Step §2's

```text
ordinary V*(A_f,v_f,r_f,e_g_pre), together with its result incidence
and the valid immutable preconstruction world at e_g_pre.
```

In the selected source, the outer Value-entry carrier Return supplies that
ordinary captured-f certificate. In this candidate, the enclosing f entry
Returns **x**, not f. The enclosing recursive f registration retains its
raw root/reference and monomorphic description, but no already established
ordinary f certificate is supplied by that Return. g cannot supply it: g
has not yet been introduced. The later final `answer` Name-f Return would
consume f membership and cannot introduce it retroactively.

Step's §5.1 H contains only the newly constructed step/g actual value and
its restrictions. It explicitly supplies no captured-f membership or world,
carrier, continuation, guard or authority hole. In Step's proof (§6,
“Construction and captures”), the captured f's **ordinary** certificate is
unfolded before embedding into the relative background. A temporary recursive
assumption `f in S.V` is not this input; replacing it changes the premise.

There is also a distinct raw source mismatch after that missing input:
Step's local body is one Name/Name Call returning f's invocation result,
whereas g performs local drop construction and Call drop. Drop's Value entry
forces the whole f-y computation and returns the captured y after the actual
z rebind. It is not source equality to the single selected Call body, even
if some terminating pure outputs happen to agree. Strict constructs a
complete descriptor for a supplied body; registration or a Strict-shaped
endpoint alone does not prove that this actual closure realizes it.

Applying Step to f itself would also require an ordinary external captured
callee and the selected single-Call body; it supplies no recursive f
introduction. Applying it to drop does not repair the f premise, and drop's
body is Name-y Return rather than Step's Call body.

### 4.3 Exact local stop and relation to c

After the raw O-pair mismatch and the mapped Step input above, attempt Name
at the actual inner c. Lemma W requires an already hereditary f projection
in the same persistent telescope; the Return rule requires both

```text
J_c = ValueMem_A_f(v_f,r_f,e) and JointWF(C_e,w_e)
      and original correlated incidences.
```

No selected application above supplies J_c. This is the first outstanding
recursive semantic admission input for the frozen f-y derivation, separate
from actual source registration/checking records. Typed y Return/rebind can
supply y's own certificate; it cannot supply f's. Restriction cannot create
an initially absent f certificate or a jointly valid world.

The exact owning missing construction is f's recursive Lambda/installation
at b, with body validation uniform under f entry and dependent local g/drop
formation. A genuine proof must replace the actual f value assumption in
the selected positive operator while constructing all relevant worlds and
body/pending/future obligations jointly. In the existing Phi language the
decisive unfinished proof clause would be

```text
H_f subset Phi(S).V
```

for the actual f tuples and lawful restrictions, with S's body fields
covering the actual `v_g[h_f]` and `v_drop[h_f,h_g]` families at their
original events. This identifies the missing clause of a possible direct
proof; it is **not** an established invariant, an added semantic rule or
an assumption used to claim closure. Merely putting those tuples in S,
or assuming their transition/checking clauses in a checker, does not prove
postfixedness. Step cannot be invoked to replace H_f without the very
ordinary certificate this construction seeks.

This attempt stops here. Complete same-value checking, carrier admission,
receipt/receiver acceptance, invocation result/future fields, annotation
checking for first, and all original W/Z alternatives remain separate
genuine premises. None is silently discharged by this reduction.

## 5. The exact odd/even witness at the same seam

The user's source is

```yulang
my odd n =
  my even n = if n <= 0 { true } else odd(n - 1)
  even(n - 1)
```

Keep `q_n_outer` and `q_n_inner` distinct. Test `n <= 0` and the argument
of inner `odd(n-1)` use `q_n_inner`; the final `even(n-1)` uses
`q_n_outer`. Inner odd resolves to the same outer recursive root r_odd;
the final even resolves to the nested binder r_even. The original source-owner
cycle across levels does not make two actual sibling closures at one
allocation event.

Under the accepted definition-root ownership rule recorded in the frozen
admission audit, the exact original-root incidences are

```text
r_even -> r_odd   (odd Name in even's nested initializer)
r_odd  -> r_even  (even Name in odd's final body expression).
```

Thus those two original roots form a nontrivial Value-reference SCC on that
resolved source graph. This is the accepted source-incidence result, with
distinct shadowed formal roots retained. It is not a jointly installed
hereditary world, a parent/copy pair, or proof that current HIR emits the
graph; actual exact-source operational reachability remains unproved.

Try O-pair with `a=odd,b=even`: odd's body is a sequential nested
initialization then a Call, and even's body is a guarded Branch with a
recursive Call arm. Both fail the required opposite Name/Return body
equations. `v_even[h_odd]` is allocated under odd's invocation, so the
preinstalled opposite capture equation also fails. Try captured Step with
captured f=odd and new step=even: the enclosing carrier Return supplies
the outer n, not ordinary hereditary odd membership; its singleton hole
does not supply odd. Its selected single-Call body also does not cover the
Branch, primitive test, arithmetic or true's original local law.

These are exact mathematical constructor mismatches, conditional on the
source's original resolved/primitive records. The frozen
[admission audit](../progress/2026-10-12-odd-even-source-admission-audit.md)
separately reports that the exact indented/conditional source has no established
current private HIR route. That operational gap is not used here as a semantic
rejection or as a way to discharge L4. No brace replacement or executed
analogue is substituted for the user's source.

## 6. Proof-obligation economy and next owner

This is one direct application attempt; O-pair and Step are the two checked
candidate introduction constructors within it, not two completed proofs.
The predecessor f-y note already localized L4; this note adds actual
source-equation unification, ordinary-versus-relative capture evidence, and
dependent allocation/event incidence. It does not count another description
of the missing premise as progress toward the parent theorem.

The missing premise is A/B: valid accepted recursive closures/worlds and
ordinary nested recursion. No optional stronger characterization is needed
to excuse it. The owning phase knows the raw recursive root, complete code,
actual capture edges and local allocation scopes at recursive registration
and Lambda formation. Source Generalize already says to retain their
MemberEntry/Internal/Event incidences; recovering them from levels or
solver success would add D reconstruction debt without proving the semantic
clause. A retained record alone cannot establish universal body correctness.

**One next action:** the primary assigns the recursive source-introduction
proof owner the actual f `H_f subset Phi(S).V` clause, with this unchanged
Bind/Call body and event-indexed g/drop worlds, and independently established
entry/checking/guard contracts. The decisive evidence is a complete direct
postfixedness derivation or a source-qualified falsifier of that clause;
another application of the exact pair/Step results cannot supply its absent
premise. No third equivalent constructor application is proposed.

## 7. Verification, frozen dependencies and integration packet

Checks performed: bounded cat/sed/rg reads, one static constructor-instance
derivation attempt, SHA-256 snapshots, and leased-note whitespace/link
integrity checks. No tests, builds, parsing, executable inference, probes,
measurements, Git operations, external communication or child launches.
At most four independent lightweight read commands were batched; zero heavy
processes and zero inference samples. CPU/RSS and reasoning wall time were
not instrumented; work stayed within the 30-minute allocation.

Requested runtime: normal Sol/high proof leaf. Observed identity:
`/root/nested_recursion_l4_proof`; effective model/effort metadata unavailable
and reported **unknown**. Configured agents defaults are gpt-6.1-sol/high
and the prover role omits model/effort pins; these facts do not establish
actual runtime routing. No Astra or hot reload is claimed. The yulang-proofs
skill was read and applied under the explicit leaf/no-delegation packet.

Frozen semantic dependency SHA-256 snapshots (current files, rechecked at
handoff; no dependency was written by this producer):

```text
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
a9f833556a7e7c361c5b602c982de96b78663a77099999206bdb7bda6da67903 notes/design/2026-10-08-native-recursive-interface-definition.md
6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd notes/design/2026-10-08-captured-closure-constructor-definition.md
3bcc290f0fab01f08272d83c358f491df377da46f2022412c176184533d9f872 notes/theory/2026-10-12-fy-complete-call-construction.md
29a643b5823a2732129c2e9a4924e3459648e315d9c916be9493e4218a2af680 notes/theory/2026-10-08-recursive-original-interface-embedding.md
0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f notes/theory/2026-10-08-captured-call-closure-introduction.md
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0 notes/design/2026-10-08-contextual-function-membership-definition.md
a5efa7056b12f931892548ecf3366d66156627ec44577c99d20ca48596438ae6 notes/theory/2026-10-08-simultaneous-immutable-root-introduction.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a notes/theory/2026-10-08-call-semantic-input-realization.md
2bb4b6a1389dc054f6a16a1bf566b68cba7648cd31355a4b10c29b1f91d2cb06 notes/progress/2026-10-12-odd-even-source-admission-audit.md
```

The assigned frozen baseline is primary-issued. No Git read or mutation was
performed; baseline-to-file blob equality remains the primary's integration
check. The first five and contextual/input-realization hashes agree with the
frozen predecessor's recorded dependencies. Its own current file and the
underlying selected theorem files are pinned by the hashes above, not by
historical pre-repair producer hashes quoted in design records.

Unverified scope: actual source admission/execution; complete recursive
introduction; all independent checking/primitive/annotation/guard truths;
complete Call and its alternatives; qualifying extrusion/intrusion,
fixed/template placement, effects, principality and production correspondence.
No consumer activation/replay theorem follows from stored source clauses.

Commit packet:

- Exact leased path: `notes/theory/2026-10-12-nested-recursive-l4-proof.md`.
- Baseline: `d35fe74182dbe36e6dd976dc16ecaeaa0d58740e`.
- Changed dependency hashes: none within this attempt; before/after snapshots
  equal. Primary verifies their equality to the assigned baseline before
  integration.
- Claim/review: frozen, unreviewed bounded static characterization and exact
  local obstruction; no complete theorem, counterexample or gate promotion.
- Checks already run: static source-rule reads/unification, dependency hashes,
  leased-note whitespace and local-link checks; no executable inference.
- Proposed one-line checkpoint message: `research: map nested recursive L4 constructor premises`.
- Shared-record delta left to primary/curator: keep parent inference/Call and
  L4 introduction OPEN; attach this exact ordinary recursive-f certificate /
  event-indexed postfixedness dependency to the owning recursive source proof
  lane. No tasks, theory map, design, index, questions or production path edited.

Writes stop at handoff. Independent review and any accepted status implications
remain the primary's responsibility.
