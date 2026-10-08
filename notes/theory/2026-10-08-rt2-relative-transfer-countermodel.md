# RT.2 relative Function readout: finite separation and legal-model boundary

Date: 2026-10-08
Status: Conditional falsification research; unreviewed
Baseline: `3cfdbaa7dd80878e8ec5599f805172dd8d095506`
Exclusive producer lease: this file only
Method: finite positive-dependency separation, then source-shaped legality audit
Claim class: algebraic counterexample to a proposed implication; conditional semantic attack
Definition selection / complete Yulang countermodel / gate closure / implementation authority: none

## 1. Result

An ordinary final-model same-value inclusion does not, as an algebraic law,
force the non-hole Function readout required by RT.2. A four-coordinate
positive system below separates them even when the returned value has a
non-hole relative certificate at its source descriptor. Thus merely checking
that f is not itself a declared hole does not repair the proposed transfer.
Its certificate can depend on a declared hole in a returned value or capture.

The source-shaped realization of this separation is conditional. The inspected
selected definitions leave the complete independent challenge/carrier
interpretation as an input. They do not supply the original full-domain
admission and interpretation witnesses needed to certify this example as a
legal countermodel of the entire selected Yulang kernel. This note therefore
does not claim that RT.2 is false for every legitimate completion, or that
unconditional outer membership is impossible. It identifies the exact
additional interpretation that would decide the attack.

No other concurrent producer's artifact was read. Existing committed governing
sources were inspected directly. No model, domain restriction, semantic leaf,
source rule, or production behavior is adopted here.

## 2. Governing premises and the disputed implication

The governing selected scopes are:

- [Contextual Function definition](../design/2026-10-08-contextual-function-membership-definition.md)
  §§2–3: same actual provider, independent complete challenges, full observation
  and future envelope, ordinary pointwise VIncl, and the positive hereditary
  interpretation.
- [Complete captured closure definition](../design/2026-10-08-captured-closure-constructor-definition.md)
  §§2–4: Strict, the exact local step hole, and ordinary actual-f input evidence.
- [Approved nested source](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §2: sequential creation and Return of step, retaining the same captured f.

The target is [outer apply introduction](2026-10-08-outer-apply-closure-introduction.md)
§3, RT.2. Write

```text
M    = nu Phi
B_as = nu (Phi with its V component augmented by H_a union H_s).
```

The invalid general shortcut would be

```text
B_as.V(A_f,f),  M.V(A_f,-) subseteq M.V(F_c,-)
------------------------------------------------
Phi(B_as).V(F_c,f).
```

Ordinary VIncl is the second premise. It is not quantified over arbitrary
relative interpretations. Whole-argument checking supplies the checked
carrier admission and challenge formation; it has no rule deriving actual
provider output membership from those facts alone.

The established sufficient route remains

```text
M.V(A_f,f)
  -> M.V(F_c,f)
  -> Phi(M).V(F_c,f)
  -> Phi(B_as).V(F_c,f).
```

The last step is positivity and `M subseteq B_as`. It is exactly the ordinary
certificate unfolding in [captured introduction](2026-10-08-captured-call-closure-introduction.md)
§6, the paragraph beginning “For f, first use the ordinary independent VIncl
action.” No reverse embedding of relative certificates is established.

## 3. Finite algebraic falsifier

Use four Boolean coordinates `(a,b,s,c)` in the value component. Other
coordinates may be taken as fixed true parameters for this algebraic lemma;
this is not an assertion that Yulang worlds or carriers are proof-free.
Define the monotone map

```text
phi(a,b,s,c) = (s,a,c,false).
```

The intended labels for the later conditional attack are:

```text
a : apply at its natural outer interface
b : returned provider g at its source interface G
s : the actual step capturing g at F_step
c : that same actual provider g at checked interface C.
```

Every fixed point of phi satisfies `c=false`, hence `s=false`, `a=false`, and
`b=false`. Its greatest fixed point is therefore

```text
m = (false,false,false,false).
```

At the ordinary interpretation, inclusion of b-members in c-members holds:
both predicates are empty. This is a valid semantic inclusion proposition;
no successful solver query or nonempty source membership is asserted.

Add declared assumptions only at a and s:

```text
psi(a,b,s,c) = (true,a,true,false).
beta = nu psi = (true,true,true,false).
```

Now b is a **non-hole** relative member, with its actual one-step source
readout `phi(beta).b=true`. Nevertheless the target readout is
`phi(beta).c=false`. The proposed implication fails. Even the stronger
premise consisting of a source one-step readout plus final-model VIncl
does not force a target one-step readout.

This four-coordinate computation proves only the stated algebraic separation.
It does not instantiate source M_E, a complete challenge domain, W/T/Car, or
the full original dependent tuple. In particular, setting other coordinates
to true is not a permitted shortcut for the legal-model audit below.

## 4. Source-shaped conditional realization

A concrete discriminator suggested by the finite system uses the same actual
apply closure a and a separately registered Pure Value-entry provider g:

```text
g = Closure(Pure,ValueEntry(I_u),result(name apply),captureReferenceTo(a))
G = Strict(I_u,z:Unit,PureReturn(F_apply^nat),IF_g)
C = Strict(I_u,z:Unit,PureReturn(Unit),IF_check)
A_f = G
F_c = C.
```

These are candidate independently fixed complete contracts for this attack,
not replacements for any already fixed original descriptor. The actual g
remains g at one retained provider/root. It receives an I_u carrier, performs
the designated Force after receipt, and then returns a without invoking a.
At a completed inner pure Name argument returning Unit, the actual g Return
has a callable value a, which is not a ground Unit. Therefore the complete
C observation contract fails at a genuine actual Return. Actual input
acceptance can hold: this attack needs no inlet mismatch or false guard.

At G, that same Return instead asks for a at F_apply^nat. In B_as it may use
H_a. The actual g capture also uses that exact a/root certificate. Thus a
non-hole source Function clause for g can depend positively on the apply hole
in both its capture and returned-value fields. If the complete independent
world/carrier/continuation interpretation and all immediate guards are
genuinely supplied, the original Strict and Return constructors can build
the full G readout from those fields.

An outer carrier t_g returning g at G would then supply a relative g result.
The actual apply body makes the real step s_g capturing that same g. Its
future body invokes g on the actual Name/Return/Delay carrier. The ground
result mismatch at C defeats the needed checked-provider readout. H_s may
assume the exact s_g value while constructing B_as, but it cannot alter g's
actual Return or make the callable a a Unit.

The finite pattern is consequently `a requires s`, `g:G requires a`,
`s requires g:C`, while `g:C` fails at the same real returned value. The
complete constructors contain further positive world/carrier/pending fields;
this pattern is not claimed to be their entire equation system. A source
world containing a, g, and a created step would need every binding unfolded
in the same operator, with all actual provider, registration, incidence and
current-authority evidence. No world, carrier, or continuation is declared a
hole in this proposed realization.

For an ordinary interpretation in which no value realizes G, VIncl(G,C)
holds vacuously. Establishing that emptiness for the **full** original value
universe is an additional requirement of this realization. It cannot be
proved by examining g alone: another callable could realize G. A finite
chosen universe or omission of other admitted providers would not establish
the original inclusion. This is a second concrete stop condition.

### Complete-domain and future audit

The decisive bad Return is one member of the full observation family, so it
already refutes a C readout whenever its real challenge is admitted. Prefixes,
requests, raw resumes and future uses must still remain in the original
relations. Nothing here permits replacing the domain by this one successful
carrier or discarding other observations. g's positive G readout would have
to cover **every** original compatible I_u challenge and all its Force
progress, current worlds, response/continuation fields and later demands.

Likewise the outer t_g must have original inert formation, scope/license and
the universal designated-execution certificate at I_f, not merely one Return.
Every retained alternative needs its original contract. No unanchored arm
receives a source-execution witness. An immutable capture supplies no live
authority grant. Source roots, event restrictions and new parameter/result
incidences cannot be collapsed into the four Boolean coordinates.

Thus this is a **conditional source-shaped attack**, not a certified legal
finite interpretation. It uses a valid observable discriminator, but the
missing full-domain witnesses and global inclusion cannot be fabricated.

## 5. What exactly the current domain does and does not supply

For an independently ordinary `M.Car(I_f,t)` certificate, Return inversion
supplies `M.V(A_f,f)` at the same actual result/root/current event. This is
the selected ordinary carrier/Return meaning, and supplies the sufficient
route in §2. The local Step/Block/OuterTrace theorems consume this input.

For an outer relative `B_a.Car(I_f,t)` certificate, inversion instead supplies
`B_a.V(A_f,f)`. The selected positive clause interprets the carrier's result
and world fields in its current relation parameter. Original checked inlet
acceptance by itself has no clause converting this result to an ordinary
M certificate. Independent admission and hereditary carrier validity are
distinct obligations.

Whether **every** carrier in the unchanged outer challenge domain already
comes with an independently ordinary full M carrier/result certificate is
therefore the specific missing interpretation question. If that uniform
ordinary certificate is actually supplied, RT.2 follows by §2. If the domain
instead contains genuinely relative declared-hole carrier/world fields, a
separate source-owned relative checking action or joint source construction
is needed. One cannot settle this by defining the domain as those cases
with the desired ordinary certificate.

The selected [input realization](2026-10-08-call-semantic-input-realization.md)
§2 leaves the independently interpreted complete admission/observation
interfaces as inputs; §3.2 specifies ordinary VIncl; §4 specifies the
hereditary fields. The [source call-generation relation](../progress/2026-10-06-source-call-generation-construction.md)
§5 retains independently interpreted VIncl, whole-argument checking and
supplied complete decoration. These do not supply the missing exhaustive
domain/carrier interpretation or a parametric checking law. No completed
foreign-kernel model was located in this dependency scope.

## 6. Coincident f=apply test

The source-shaped attack in §4 is noncoincident: f is g and the checked
interface is C. It does not refute the exact identity instance
`f=a`, `F_c=F_apply^nat`.

For that instance, identity VIncl preserves a relative H_a certificate. It
does not unfold the H_a branch into `Phi(B_as).V(F_apply^nat,a)`. The selected
local Step proof's coincidence remark is justified by its independently
ordinary input certificate obtained before embedding; it has no corresponding
premise for an outer hole-derived input.

Conversely, absence of a direct unfolding rule does not prove that the desired
front is false. A genuine joint postfixed source construction may introduce
apply and all steps generated by its admitted invocations together. The full
outer readout then follows from actual source cases within that construction,
rather than from identity inclusion alone. This note constructs no such
family and excludes no coincident challenge.

## 7. Conclusion, checks and handoff boundary

The proved finite result rules out treating final-model VIncl as a general
relative-readout law, including when the source relative certificate is
non-hole. The legal-model attempt identifies two unsupplied witnesses:

1. authentic full independent challenge/carrier/world interpretation admitting
   the proposed relative t_g at every original required incidence and future;
2. genuine ordinary VIncl(G,C) over all original decorated values, not merely
   the examined g or a chosen reduced universe.

The producer stops at those witnesses. No failing tuple is declared valid,
no original domain is narrowed, and no impossibility or unconditional
countermodel is claimed. The recommended next action is to pin the actual
full outer-domain carrier interpretation and its source-owned checking
evidence: ordinary uniform certificates would close this RT.2 route; genuine
relative fields require one-step checking transport and actual source
replacement of the apply hole. This is an input-owner/proof task, not another
trace or Boolean-table expansion.

Checks: documentary source reads, direct dependency SHA-256 capture, exact
leased-path existence check, and focused whitespace/link/dependency integrity
checks. The four Boolean equations were evaluated by hand. No executable
model, test, build, broad experiment, random seed, or performance measurement
ran. Counts: zero probe processes and zero measurement samples. Independent
review is pending; the producer does not certify its own result.

Shared task/theory/design records are intentionally deferred to the primary.
Suggested research-only checkpoint message:
`research: separate final VIncl from relative Function readout`.

### Direct dependency snapshot

| Path | SHA-256 at the stated baseline |
| --- | --- |
| `notes/theory/2026-10-08-outer-apply-closure-introduction.md` | `8a02c821a6b36486d613e5c44d1f96a5c6c0146d8bc4c8ebd99c032f422d4ea2` |
| `notes/theory/2026-10-08-call-semantic-input-realization.md` | `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a` |
| `notes/theory/2026-10-08-captured-call-closure-introduction.md` | `0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f` |
| `notes/theory/2026-10-08-simultaneous-immutable-root-introduction.md` | `a5efa7056b12f931892548ecf3366d66156627ec44577c99d20ca48596438ae6` |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| `notes/design/2026-10-08-captured-closure-constructor-definition.md` | `6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
