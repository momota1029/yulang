# First Call local result view: fixed-dependency audit

Status: bounded research characterization, accepted by independent review;
recursive complete challenge/IF/ResultBind projection remains OPEN
Date: 2026-10-16
Baseline: primary-pinned `4704b99e2`; native production `bf0562382`
Method: complementary static source-constructor falsification and native-owner inspection
Lease: this new file only; other concurrent work preserved

Primary review receipt: `ordinary_carrier_semantic` accepts the bounded field
audit at producer SHA-256
`da5ce19b8fadcffca823f9c245280c3755af9bae3c433df6a4270bd409dcb177`.
The audit correctly leaves recursive projection unproved. Its companion source
proposal received an accepted MAJOR for the retained typed d→g:A1 dependency;
the repaired companion withdraws eligibility and has accepted correction review.
No absence-of-dependency, source rejection, constructor selection or original
parent closure is inferred from this audit.

## 1. Question and result

For the actual source constructor

```yu
my receive (f: () -> 'a) = { my g = f(); g() }
```

does an actually fixed field of Call/Return/ResultBind/g publication have a
free dependency on the first Apply's candidate-local result description A1?
The relevant fixed closure is the **whole** SourceGeneralize §5.1 closure,
including actual installed contracts, shared evidence, private captures,
latent admission and future fields. A scalar lower-bound argument alone
does not answer the question.

**Result:** no source-qualified counterexample was authenticated. The
inspected ordinary source constructors introduce A1 as a checking description;
they execute no conversion or dictionary selection using that description.
The audit identifies the exact distinction needed at ResultBind: the actual
returned/installed evidence tuple remains fixed, while a proof checking that
same tuple at A1 may belong to the description's Check/EventProof region.
An actual monomorphic dictionary selected by evaluation cannot be moved into
that region. The distinction applies to external returned providers as well
as closures; returned external providers are not own-component closures.

This is bounded constructor coverage, not certification that the full fixed
closure avoids A1 for every original provider/challenge. The remaining proof
must apply the owning classification recursively to the complete returned
certificate and to every retained context operand, preserving the original
scopes. Neither native metadata nor the absence of a runtime conversion in
this syntax establishes that universal statement by itself.

## 2. Governing premises and ownership distinction

The selected Application interpretation §§1–3 fixes the original source c,
Gamma, f's independently formed full Function contract, alpha, A1/E1, IF,
provider/captures and all original xi/return witnesses. A1/E1 are introduced
before execution and observation. There is no RHS annotation on g. The
selected checking view adds full same-value Value(A1) and the local E1
guarantee to the same complete ReadInvoke certificate; it changes no event,
provider, role, return or world.

SourceGeneralize §3.3 (`2026-10-08-source-generalize-definition-and-proof.md`,
lines 224–268) makes the necessary distinctions explicitly:

* Mono/Established follows an external installed certificate's **entire**
  free dependency telescope.
* Executed/OneShot fixes the selected execution and its actual installed
  contract/evidence; Shared keeps its one actual binder and dependencies.
* ViewLogic/EventProof certifies the same execution in its source description
  region. Such a proof may differ between independent description frames.
* An own-component closure's Internal description is separate from its raw
  returned object. This exception does not classify an arbitrary returned
  provider's private contracts.
* An actual installed monomorphic dictionary chosen by evaluation remains
  Established/OneShot, even if Function-shaped.

At **g's own publication**, g's new inferred result view is not an already
external Mono(g, Value(A1)) imported before that publication. The preceding
external binding is f with its full alpha contract, together with genuinely
established returned/captured evidence. SourceGeneralize §5 (lines 412–424)
selects the current publication's final synthesis/check root; §5.1
(lines 491–495) permits fixed operational fields and schematic descriptions
of the same value. Importing a hypothetical pre-existing Mono(g,A1) at that
point would pre-decide the dependency question. Conversely, calling the
entire new environment entry a variable proof would incorrectly discard its
actual retained fields.

After a publication, a particular monomorphic handle does retain its entire
instance: SourceGeneralize §3.4, lines 318–328, and §5.2, lines 525–530.
This audit gives aliases no independent description choice.

## 3. Constructor-by-constructor dependency attack

| Actual field or operation | Responsible source constructor | Audit result and limit |
| --- | --- | --- |
| Original f identity, role, full alpha contract and private captures | Parameter/Import/Name; SourceGeneralize §§3.1,3.3 | Fixed. A1 is a later caller-owned result description, not a new formal annotation on f. Existing free descriptive fields of f remain fixed; their relation to A1 is not itself a new free reference from the installed contract. |
| Unit value, inert carrier, actual argument captures and entry | Literal/Return/Delay and selected Unit inlet | No result conversion or result-contract selection. Preserve the authentic carrier's full scopes/license, and the independent checked challenge; Unit shape alone is insufficient. |
| Actual callee, phases, C2 and return/provider incidence | Original full P_F and Call/Return constructors | Fixed actual operands. Full P_F is used on its original alpha contract; A1's checking proof does not authorize changing any selected runtime phase or evidence. |
| Same-z W_z and matching F_R,z | Checked-result construction §6, lines 277–288 | Same decorated J_z, not two marginal values. Reindexing/checking its current typed presentation does not change a private packet's original reference. No own-component classification follows from returning it. |
| Hereditary alpha certificate and latent/private contract already in J_z | Same actual f's original result clause | Retain the complete actual certificate and all genuinely fixed free dependencies. This includes contracts with current authority requirements; a departed grant is not silently kept live. |
| New full Value(A1) proof | Checked-result construction §4 step 4, lines 207–214; SourceGeneralize §3.2.3 | Same-value checking on J_z. This creates a proof at the new checking view, not a new executed dictionary. It must cover full dependent/latent guards and retain its legal binder position. |
| Actual g binder, C2, rebind path, retained shared fields | Semantic-input realization §4.1, lines 333–337; source-interface construction §5, lines 388–396 | Fixed actual result and shared fields. The hereditary A1 proof supplies the new logical membership premise. The proof must preserve this split field by field; the printed assertion `g:Value(A1)` does not determine the classification of every subfield. |
| Actually selected dictionary, conversion or installed mono contract in a return | SourceGeneralize §3.3, lines 239–267 | Fixed, including all free type/evidence dependencies. No actual constructor in the displayed Name/Unit/unannotated-Apply route selects one using A1. An independently supplied opaque constructor keeps its actual L1 telescope; it cannot be classified solely from the return's type shape. |
| Pending request, actual response, raw suffix and resumed C2 | Checked-result construction §4 steps 5–6; original Bind | No g entry before Return. The same actual response/suffix survives; new logical proofs remain under the same event, not a new per-frame execution. |
| Future membership at the same returned provider | Semantic-input realization §4.1, lines 304–320; checked-result §4 step 6 | The A1 proof is hereditary at the later actual event. Fixed private contracts and current Observe/Receive/Grant/eligibility operands remain actual; first-return activity is not a substitute. |

These cover the selected ordinary Name/Unit/Call/Return/Request/Bind outputs.
The decisive difference from a type-shape census is the classification at the
**introducing source rule**. The original complete P_F may expose any actual
provider, not just a syntactic Lambda. Its private certificate must be retained
as supplied, while the same-value check concerns that complete supplied tuple.

SourceGeneralize §6, lines 664–688, independently distinguishes these cases:
Call cannot choose its callee from the checked type; reading another typing
proof does not rerun the initializer; same-value checking changes an asserted
contract; an actual method/adapter requires its actual conversion constructor.
Thus an alleged counterexample which simply assumes an A1-directed runtime
cast at this unannotated result has not authenticated an original source rule.

## 4. Captured-return falsifier and opaque-provider boundary

The existing source-qualified captured/direct factory instance is a useful
attack on an overbroad own-component argument. In
`2026-10-16-native-returned-callable-incidence-instance.md` §2, a factory
returns `captured`, whose private `thunk` binding originates outside the
factory; its alternative returns `direct`. Both providers coexist. The
captured result keeps its original thunk reference and packet; the direct
result keeps its own operation origin. These are observably different later
incidence/authority configurations.

Returning `captured` at the first Call does not make its private thunk contract
an A1-owned description. It remains an original external contract. Checking
the same returned value at A1 adds the full logical proof, and does not copy,
reconstruct or convert that thunk. This rules out the proposed *reason*
“all returned Function evidence is Internal” on an actual source instance.
It does not yield a fixed free dependency on A1: no source operation in this
instance installs a dictionary selected from A1. The result's original alpha
certificate and its private evidence remain the base of the same-value check.

An arbitrary opaque provider can similarly carry actual monomorphic evidence.
Its returned certificate is not erased by this argument. To refute eligibility
one needs an authentic field path of the form

```text
actual return / installed shared tuple
  -> actual mono contract or executed evidence field
  -> free original A1 declaration
```

with its introducing L1/ordinary source rule and original scope. A dependence
only of `Check(alpha,A1,J_z)` on A1 is not that path. A primitive which takes
an A1 descriptor/dictionary as an actual operand would need its actual
declaration and source operand introduction; no such operand is established
by the displayed Unit input or unannotated result rule. This is a falsifier
criterion, not a language prohibition or a claim that every unknown primitive
has been inspected. No unknown State/adapter/dictionary rule is invented here.

## 5. Actual native copy decision, including context additions

The source cut is local g boundary1, distinct from outer receive boundary0.
`candidate_source.rs:757–763` visits the initializer at the next level;
`:824–845` emits its one-shot effect outside the generalized value and installs
the unannotated initializer root. `candidate_scheme.rs:1480–1494` retains the
LocalScheme root/boundary, not a runtime-selected result contract. Name's
actual route captures that root and prepares FreshUse at `:1524–1541`.

The reviewed demand-frontier note §§2–3 supplies the actual alternatives:

* if the first result has merged with its level1 extrusion root, local g
  capture shares it;
* if A1/r remains level2, local capture copies r and shares its level1 positive
  lower y. Restoring y as the positive owner on the fresh root preserves the
  source relation to fixed alpha. An ordinary comparison must not replace
  that restoration orientation.

These are operational cases, not semantic eligibility criteria.
`Capture::row` (`candidate_scheme.rs:355–379`) uses the canonical row's
`level > boundary && !non_generic`; preparation rechecks that condition
(`:1135–1147`). Intrusion merges levels by minimum and non_generic by OR
(`candidate_intrusion.rs:583–598`). Consequently a canonical equality with
an older fixed row does not leave a separate eligible high-level row merely
because its old raw ID was A1. A semantic constraint to an older row is not
itself canonical equality or proof of a fixed-field free dependency.

Nonidentity contexts cannot be omitted from this correspondence:

* capture follows every retained relation context, its payload views/tails,
  and deferred negative demand roots (`candidate_scheme.rs:852–875`);
* local rows' direct/exact bounds are retained, while older shared rows remain
  live (`:645–690`); this is not copying a snapshot of their mutable bounds;
* preparation uses the common row map for effect views and context payload
  tails (`:1173–1189`, `:1216–1233`), then reconstructs Function terms from the
  mapped children (`:1268–1287`);
* attachment bundles retain their source occurrence/sets (`:1152–1161`);
  scoped demands/transformers use the owned scope/input map (`:1294–1317`);
* historical bound evidence snapshots are imported unchanged (`:1353–1356`).
  Their source-bound/relation fields record historical admission and emission
  provenance (`candidate_context.rs:468–496`); an old A1 occurrence there is
  not by itself an actually installed source contract.

`context_payloads` covers PrefixLeft, SuffixRightPops, Replay, Swap and
WithoutLeftFilter (`candidate_context.rs:1593–1620`). BothFromRight currently
returns unavailable: this audit grants it no successful FreshUse action,
and does not infer a source-language rejection from that guard. Scoped local
callee refusal is likewise not removed. Neither context reachability nor a
successful copy proves the semantic classification of its operands.

## 6. Exact residual responsibility and quantifiers

No additional source guard or dependency counterexample was found. The
remaining owning proof must identify, at the actual result-publication
telescope, the projection of the fixed returned/installed evidence and the
separate description-owned A1 proof, including opaque/private subfields.
It must then apply that classification to all rows added by captured contexts,
not just r. The generic SourceGeneralize rules permit this split; they do
not justify silently splitting a genuinely evaluation-selected dictionary.

The conclusion sought is about **all** legal independent A1_i description
frames, introduced before observations, with one original raw tuple, alpha,
private captures, provider and original xi, and both same-z packets. Aliases
share one frame. EventProof may vary by frame at its original proof scope;
runtime EventFields and Shared/OneShot binders do not. Pending/future fields
keep their original event telescopes and current configurations. The unchanged
joint client W is conjoined and is not presumed satisfiable. One same-old-
denotation copied-instance model would not discharge these quantifiers.

Thus this audit supports the ordinary-constructor separation and excludes the
specific own-component shortcut on the actual captured factory. It does not
close the universal fixed-dependency/copy-applicability gate, original
FIRST-RESULT, native MODEL establishment, soundness/principality or cutover.
Recommended next action: apply the producer's local result-view construction
to the exact ResultBind projections above, then independently review its full
fixed-closure argument and native extra-context-row correspondence together.

## 7. Frozen inputs, checks and resources

SHA-256 of read dependencies:

```text
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240  notes/theory/2026-10-08-source-generalize-definition-and-proof.md
c9207625887d78aaccef988324e8505f6dd08fdfe076e0f564f8b7dca3c54076  notes/design/2026-10-16-source-application-checked-result.md
89fb62b1fe9e10d6972a79f17399d4a0332cf57817bb06a07f5e054ecb4b9dfa  notes/theory/2026-10-16-first-call-checked-result-construction.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a  notes/theory/2026-10-08-call-semantic-input-realization.md
278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98  notes/theory/2026-10-08-call-source-interface-construction.md
b5b2a3176ffb3e5271d2d1150ec0e131752ed881a1eafefd0be40827df593e16  notes/theory/2026-10-16-native-returned-callable-demand-frontier.md
5c23507c218fcaa842f1c4ad844dc942d14b8cff7b09f1fc16df271f2bb290ba  notes/theory/2026-10-16-native-returned-callable-incidence-instance.md
f71cc442bcccb23f7e6f1aa6221b089abb8c24d1c4ce01fecef37995541c16b6  notes/theory/2026-10-16-first-call-joint-forward-preservation.md
79acf8f07fa97b19aa6082d066a78cffc1c0fa3d8072fe0ad6c013066729612a  /tmp/yulang-native-result-captured.yu
2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e  crates/yu-solver/src/candidate_scheme.rs
efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38  crates/yu-solver/src/candidate_source.rs
2158e7377686189ed90d8b8d8803dbb446368abb52b7e0cb24b2282ebe41007c  crates/yu-solver/src/candidate_intrusion.rs
2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b  crates/yu-solver/src/candidate_extrusion.rs
72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6  crates/yu-solver/src/candidate_context.rs
```

Static checks: bounded `rg`/`sed`/`nl` reads and SHA-256 input/artifact hashes.
The independent evidence method is comparison of the accepted source rule
outputs with their actual compiler constructors. It assumes the selected
checked-result definition and accepted local forward theorem; it neither
re-proves them nor uses a transition checker that assumes their rules.
No compiler execution, build, test, executable probe, Git operation, delegation,
or production edit. One leaf, sequential lightweight reads within the assigned
25-minute wall budget; CPU/RAM not measured. No producer unfinished theory
artifact was read. Previous guard-falsifier artifact remains frozen and untouched.
No independent review is claimed. Shared status/theory records are left to the
primary after adjudication.
