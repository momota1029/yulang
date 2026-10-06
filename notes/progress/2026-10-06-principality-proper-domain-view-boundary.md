# Proper-domain Function views and the A-allocation boundary

Date: 2026-10-06
Status: bounded conditional discriminator; independently compiler-referee-reviewed
(no findings); research-only
Baseline: `2d378d0cf84b110e034d792d680f94b9369ad90d`
Implementation authority: none

## Question and result

Does the restricted A-allocation certificate establish every sound Function
view, including one that accepts a strict subset of the source callable's
input domain? Under the hypotheses below, no: a narrower target input domain
can be sound while failing the exact-domain premise required by `V_alloc(S)`.
This excludes the shortcut that every independently valid view belongs to the
displayed A-allocation class. It does not refute A-allocation, unrestricted
principality, or every other possible direct-query proof.

The governing `source-contracts` §6.3 restricts `V_alloc(S)` to views whose
non-coverage kernel and value interfaces match the original after the allowed
uniform grafts, and whose local coverage certificate entails coverage of each
selected contributor and the original outer endpoint. Section 5.3's displayed
allocation certificate requires equality of the complete common and target
challenge domains. Typed-core §7 allows domain inclusion for validity, while
§9 requires preserving complete invocation observations. These are different
obligations: inclusion may suffice for a checked target view even where the
restricted allocation certificate's equality cannot hold.

## Conditional derivation

Fix an annotated constant function source:

```text
our k(x:A) = 42
```

Assume it has an independently licensed, complete original interface and
common source export. Fix one original source solution `s`, common allowance
witness `a`, and joint `xi`. For every selected provider `j`, retain the same
whole provider operand `u_j(s,h)` at its original scope and non-coverage
envelope, and assume the existing coverage certificates
`Cov(E_j(s),a)`. Same-provider Absorb then yields
`D_common(s,a,h)=D_A(s,h)` under the common formation equations. Let `h` be a
fixed surrounding history and `D_A(s,h)` the source's admitted Value-entry
challenge domain there. Now suppose an independently source-licensed
same-value relation gives a complete target input view `B` with

```text
D_B(s,h) ⊊ D_A(s,h)
```

and preserves actual entry, effect/profile, histories, scope and original
joint `xi=(nu,K,D)`. Assume every challenge admitted by `D_B(s,h)` preserves the
complete original invocation observations and the source satisfies the
target's unchanged output/result obligations. Typed-core §7's Function
inclusion rule then permits the narrower target input contract on this fixed
solution/fiber/history: the target caller can supply only carriers in
`D_B(s,h)`, and each such carrier remains in the actual source domain
`D_A(s,h)`.

But §6.3's `V_alloc(S)` certificate requires equality of the complete
common and target challenge domains at the fixed scope/fiber. The supplied
coverage premises and same-provider Absorb identify the common domain with
`D_A(s,h)`; strict subset makes that equality false.
Changing only the allocation allowance cannot prove equality of the domains.
Thus this target has no certificate by the *displayed A-allocation route*.
Another ordinary comparison or a broader principality proof may still cover
it. In the Record candidate below, §6.3's unchanged value-interface condition
already excludes the view from `V_alloc(S)` independently. The strict-domain
calculation is an additional failed certificate premise, not a claim that
domain equality is the only reason that concrete view is outside the class.

One small finite structural candidate, if source contracts license the record
inclusion, is:

```text
A = {a:Int}
B = {a:Int, b:Int}
source: our k(x:A) = 42
target: B -> Int
```

A pure returned carrier `{a=0}` distinguishes these record domains: it is
admitted by `A` and lacks required field `b`; `{a=0,b=0}` is admitted by both. The witness
uses one parameter, one literal result and one additional required field. It
is a conditional decorated-source witness, not an accepted-program
counterexample.

## Exact unresolved premise and limits

The key source premise is that mandatory Record width is licensed as
same-value inclusion over the *complete* Value-entry challenge domain for this
annotated source, with all invocation, scope, effect and joint-`xi` conditions
preserved. Structural FMP establishes a mathematical Record order, not this
source interpretation. The cited source contracts do not themselves establish
that the concrete checker admits this candidate conversion. Therefore the
record inclusion is an explicit unresolved premise.

No claim is made that source annotations may be widened, that this code
currently accepts the target, or that a smaller source-domain certificate
must be preserved by every admitted source rule. A later proof may show that
the source gate forbids this case, or may prove a different allocation/query
route. The result only separates semantic validity under supplied complete
domain inclusion from the narrower equality-based certificate class.

Method: bounded conditional calculation from source-contracts §§5.1, 5.3,
6.3–7, typed-computation-core §§7 and 9, result-synthesis §§2 and 4, and
structural FMP §2. Frozen Oracle was not consulted. No builds, tests, runtime
probes, enumeration, or performance measurements were run. Claim remains
conditional and research-only despite independent review; the source-licensing
premise and any implementation acceptance remain unverified.
