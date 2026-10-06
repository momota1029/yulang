# Exact captured-step source: a candidate first-profile producer

Date: 2026-10-06
Baseline: `bab14bf7a740d271e9c27585d4fb9371c1cf0230`
Scope: `my apply f = { my step x = f x; step }`, one resolved Call
Status: compiler-referee and spec-auditor reviewed research proposal; minor scope correction applied by primary
Claim class: constructive candidate, internal inversion theorem, authority-gap audit
Exclusive lease: this file only
Semantic / implementation authority: none

## 1. Objective and result

Supply an actual finite producer instead of another conditional table of
unknown introduction leaves. The producer below has a closed introduction
grammar for this exact source. It constructs a single new original profile
schema at `p0=(beta,call.effect)` and keeps inherited packets separately.
An internal inversion theorem follows by examining its displayed clauses.
It does not identify original source applicability with this output.

The missing bridge is precise: the original implicit formal and exact Call
must use this first-generation grammar, including its decision to generate
no dependent result-profile schema. The approved formation direction does
not establish that assertion. Adoption of the assertion as a durable source
rule requires independent review and approval; this note establishes neither
an incompatible alternative language meaning nor an already necessary new
user decision. The producer is a concrete proposal for the primary to assess.

## 2. Baseline, authority and hypotheses

The [inferred-call-view direction](../design/2026-10-05-inferred-function-call-views.md)
§§1–5 and integrated `function-call-view-formation/q1 a2` fix shared source
formation, stable identity/scope/annotation presence, one original
`xi=(nu,K,D)`, Q-independent admission, the protected provisional Handler
view, and ordinary-value refinement on that same formal/use root. Actual
callable roles and callback-literal B remain fixed. Missing annotation
supplies full protection at applicable positions and no annotation permission;
this is not an empty effect constraint.

The [nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–4 fixes sequential binding, final Name return of `step`, resolution of
inner `f` to the outer formal, and capture of that same formal. Its exact
selected core is:

```text
C = lambda(f,
      bind(step,
        result(lambda(x,
          c = call(result(name f),result(name x)))),
        result(name step)))
```

Conditional machinery is [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§§2–3/10, [typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
§6, and [typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
§6. Their decorated profile/receipt inputs are not a raw-source profile oracle.

Explicit premises for the construction:

- **Hresolve, established selected meaning:** the finite tree above, its
  resolved binder/use identities, original scope tree, and annotation absence.
- **Hseed, bounded established dependency:** the reviewed
  [Call construction](2026-10-06-source-call-generation-construction.md)
  §§3–7 supplies the immediate complete-invocation origin before satisfiability.
- **Htyped, conditional realization:** each used packet edge has an independently
  typed correspondence; imported packets have their own original introduction
  certificates. The producer emits requirements for these, not actual receipts.
- **Hann, unused extension hypothesis:** an annotated occurrence would require
  an independent map from that source occurrence to its governed original
  contribution and typed position. No such map is claimed here; the exact
  source does not invoke this leaf.

The closed grammar in §3 is a **candidate definition**, not a hypothesis that
original source has no extra positions. There is no premise
`Slots_original={p0}`, no `Applicable_original` premise, and no test of Q.

Read research dependencies: the
[formation attempt](2026-10-06-formal-profile-formation-rule-attempt.md) §§3–5,
[normal form](2026-10-06-profile-source-normal-form-construction.md) §§3–6,
[original-introduction attempt](2026-10-06-profile-original-introduction-construction.md)
§§3–6, [extra-origin audit](2026-10-06-profile-extra-origin-falsification.md)
§§3–5, and reviewed
[naturality limit](2026-10-06-profile-substitution-naturality-closure.md) §§3–6.
The observation-quotient artifact was read at separate commit
`f762d7464e3047b8092652aab264842ad646bbe8`, without merging it. Its producer
header still says unreviewed; the assignment supplies its reviewed status.
No result here depends on that status: its grant/expiry calculation is used
only to reject dynamic redundancy as a source-introduction proof.

## 3. The smallest candidate grammar

### 3.1 Outputs and original coordinates

At the original scope, allocate one registry record for `d_f`:

```text
Reg_f = (C,d_f,A_f,R_f,F_c,beta,NoAnnotation,sigma)
beta = (d_f,R_f)
F_c = (parameter, complete-invocation effect, A_c, retained constraints)
```

All coordinates are symbolic. Allocation/reuse follows the resolved binder,
not inferred endpoint equality. `F_c` is one dependent complete Function
variable. The inner `x` has its separate `Value(A_x)` binder record.
Neither record allocates an executing boundary or chooses a provider.

The output is `(Reg,B,T,E)`. `B` contains new first-introduction schemas;
`T` is a source-indexed packet/transport recipe; `E` retains ordinary source
constraints and pending realization obligations. A birth has the form

```text
birth(id, C,n,d_f,R_f,beta,original_position,origin,policy,sigma).
```

An imported packet is `import(i,packet_i,source_certificate_i)`. The source
index and certificate remain distinct even if it has the same static beta
label. Original applicability is an independently intended source relation;
it is not defined by projecting `B` or by the support of `T`.

### 3.2 Constructor clauses

These clauses are the entire proposed grammar for this tree. They are emitted
once per defining source occurrence; Name references point to existing roots.

| Clause | Constructed result |
| --- | --- |
| **ImplicitFormal(d)** | Register the shared Value endpoint and contract/entry references; for `d_f`, record the provisional protected seed on `R_f`. Initialize its birth accumulator to the empty set. Subsequent use clauses extend the accumulator. |
| **Name(u,d)** | Return a reference to d's registered root and its typed view recipe; use the identity correspondence on matching paths. Local birth increment is empty. |
| **Call(c,u_f,u_x)** | Extend the shared `Reg_f` with exactly the birth shown below, the complete Call constraint and pending typed receipt/capture requirements. Combine both argument/callee recipes by their indexed typed edges. |
| **Result(n)** | Preserve n's birth roots and actual returned packet; use the matching result correspondence. Construct no profile birth. |
| **Lambda(d,n,captures)** | Retain body birth roots; keep captured `d_f` by its resolved reference and environment correspondence. The public view recipe does not expose private captured fields. |
| **Bind(d,r,b)** | Register d's RHS provider, retain the ordered suffix and shared rebind witness, and union referenced birth roots without copying their identities. Transport matching packets. |
| **Normalize** | Use the known source Value/Computation tag; retain its existing profile. The administrative `eliminate(reify(c))` references c's outer port and birth. |
| **Import/Transport** | Retain an independent packet with its original certificate; apply the indexed typed image to its paths and D, keeping K and lineage. Allocate no component birth. |

The complete Call birth is:

```text
id0 = (C,c,CompleteFunctionElimination)
p0 = (beta,call.effect)
o0 = ElimOrigin(c,u_f,d_f,R_f,p0,p_out(c))
Call's local B = {birth(id0,C,c,d_f,R_f,beta,p0,o0,FullProtection,sigma)}
Call's annotation permission = None
```

`p_out(c)` is the complete invocation observation position, including actual
entry, body and designated consumer. The origin is the source Function
elimination at c; its interpretation uses pre-dispatch Observe at that port,
not outward row support. Its local output contains no result-root birth or
symbolic result-profile primitive. It imposes no latent shape restriction on
`A_c`. This is a decision in the candidate clause, whose source justification
is assessed in §6; it is not a theorem obtained from the absence of Force.

**Annotation clause.** The absence flag is copied from source and supplies
the FullProtection/None policy for the Call birth. A hypothetical present
annotation would call `AnnMap(a,Reg,xi)` under Hann and emit a source-indexed
annotation contribution/permission schema at its mapped position. A mapping
to an already introduced position updates that position's annotation policy;
a distinct governed position would require its own annotation origin.
For `[io]`, the permission names only the specified io contribution. Actual
removal remains a separate boundary realization, retaining prior evidence.
There is no type-shape scan, automatic subtraction, or guessed mapping to all
descendants. This is an explicit open extension interface, not a completed
annotated-source producer. On this exact source `AnnMap` is never evaluated.

**Role clause.** At the same `R_f`, append
`(ProtectedHandlerSeed,NonHandlerFormal,c,ordinary-Value(x))` from Hseed.
Keep `id0`, source absence and scope unchanged. This emits canonical role
records and obligations; no actual callable's entry/role is rewritten.

## 4. Explicit inversion and exact-tree derivation

**Internal theorem (candidate grammar only).** For any joint fiber and any
finite derivation in §3 on this selected source:

1. Every newly introduced beta birth inverts to the displayed Call clause at
   c, with `id=id0`, `position=p0`, and origin o0.
2. Every transported beta-protection-profile (`chi`) incidence inverts to
   either that birth or an indexed independent imported incidence, with its
   retained original tag. Ordinary predicate (`D`) identity is retained by
   Htyped, but this candidate does not prove a corresponding first-origin
   inversion for `D`.
3. The birth registry has one beta schema; its policy is FullProtection and
   its annotation permission is None, independently of satisfiability.

**Proof.** ImplicitFormal constructs references and the empty accumulator;
Name reuses them. Call is the only row that constructs a birth. Its syntactic
selector is the resolved callee d_f and its conclusion fixes the entire birth
record. There is one such Call in C. No annotation occurrence selects the
open annotation clause. Result, Lambda, Bind and Normalize retain or union
registered references. Inverting a union selects an existing source index;
inverting a typed image supplies the input incidence and its correspondence.
Induction on these finite derivations therefore reaches id0 or the imported
input `chi` certificate. Reference reuse never introduces a second id0. These
cases exhaust **this candidate grammar** by its explicit definition. Hseed
gives the positive Call instance; thus its singleton is nonempty. Q and
interpreted result heads occur in no selector. This proves the three items.

The exact construction order is:

```text
register d_f, d_x                       B_beta = empty
resolve u_f, u_x                        B_beta = empty
emit c's Call birth id0                 B_beta = {id0}
build lambda(x,...) and captured f      B_beta = {id0}
bind step, return name step             B_beta = {id0}
build lambda(f,...)                     B_beta = {id0}
```

This is exhaustive inversion of a specified candidate, not a source proof
by assuming transition rules. It differs from the previous unknown-leaf
interface by supplying actual candidate conclusions for ImplicitFormal and
Call, making the disputed assertion inspectable. Original `Slots(beta)` and
the original witness relation remain uncomputed by an independent rule basis.

## 5. Dependent result profiles and whole-coordinate preservation

This same candidate **excludes a newly generated dependent result schema**
for beta: its formal clause allocates references only, its Call clause allocates
id0 only, and its remaining clauses transport existing facts. A latent choice
of `nu(A_c)` cannot change that grammar. There is no dormant result-root node
whose extension might become nonempty after grafting.

It **allows an inherited dependent result profile** in its packet output:

```text
chi_result = M_actual*chi_actual_result
             union M_signature*chi_signature_result.
```

The second arm can be nonempty only if matching independent original result
information is supplied; it cannot be filled by id0. A packet containing a
same-beta result schema from another certified use/activation is still an
imported witness. It does not amend this component's introduction registry.
If that certificate actually depends on the missing source producer for C,
the arm is an unresolved obligation, not an independent input that closes P.
The actual-result arm likewise retains provider provenance. Thus packet
output is not promised to have singleton support or zero latent profiles.

Under Htyped, `chi'=M*chi`, `D'=M*D`, `K'=K`, and inherited lineage is retained
under the same whole xi. Result projection removes the matching result prefix;
it does not map `call.effect` to `result.latent.effect`. Capture preserves the
same outer registry and requires typed attachment separately. Receipt records
use ownership and creates no birth, permission or dynamic boundary.

Uniform legal graft/freshening acts on the entire original registry, birth,
constraints, imported packets and incidences. It preserves beta/source identity
and evaluates dependent imported schemas under the composed assignment.
The naturality countermodel is therefore compatible with inherited packets;
it cannot add a new birth through this grammar. Conversely, its exclusion
from this candidate proves nothing about its independent source validity.

Appending these canonical syntactic records to a raw tuple has the trivial
erase/lift inverse, modulo coherent fresh naming. This is record uniqueness,
not original-solution or principal-type preservation. Interpreting FullProtection,
Call constraints, source-dependent K,D or admission may restrict tuples.
Before replacing any original producer, one needs original-scope maps that
lift **every** original solution and preserve the whole evidence-rich relation,
including any dependent schemas. No expiry, local grant, empty outward row,
or observation quotient supplies those maps. Full source principality remains
open even if this grammar is eventually approved.

## 6. Can the source direction justify this candidate?

The positive Call origin, stable shared registry, annotation absence policy,
Q independence, and provenance-preserving transport meet the selected
direction locally. The exact ordinary source skeleton also selects no latent
result elimination. These facts support the candidate's positive clauses.

The direction does not entail these two new clause conclusions:

```text
ImplicitFormal produces only a shared registry/seed and references to
component introductions, rather than a dependent original profile schema.

This exact Call introduces the complete-invocation origin only, rather
than an additional original contract schema at its dependent result root.
```

Inferred-call-view §5 asks for the eventual profile producer and uniqueness/
principality proof; it does not select those conclusions. Typed-core §6
fixes the outer interface/consumer and retains a supplied profile. Typed-boundary
§6 takes original Gamma as input. Source-contract §3's exhaustiveness concerns
decorated relation clauses; repurposing it as profile-birth exhaustion would
assume the missing premise.

The exact additional assertion is therefore: **for this original unannotated
formal/Call component, original first-profile introductions are generated by
the clauses of §3, with the specified formal and Call outputs, and every
other original profile-bearing step is an indexed inherited input or one of
the stated preserving steps.** It must include original-witness inversion,
not merely agreement of printed rows or candidate cardinalities. This assertion
is not used as a premise in §4 and is not inferred from that theorem.

No independent original source rule currently supplies a proof or falsifier
for the two disputed conclusions. No source-certified counterexample is
reported. A checker implementing §3 would verify §4's internal consistency,
while assuming precisely the new source assertion if presented as P evidence.
This construction stops at that boundary rather than funding a third probe
that leaves original introduction untouched.

## 7. Checks, resource account and failure conditions

Method: manual construction and finite last-rule inversion on one fixed
resolved source tree, all jointly scoped xi; no finite semantic range claimed.
Commands: bounded `rg`, `cat`, `sed`, read-only `git show`, HEAD/status reads,
and standard-library Python dependency hashing / note metadata checks.
No source/compiler test, build, Oracle execution, executable model, Git
mutation, child delegation, temporary output or production edit was performed.

There is no executable oracle. Independence from Oracle means that no legacy
rule is a semantic premise; it does not mean independent validation. Shared
assumptions are the approved source tree and the supplied typed/decorated
transport basis. Seeds/ranges and process sampling are inapplicable. Conceptual
mutations were examined by clause inspection: adding a result-root birth
invalidates item 1 of §4; making Name allocate a birth invalidates uniqueness;
copying call.effect into a latent result violates the matching-path rule;
filtering formation by Q violates its selectors; discarding an import violates
item 2. No mutation was executed and none certifies source adequacy.

Budget: lightweight bounded reading and one leased note only; no numerical
wall-time/CPU/RAM budget was supplied in the assignment. At most three short
read commands were active together; hashing/checking used one process at a
time, with sequential read-only Git subprocesses. Zero heavyweight processes.
CPU time, peak RSS and total reasoning wall time were not instrumented.
Early combined task/evidence captures were truncated; substantive governing
sections and assigned evidence used later narrow reads. No whole-repository
search or complete shared-task audit is claimed.

Failure conditions: a genuine original formal/result producer not accounted
for by §3 defeats external completeness; an invalid typed map defeats packet
preservation; a non-equivalent role refinement defeats original solutions;
cyclic/infinite first-introduction derivations need an additional proof beyond
the finite grammar. Shape equality cannot repair any of these failures.
Omitted: independent original P/contribution formation, annotated/multi-use/
recursive source completion, actual capture/receipt/receiver realization,
all-world admission, Option A/2 production correspondence, source acceptance,
full soundness/principality and solver lifecycle. No gate is closed.

Recommended next action: independently assess the two disputed clause outputs
against an original source introduction judgment; if they require a new durable
selection, submit this concrete exact-scope assertion for review and approval
before deriving external completeness or implementing it.

## 8. Frozen dependency snapshot

Inputs below are pinned baseline bytes; a separate revision is marked. The
first live hash pass found no changes to the baseline inputs consumed here.

| Input | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `rules/question-board.md` | `8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `questions/2026-10-05-nested-block-function-source-realization/receipt.md` | `e5e59e176eb865a588b2843b18137571fe9c5b6f43bf1ca349bc60c9ad90f0ec` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/progress/2026-10-06-formal-profile-formation-rule-attempt.md` | `8b8b1d49e587835d65c4c6a13a0fc476b07bc58282ac5c58e782b4e5fd5b6a4b` |
| `notes/progress/2026-10-06-profile-source-normal-form-construction.md` | `ea32179888d41ceaddda7ba5c3566e1e83bf489da3fba763a28fda37e8876fad` |
| `notes/progress/2026-10-06-profile-original-introduction-construction.md` | `c5ec22bab3b082de6c460aff3b6775fe9aa0f0624659748e9c5b2feb2d08d8c9` |
| `notes/progress/2026-10-06-profile-extra-origin-falsification.md` | `abbef6d58c5e5691e84ed85fb85038a9805a3a237e19769bdae3dce9da60bf05` |
| `notes/progress/2026-10-06-profile-substitution-naturality-closure.md` | `3c8f99d0456fb2becb57a6429407eb2fc7410ac5e27aaaa5c94cf81843112087` |
| `notes/progress/2026-10-06-profile-completion-observation-quotient.md` at `f762d7464` | `967f4efbf16e023e571d7504b26b50238074714bbb6c81b0740cc9515a6f4b17` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-profile-origin-candidate-rule.md`.
- Baseline SHA: `bab14bf7a740d271e9c27585d4fb9371c1cf0230`.
- Changed dependency hashes: none in consumed pinned bytes; separate upstream
  dependency fixed at `f762d7464e3047b8092652aab264842ad646bbe8` and hash above.
- Review status: compiler-referee/spec-auditor reviewed with no blocking/major
  findings. One minor overbroad quantifier about all transported packet
  incidences was narrowed by the primary to beta-protection-profile (`chi`)
  incidences. Ordinary predicate (`D`) origin inversion and original-source
  closure remain open; research only.
- Checks already run: exact-section reads, baseline/live hash comparison,
  finite clause inversion, note whitespace/newline/link/hash checks. No builds/tests.
- Proposed one-line research-checkpoint commit message:
  `research: specify exact captured-step profile-origin candidate grammar`.
- Shared-record deltas intentionally left for primary/curator: record the
  candidate grammar and its two disputed source outputs; keep original P,
  solution/principality preservation, A and implementation gates open. No
  authority/index/task/question-board edit is proposed as an automatic delta.
