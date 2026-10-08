# Flat Name/Int literal: bounded Return-path falsification

Date: 2026-10-09
Baseline: `d863159d652e36dc4c29fd2baf3e3a3af2078f95`
Status: frozen unreviewed research; bounded elimination and conditional derivation
Exclusive lease: this file only
Method: invert the retained constructor path and eliminate proposed falsifiers
Implementation, historical-family equivalence and gate closure: none

## 1. Objective and result

Find the smallest legal original typed-source witness in the selected
Name/Int literal seam where `Application_N`'s `R_a=Comp(empty,Int)` / Result-N
path differs from the exact literal Return image `J_a`, or fails a named source
consumer premise. Preserve the actual primitive relation, world/provider,
`xi`, result occurrence and consumer port.

No such witness follows from the inspected clauses. The retained Result-N
constructor excludes the obvious behavioral mutations: it returns the same
literal at the same current world. This is a conditional path calculation,
not a completeness theorem about original source typing. The unresolved
consumer seam is an exact dependent origin/signature map; lack of that map
is not a demonstrated negative instance of the consumer predicate.

This lane does not repeat the earlier divergent-carrier/interface discriminator
as a source counterexample. It tests whether that discriminator, an incompatible
receiver, or a changed source tag survives the assigned invariants.

## 2. Governing scope and explicit hypotheses

- Integrated flat-owner q1/d1, approved-answer **Proposed decision and
  authorized scope**, and receipt **Application and remaining scope** select
  the fresh `Application_N` for this bounded owner seam. Exact `J_a`
  realization remains open; historical equivalence and production are excluded.
- Owner completion §§4–5 specify Literal-N, Result-N, ArgDelay-N, Checks-N and
  the `WholeArgCompatible(R_a,CarrierContract(F_c);xi)` occurrence. Section 9
  leaves selected-original consumer realization separate.
- The literal relation-tree audit §§2–4 distinguishes canonical Int and the
  skeleton from the independently supplied primitive contract and attachments.
- Authoritative source result synthesis §1 selects interface preservation for
  function results. It does not independently adopt the entire typed-core
  literal translation. Typed core §§3,6 remains Draft; its literal and
  normalization calculations below are conditional construction rules.
- Authoritative contextual Function membership §3 selects same-value/provider,
  same-world and same-incidence pure Return, plus separately licensed Delay.
  It supplies no general equality between an interface and a source image.
- Call-input construction §§3.1,3.4 supplies the conditional Code-Result and
  the exact `WholeArgCompatible-origin(J_a,CarrierContract(F_c))` consumer.
  Initial-context construction §§4.1,4.3–4.4 imports the primitive and
  independent descriptor kernel. Source generation §5 retains whole image
  checking, one joint assignment and supplied decoration. The flat Code/Call
  instantiation §3.1 explicitly retains both the literal image and interface.
- Direct-Int **Controlling decision and evidence** fixes canonical integer
  meaning. Its withdrawn implementation prescriptions supply no bridge here.

Fix the following hypotheses for the path calculation:

```text
H_lit: actual Integer(a,k), q_a at Value(Int), its entire independent
       primitive contract, scope and witnesses; no replacement interpretation
H_N:   the selected N constructor output, including Result-N's actual o_a
       and ArgDelay-N's actual Reify incidence at this c
H_T:   the Draft typed-core V/X/Normalize equations apply to this compatible
       typed leaf and agree with the selected independent Return kernel
H_joint: one jointly valid xi=(nu,K,D), current configuration/world,
         result/provider incidence and lexical references throughout
```

H_T is explicit, not established by the authoritative function-result choice.
For an **original** Code-Result derivation additionally require the independently
typed literal Data leaf and its original result-origin interpretation. N
formation alone does not supply that interpretation into a fixed foreign
consumer. Original Code-Call additionally needs its genuine argument origin.

## 3. Conditional path derivation and minimal premise frame

Under H_lit/H_N/H_T/H_joint, constructor inversion gives:

```text
I_a = Value(Int)                 d_a = literal(a,k)
R_a = Result(I_a) = Comp(empty,Int)
n_a = Normalize(I_a,d_a) = result(d_a)
V[d_a] = k                      X[n_a] = Return(k)
t_a = Delay(X[n_a],same references)
    = Delay(Return(k),same references)
```

The equation for `X[n_a]` retains the actual result occurrence `o_a` and
current joint world, rather than constructing an unindexed Return elsewhere.
Contextual membership §3 prohibits changing its value/provider, world or
result incidence. The primitive witnesses remain those of H_lit; no canonical
replacement witness is chosen. ArgDelay-N adds inert formation at the actual
argument port, and executes no prefix.

Consequently, **conditional path theorem**: a competing path obtained from
these same clauses, same leaf and same indices has the same Return constructor
image. A behavioral separator at this child would require a different supplied
primitive/Return interpretation, an extra consumer, changed incidence/world,
or failure of H_T. This does not prove `J_a=R_a`: the left side is a source
constructor image, the right side its computation interface.

The smallest consumer-premise frame is:

```text
c = Application(Name(u_f),Integer(a,1))
u_f resolves to the same immutable ordinary Value formal d_f
q_a -- Result-N at o_a --> n_a -- ArgDelay-N at r_arg --> t_a
Checks-N at check_a emits WholeArgCompatible(R_a,CarrierContract(F_c);xi)
original Code-Call asks for
  WholeArgCompatible-origin(J_a,CarrierContract(F_c)) at that same c/xi
```

Its raw illustration is the inner `f 1` of `my apply f = f 1`. This is a
minimal premise frame, **not an exhibited original typed-source falsifier**:
the authentic original argument-origin and independent kernel signature are
exactly what this calculation lacks. Removing the Call loses the consumer
question; removing its literal or formal Name leaves the assigned seam. The
integer spelling `1` is sufficient; no value-dependent branch is used.

## 4. Elimination attempts and exact blocker

| Proposed attack | Why it yields no legal falsifier here |
| --- | --- |
| Replace `Delay(Return(1))` with a divergent pure Int carrier | Preserves a printed interface but changes the actual operand/source image. Result-N inversion yields the retained Return, not that replacement. This already known interface discriminator is excluded by the lease's fixed-source requirement. |
| Change literal value, provider/world, xi or result port | Violates an assigned invariant or selected pure Return retention. A different legal literal occurrence is a different frame, not a mismatch at the fixed occurrence. |
| Switch Value(Int) to retained Computation(empty,Int), or force a latent value | Changes the actual source tag or adds a consumer. Empty effects do not authorize this change. |
| Supply a callable whose inlet excludes this integer | An unsatisfied independent argument obligation can make the interpreted N fiber empty. Installation explicitly allows that. Without a satisfying original typed-source certificate this is a rejected candidate assignment, not an accepted-source divergence. |
| Omit the literal Data or original argument origin when invoking Theorem S / Code-Call | Shows an unavailable derivation premise, not that an actual origin cannot exist. The displayed Theorem S Data list alone lacks Literal; the imported compatible leaf remains required. |

The precise blocker after these eliminations is **H_arg_origin**:

```text
an independently declared WholeArgCompatible signature and a typed map
from the installed N argument-check occurrence at
  (c,a,q_a,o_a,r_arg,check_a,R_a,F_c,scope,xi)
to the original required origin at
  (same c,a,q_a,o_a,r_arg,check_a,J_a,CarrierContract(F_c),scope,xi),
preserving whole primitive/kernel witnesses, world/provider dependencies,
licenses, source tags and future-use evidence.
```

The inspected initial-context §4.4 names a complete independent proposition;
the original Code-Call retains the exact image-origin. Neither gives this
dependent conversion. Two possible signature shapes remain **candidate
assumptions**, not selected conclusions: the kernel may be indexed by a whole
source object that contains both image and interface, or it may require an
explicit lawful realization/transport between distinct indices. This lane
selects neither. Equality of printed `Comp(empty,Int)` expressions cannot
settle the question. Conversely, the differing written arguments `J_a` and
`R_a` alone prove no semantic disagreement.

This is a bounded characterization of inspected suppliers. There is no claim
that H_arg_origin is impossible, absent repository-wide, or a new language
decision. Another checker assuming either signature would leave this premise
untouched. The next useful method is an owning-kernel/source-origin artifact
bridge, rather than a third transition probe.

## 5. Independence, coverage, checks and resources

No executable checker or external oracle ran. The two constructor presentations
share the literal interpretation, Return kernel, source tags and joint indices;
their agreement cannot independently prove those rules. The elimination table
is documentary analysis of named mutations, not executed mutation coverage.
No finite model enumeration, random seed/range, numeric literal range or trace
sample was used. The calculation is symbolic in k under H_lit, rather than an
exhaustive validation of integer primitives.

Coverage: one direct formal Name/Int constructor and the operand-to-argument
origin seam; exact cited clauses. Arbitrary source elaboration, original
membership inventory, actual runtime admission, effects, mutable State,
complete Call arms, solver/export/principality and production are unverified.
Initial combined captures truncated; the relied-on governing clauses were
reread in bounded slices. The earlier locator included nonexistent `spec/`
and returned exit 2; no absence claim relies on it. No repository-wide search
was completed.

Checks: sequential scoped `rg`/`sed`/`cat` reads; `git rev-parse HEAD`;
Python byte/SHA-256 comparison against the pinned baseline for 18 governing
dependencies; exact approved-draft inclusion in the finalized answer;
final output whitespace, lease and dependency recheck. These are artifact
checks, not compiler tests or independent review. No build, test, formatter,
Git mutation, child agent, generated log or extra output path was used.

Resources: one research producer, zero heavyweight processes, lightweight
document/hash commands only. No numerical process/CPU/RAM/wall ceiling was
supplied. Aggregate CPU, peak RSS and reasoning wall time are uninstrumented.
The bounded lane stopped after the path and consumer-origin eliminations.

Recommended next action: request the exact WholeArgCompatible kernel signature
and retained source-origin conversion from its construction owner for this
single installed literal occurrence; independently review that map.

## 6. Frozen dependency and commit packet

All 18 checked governing dependencies equal baseline bytes; none changed.
The approved proposal SHA-256 remains
`61d5fd8e3a359c9ad7fce203ee7927553964b4eeae4a923319aca49a846f826a`.
The approved answer SHA-256 remains
`ab2ffb1cd14b023d7159f98f05df480d30772091a77b4079750932e76cab17e2`.
The literal audit SHA-256 is
`500dfc3cd41501945f9983119da8c404e747b464b121c27b019108f0ec70c091`.
Primary integration must recheck the relevant dependency snapshot.

- Exact leased changed path: `notes/progress/2026-10-09-flat-application-literal-return-falsification.md`.
- Baseline SHA: `d863159d652e36dc4c29fd2baf3e3a3af2078f95`.
- Changed dependency hashes: none; no shared dependency was edited.
- Claim/review status: unreviewed bounded elimination and conditional path
  derivation; no legal counterexample found, no gate promotion; producer checks
  are not independent review.
- Checks already run: scoped clause reads, baseline/dependency byte and hash
  equality, exact approved-draft inclusion, output scope/whitespace checks;
  no tests/builds/probes.
- Proposed research-checkpoint message: `research: bound flat literal Return falsification at consumer origin`.
- Shared-record deltas intentionally left for primary/curator: record that the
  fixed retained Result-N path yields no legal behavioral falsifier under its
  explicit kernel premises; retain H_arg_origin as the exact open consumer
  seam; do not equate image/interface, claim original impossibility, or promote
  admission/CallInitial/production gates. No shared record is written here.

Writes stop before submission for frozen review.
