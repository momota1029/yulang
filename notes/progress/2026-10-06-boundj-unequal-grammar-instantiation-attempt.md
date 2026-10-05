# Bound_j unequal-grammar instantiation attempt

Status: bounded source-grounded failed instantiation; research only
Review: pending independent review; producer-authored
Implementation authority: none
Assignment baseline: `3335701a198acbc511bec80d99dbf8c4b51cdb5c`
Exclusive lease: this file only
Method: constructive contract instantiation, with a precise missing premise

## 1. Objective and result

Attempt to turn the existing whole-provider `Bound_j(E,u;xi)` contract into
one independently valid common/view pair with unequal abstraction grammars.
The pair must retain the full original tuple, binder scopes, provider incidence,
admission and finite future-use interfaces, and compare the actual designated
common export. The starting evidence is the independently reviewed
[source-pair audit](2026-10-06-all-view-unequal-grammar-source-pair-audit.md).

The attempt supplies a source-grounded **conditional local inclusion**, but no
licensed unequal grammar pair. Source-contract §4 defines a provider predicate
and proves guarantee monotonicity. It does not make that predicate an
exhaustive `Z` or `W` membership alternative, supply abstract-provider admission,
or establish a strictly different observation/history. Source-contract §3.7
expressly leaves the concrete abstraction relations unselected. The attempt
therefore stops at the missing source-formation premise. This is neither an
impossibility claim nor a selection of language semantics.

## 2. Governing evidence and preserved decisions

Directly inspected original clauses:

- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §3.7, lines 300–386: whole-tuple grammar, unchanged correspondence,
  exhaustive alternatives and independent admission/future-use obligations.
- The same source, §4, lines 426–478: complete non-coverage envelope,
  `Bound_j` definition and Lemma 1.
- The same source, lines 665–770: actual submitted roots and local
  resolution-conformance boundary; A-extension; §6.1 constructor table and
  the beginning of §6.2.

The reviewed source-pair audit supplies the retained target and its references
to source-contract §§5.3, 6.3 and 7, coverage/source joins §8, and certified-use
§§5–6. Those original sections were hashed here but not successfully captured
for direct inspection in this lane. No new claim about their contents is based
on an uncaptured read. The extension note's §7 review/integration tail was
directly captured; its grammar derivation is used through the reviewed audit.

Option 2 permits conservative root extras without selecting their primitive
interpretation. Selected Option A retains old source endpoints, provider
constraints, original scopes and one joint assignment. Public guarantee
widening is distinct from changing an abstraction relation. Production is not
identified with a source-reference interpretation; successful concrete Function
comparisons are not composed. No question-board bundle was consumed.

## 3. The constructive step that the source does justify

Fix an original typed provider port `j`, one joint assignment `xi`, its entire
non-coverage envelope `N_j`, and the **same whole provider witness** `u`.
Section 4 requires `N_j` to include the actual role, entry, full challenge and
future-response domain, typed value paths, operation-instance predicates,
continuation/provider relation, routing and shared dependencies. Every
admitted finite interaction and finite future use remains in the contract.

Write `M_j(u,h,q;xi)` only as notation for a genuine guaranteed may-bound point
`q` at a selected output in an admitted finite interaction/history `h` of that
existing provider interface. This introduces no source rule, operation or
membership constructor. The §4 definition has the following logical content:

```text
Bound_j(E,u;xi) iff
  N_j(u;xi) and
  forall admitted finite h and selected guaranteed may-bound q.
    M_j(u,h,q;xi) implies Allow(E,xi,q).
```

This notation retains all the source definition's dependencies; it is not a
projection to observed requests in one execution. A guaranteed may-bound can
conservatively admit a request that an execution never makes.

Let the candidate bounds use the audited §6.3 public-allowance example:

```text
E = Read
A = flat{Read,Write}.
```

These are the existing example's labels, not a newly supplied concrete
operation-instance declaration or provider implementation. By §4's legal
positive-flat interpretation, at the same well-formed joint fiber,

```text
Allow(A,xi,q) = Allow(Read,xi,q) or Allow(Write,xi,q),
therefore Allow(E,xi,q) implies Allow(A,xi,q).
```

Retain `N_j`, `u`, every admitted challenge/history and all incidence. For an
arbitrary guaranteed bound point, its old coverage gives `Allow(E,xi,q)`;
the displayed implication gives `Allow(A,xi,q)`. Universal introduction gives

```text
Bound_j(E,u;xi) implies Bound_j(A,u;xi).
```

This is exactly Lemma 1 under its original scopes, not an independent theorem
about a new source view. It applies only to eligible guarantee upper-bound
occurrences at the provider being compared. A change to capture, challenge
domain, role, future argument interface or an arbitrary child input violates
its hypotheses (§4, lines 445–450). No original `E_out` is reassigned to `A`.

## 4. Why this does not instantiate the unequal-grammar gate

The target grammars, as retained in the reviewed audit, are complete:

```text
H_i = lfp X. G_i and
  (R_i or Z_i or exists x,z. X(x) and W_i(x,y,z)), i = P,V.
```

Here every relation must carry the old whole tuple and original source/provider
correlations. An actual witness must provide independently licensed source
formation and admission, exhaustive membership alternatives, finite local
comparison certificates, and the direct query at `B_common(s,a)`.

The local provider derivation above has no conclusion of any of these forms:

```text
SourceFormsUnequalPair(S,P,V)
CompleteMembershipGrammar(P,R_P,G_P,Z_P,W_P)
CompleteMembershipGrammar(V,R_V,G_V,Z_V,W_V)
IndependentAdmissionAndFutureUse(P,V).
```

No `R`, `Z` or `W` clause is instantiated by this attempt. Section 4 defines
one provider predicate; neither its definition nor Lemma 1 chooses a source
membership arm or a source rule relating a provider witness to the final whole
tuple. Section 3.7, lines 314–331, requires independently interpreted whole-tuple
relations and explicitly says those relations are not selected there. Lines
367–380 additionally require complete accounting and independently supplied
abstract-provider future-use/admission rules. Positivity does not prove them.

The already declared constructor forms in §6.1 provide coverage obligations:
declared requests, bind, call, returned providers, recursive references and
public guarantee views. They retain the original source kernel and do not
declare a new `Bound_j` abstraction alternative. The section expressly calls
its clauses a candidate allowance abstraction. The audited `Read`/`Read,Write`
example consequently supplies an allowance candidate, not an operation/provider
declaration with exhaustive unequal `Z/W` grammars.

**Exact first blocker:** an existing source formation/interpretation judgment
must license this provider predicate as part of both complete common/view
membership grammars, specify the whole-tuple mapping and every alternative,
and retain/certify independent admission and abstract-provider future uses.
Declaring such a placement here would add the very source premise the task
requires deriving. Accordingly no proposed new `Z/W` rule is written.

The actual common-export requirement is also retained. A local inclusion at
`j` is not the direct Function query at the submitted common root. Lines
671–688 require actual membership/admission clauses, finite derivations and
local resolution conformance at those roots. A hidden retained root cannot
replace the designated export.

## 5. The exact strict-difference premise is also absent

Even conditional on a separately licensed placement, Lemma 1 proves inclusion,
not strictness. A provider-level difference would require an independently
admitted whole `u` satisfying precisely:

```text
N_j(u;xi)
forall admitted finite h and guaranteed may-bound q.
  M_j(u,h,q;xi) implies Allow(A,xi,q)
exists admitted finite h and guaranteed may-bound q.
  M_j(u,h,q;xi) and not Allow(E,xi,q).
```

Under the fixed §4 domain these are the missing premises for
`Bound_j(A,u;xi) and not Bound_j(E,u;xi)`. An `A`-covered `Write` point outside
`E` could serve only if its actual operation-instance predicates, provider,
history and all original dependencies are independently supplied. The source
excerpt and reviewed audit do not supply that object. Distinct row labels
alone do not prove a suitable request or provider exists. The fixed `N_j`
may constrain every eligible guaranteed point to `E` even when `A` has extra
support. Exact execution occurrence is neither required nor established by a
may-bound difference.

A provider-level separating point would still need a licensed final tuple
that passes the full guard, admission and future-use contract and is absent
from **all** common-grammar derivations. Other `R/Z/W` alternatives could
already admit it. Thus neither a smallest actual differing observation/history
nor strict complete-membership difference is established. No further search
or algebra-only probe is attempted after the formation blocker.

## 6. Independence, coverage and resource accounting

There is no executable oracle, checker, mutation suite, random seed or numeric
enumeration range. Original source clauses test the proposed inference; the
local derivation and reviewed audit share the same source assumptions. This
note is new producer output and has no independent review. The reviewed audit's
status is not inherited by this note.

Three sequential lightweight command processes were used. The primary
explicitly extended the original two-process limit to three after a capture
failure:

1. `git rev-parse HEAD`, `sha256sum`, policy/audit `cat`, and bounded navigation
   `rg`. HEAD matched the full pinned SHA. The capture truncated the policy
   middle; the reviewed audit and research-lab policy were visible.
2. A single `python3` here-document used only `Path.read_bytes()`/text slicing
   and `hashlib.sha256` to collect source/policy sections. The oversized tool
   output was truncated; subsequent JSON parsing failed before its data was
   retained. It provided no usable additional source evidence.
3. The authorized narrow `python3` here-document captured full
   design-authority/Git-concurrency policies, source-contract lines 300–386,
   415–484 and 665–770, the extension note's §7 tail, and direct dependency
   hashes. That capture completed without truncation, exit code 0.

No tests, builds, probes, parallel commands, Git mutations or delegation ran.
Only this leased file was written via `apply_patch`. First and third command
tool timings were below one second; the failed capture's process timing was not
retained. CPU time, peak memory and total analysis wall time were not measured.
The original process budget was exceeded only under the explicit one-process
extension. No further processes are authorized or needed in this lane.

Omitted scope: exhaustive repository search; full source §5.3/§6.3/§7 and
coverage/certified-use original-section reads; actual source declaration and
execution witnesses; production membership, resolver behavior and all principal
schemes. The source reads justify a bounded failed instantiation, not a global
claim that no suitable primitive exists anywhere. Shared dependencies were not
written. HEAD was checked once; integration-time stability remains primary-owned.

## 7. Frozen dependency snapshot and recommended action

| Dependency | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/progress/2026-10-06-all-view-unequal-grammar-source-pair-audit.md` | `0a11ca0b217916e97e204b611a9a766a15e820e2411cdc1006865466f66f23a8` |
| `notes/progress/2026-10-05-all-view-extension-proof-attempt.md` | `b8bb4c1ad0a65c969c988cb3c685add687ff8db83def2bb7b0f0999e95d6a6e4` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-05-callback-coverage-and-source-joins.md` | `77b7550bdf0a610f0fde4266dcf678d028cf72b8cc6bbb3b1dfaf6a99091cf20` |
| `notes/design/2026-10-04-certified-callback-and-constrained-use.md` | `887bc7c0743d2f34608b46ccb8e5ee9b58ea4a39995b93a5aaced764295bae80` |

Policy/audit hashes common to the first and third captures match. Source and
extension hashes match the reviewed audit's dependency snapshot. No dependency
hash change was observed; this does not replace the primary's frozen integration
recheck.

Recommended next action: return the precise missing exhaustive source
formation/admission contract to the primary. If an existing primitive supplies
it, examine that primitive together with an independently admitted whole-provider
and guaranteed-point witness; otherwise it is a remaining design premise, not
something Lemma 1 or another equivalent finite model can establish.

## Commit packet

- Exact leased path:
  `notes/progress/2026-10-06-boundj-unequal-grammar-instantiation-attempt.md`.
- Baseline SHA: `3335701a198acbc511bec80d99dbf8c4b51cdb5c`.
- Changed dependency hashes: none observed; exact snapshot above.
- Claim/review status: conditional local provider inclusion and bounded failed
  source-pair instantiation; independent review pending; no strict difference,
  impossibility, source-semantics selection or implementation authority.
- Checks already run: one matching read-only HEAD check; policy/audit hashes;
  authorized third-process direct section capture and dependency hashes. The
  second capture failed and is not counted as successful inspection. No build,
  test, probe or Git mutation.
- Proposed one-line research-checkpoint commit message:
  `research: bound Bound_j unequal-grammar instantiation obligations`.
- Shared-record deltas intentionally left for primary/curator: record that
  `Bound_j` grounds the local guarantee leaf but still supplies neither a
  concrete exhaustive unequal abstraction pair nor a strict separating
  provider/history. Preserve the broader all-view gate as open. No task, index,
  authority, theory map or question-board file was changed.
- Writes stop at submission for frozen review.
