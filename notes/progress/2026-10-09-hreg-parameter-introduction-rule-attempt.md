# Hreg: forward Parameter introduction rule application

Date: 2026-10-09
Baseline supplied by primary: `8738f5b084f01c00efa913bb7f591c124821c03c`
Branch supplied by primary: `research/simple-sub-intrusion`
Status: frozen, non-authoritative research; blocked local rule application
Review: independent compiler-referee and spec-auditor review found no
actionable findings; no tests/builds run
Exclusive write lease: this file only
Hreg closure, language selection and implementation authority: none

## Objective and method

Attempt the actual Parameter source introduction for one unannotated formal
in `my id x=x`, starting from a complete authentic caller shape. The method
is **forward typed rule application**: account for the source binder, then
try to form its legal scope extension, local registration, ordered operands
and guards before invoking UV and contextual SIG packaging.

The application stops at the first scope-formation input. There is no
completed Parameter introduction, Desc certificate or inlet certificate.
The result is a bounded failed application with an exact required producer,
not a new proof that the selected source rules are insufficient in every
model. The prior two artifacts already leave this premise open; this attempt
does not count another reformulation as gate progress.

## Baseline, authority and dependencies

| Source | Exact governing use |
| --- | --- |
| `rules/design-authority.md` | Authority order; local completion cannot silently change selected meanings; proof-obligation economy. |
| [SG](../theory/2026-10-08-source-generalize-definition-and-proof.md) §2 L1–L5, §§3.1,3.3 | Parameter owns an ordinary flexible value declaration at its original scope; genuine local introduction laws and evidence remain premises. |
| [UV](../theory/2026-10-08-uniform-value-entry-constructor.md) §4.1 | Actual Parameter formation emits Desc, Intrinsic, the finite inlet schema and its Description edge; already introduced incident operands and a pre-challenge scope are required. §4.2 is read only to distinguish this schema from a later checked-inlet witness. |
| [Native Signature](../design/2026-10-08-native-signature-formation-definition.md) §§1–2 | Actual registered graph and original typed ports; independent local typing remains input. |
| [SIG](../theory/2026-10-08-source-signature-incidence-construction.md) §§2,3.1–3.4 | Exact registered inputs; full dependent injections; local source introductions supply LocalOrigin/Op, while Scope/Rename and root insertion preserve origins. |
| [Approved native projection](../design/2026-10-08-native-projection-public-export-definition.md) §§2–4 | Parameter precedes fixed generic raw closure; preserve complete static/observation checks and all original scopes. |
| [Source-owned attempt](2026-10-09-hreg-source-owned-constructor-attempt.md) and [local schema attempt](2026-10-09-hreg-local-scope-port-schema-attempt.md) | Frozen prior owner cut and rejected circular suppliers; neither supplies a Parameter-local introduction application. |
| [Authentic schema manifest](2026-10-09-id-parameter-authentic-schema-manifest.md) | Accepted caller ownership and unresolved original Parameter predecessors; no concrete caller record is supplied. |

The primary's accepted caller ownership decision is retained: the caller
supplies initial JointWF with all original scopes, evidence and dependencies.
It does not supply an extension rule for a fresh source formal. No pending
literal question was read. `tasks/current.md` and `tasks/research-lab.md`
were read for operational context; the design index was used as a locator.
Their mutable summaries are not premises of this application.

## One caller shape and exact source binder

Grant the following **particular authentic inputs**, without synthesizing
an empty context or claiming their concrete values were supplied:

```text
E0, T0, P0, h0 : caller context, original binder tree,
                complete ordered caller predecessor tuple,
                complete authentic JointWF(E0)
b0            : proposed definition insertion position in T0
sd, sell, sx, sn : actual resolved definition, Lambda, formal, body Name
resolve(sn) = sx
outer_annotation(sx) = absent
```

`P0` means the actual caller tuple, with every field type and its dependency
on preceding fields. No arity, sort or emptiness is selected. A position
`b0` is a locator; granting the locator does not grant permission to extend
the semantic binder tree there. This is one fixed caller shape, universally
parameterized by its authentic records, not an exhibited inhabitant.

The exact source binder is `sx`, the formal of `sell` in `sd`.
`sn` resolves to that formal. These are authentic resolved occurrences by
hypothesis. They justify the lexical ownership and annotation classification.
They do not yet inhabit SIG's actual local **formation record**, which
includes original scope and registration. In particular, `q` below names
the Parameter-introduction output corresponding to `sx`; it is not a
fresh numeric identifier already certified as that output.

SG §3.1 selects Value entry for this unannotated formal and an ordinary
flexible ValueEndpoint. This classification does not perform a separate
scope or port introduction. No split phase is selected by treating the
classification as a partial executable Parameter rule.

## Forward application: first failed input

Try to apply UV §4.1 at `sx`. The first typed work is establishing where
its original declaration can be introduced. The required certificate must
identify an actual legal extension of `T0` at `b0`, preserving all old
binders/dependencies and assigning the formal its original type-scope
`sigma_a` before the Lambda's independent challenge subtree.

This description names the required output, **not a defined judgment or
candidate guard**. The governing inputs do not give the domain/codomain,
operand order or introduction premises of the local extension judgment.
The attempted first inference therefore has this unresolved rule slot:

```text
complete authentic (E0,T0,P0,h0)
actual sd/sell/sx/sn with resolve(sn)=sx and annotation absence
actual proposed insertion position b0
---------------------------------------------------------------- ?
legal original source-binder extension at b0 for Parameter sx
with original sigma_a and unchanged ordered old predecessor incidence
```

The conclusion cannot be obtained by projection from `h0`: its new
scope/incidence mentions `sx`'s local introduction, whereas `h0`
certifies the existing context. Nor does lexical parenthood determine the
type-binder tree or prove its legal extension. L4 supplies genuine original
introduction evidence **when available**; naming L4 does not instantiate
this missing local rule. L1–L3 and L5 do not supply that application either.

Thus the exact first missing input is the **actual source-binder/scope
introduction law, and its application at this caller insertion site,
which produces Parameter's original legal typing scope with its complete
ordered predecessor incidence**. It is not a failed test of one known
guard atom. No atom can be named before that rule's telescope is known.
If the rule instead introduces the definition/component and the formal
jointly, its actual joint premise list is needed; this note does not select
a separate extension phase.

Stop here. No prospective port or guard is asserted inhabited. The later
input inventory below records what a completed owning rule must account
for; it is not another attempted derivation or a manufactured rule.

## Inputs beyond the stop, and conditional UV/SIG consequences

| Required local account | What an independent completion must supply |
| --- | --- |
| Source registration | Actual definition/component registration and the formal's owning introduction, tied to sd/sell/sx and the same original tree. No root/component identity is certified by naming it. |
| Scope and free dependencies | The legal sigma_a above; complete ordered Delta_a for Desc; complete already introduced inlet Delta. Their equality, subset relation, arity and emptiness are unselected. |
| Port/root formation | The genuine Parameter rule's introduction of the designated one-layer port, original source slot and receipt/receiver/formal paths, and their registry/root incidence. UV assigns this emission to Parameter; these outputs are not moved to a prior reservation rule. |
| Guard derivations | Every original formation/registry/scope/incidence and applicable local license proof at its actual dependent tuple. Typed support is not a proof that a contribution fiber is inhabited. Future event predicates remain under their events. |

**Conditional continuation, not a discharged theorem.** If an independently
justified Parameter-local rule application supplies those actual formation
inputs at this same source binder, UV §4.1 gives

```text
Desc(C,q,ValueEndpoint,sigma_a,Delta_a): a
Intrinsic(q, actual slot, Value-entry, designated one-layer port,
          original receipt/receiver/formal paths, annotation absence)
I_schema = ValueInletSchema(q,a;Delta)
Description(C,q) -> I_schema and its incident original constraints
```

The conditional premise is a local introduction application with its full
original rule inputs. It is not a completed U_g, an anchor, successful Q,
own-root membership, Generalize or a desired public export. The present
attempt has not supplied the premise, so none of the displayed certificates
is an actual emitted artifact here.

Once that owning application exists, SIG §3.4 can use its formation record
in `LocalOrigin(intro_q,k)` for genuinely introduced fields. If a local
contribution constructor is applicable, its `Op` retains the independent
typing and original license fields; no applicability is inferred just from
Parameter's support port. SIG §3.2 then inserts the complete typed telescope
at the actual operand/root occurrence and retains every original index.
These steps cannot backfill the missing scope law: Scope/Rename needs its
antecedent binder/substitution, and root insertion receives the antecedent
introduction. No pre-Parameter use of those constructors creates it.

There is also no actual UV §4.2 checked-inlet `gamma` here. That separate
certificate requires an independently typed argument and its complete
contract/current guards. The requested pre-challenge certificate is the
Parameter-owned schema and its incidence, not an argument-specific
admission witness.

## Claim class, independence, omitted cases and decision readiness

Established: the selected rule outputs and the conditional location of SIG
packaging, within these exact document sections. Bounded characterization:
this forward application cannot fill its first scope-introduction rule
slot from the supplied authentic caller/resolver shape. Candidate assumptions:
the particular caller/resolver inputs above; no concrete records are
exhibited. Conditional conclusion: UV/SIG consequences after an independently
justified owning rule application. No new theorem, counterexample, successful
application, guard law or Hreg closure is established.

No oracle or executable checker was used. The trace shares SG/UV/SIG's
selected local laws with the preceding research. Its separation of source
records from typed formation evidence is documentary; it is not independent
semantic validation. A checker assuming the missing extension/port transitions
would check their consequences only. No seeds/ranges, mutations, search
enumeration or reduced counterexample apply. No broad absence claim follows.

Failure conditions include supplying a fresh q as a formation record;
guessing sigma_a from lexical depth; setting Delta_a or Delta to empty;
flattening an ordered dependent telescope; emitting Parameter's port evidence
before its owning application; deriving new guards from h0; using declared
support as a license; selecting a later anchor/own-root certificate as the
first introduction leaf; or creating an arbitrary scope predicate in place
of the missing rule.

Unverified: concrete caller and source records, the local rule's complete
scope/registration/port/telescope/guard inputs, one actual Desc/inlet image,
later argument checks, all anchors, invocation/publication, State, recursion,
imports, foreign kernels and production/cutover correspondence.

**User decision readiness: no concrete semantic choice is ready.** The stop
identifies an owning construction law, without a contradiction between
selected meanings or evaluated alternatives. The primary can first obtain
one authentic local rule with its actual application. If completing that
rule exposes alternative observable behavior or changes the Authoritative
contract, that concrete delta requires normal design adjudication/approval.
This artifact grants neither a new definition nor implementation authority.

Recommended next action: obtain the owning source-binder/scope introduction
rule and one application at the fixed caller insertion site, retaining the
full predecessor tuple. Until that input exists, retire equivalent
Parameter packaging probes rather than run a fourth assumed-rule variant.

## Checks, resource accounting and freeze

Commands: scoped `cat`, `sed` and `rg` reads; a single-process Python
SHA-256 snapshot and leased-target existence check; a narrow final
dependency/link/fence/whitespace check. No Git commands, builds, tests,
formatters, measurements, children or question files. Only this leased note
was written. The full baseline is primary-supplied; baseline-byte validation
against Git remains with the primary.

No numeric CPU/RAM/wall-time budget was supplied. Commands were lightweight
bounded document operations; independent reads were batched. CPU/RSS and total
wall time are unmeasured. No heavyweight or search process ran. The note is
frozen at submission, and producer writes stop before review.

| Direct dependency | SHA-256 at freeze |
| --- | --- |
| `rules/research-lab.md` | `5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6` |
| `rules/design-authority.md` | `925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-10-08-native-projection-public-export-definition.md` | `aed6ef63b01f555a5f2804f87a599167c1a30fa999afc0b9d9f11b8ae974a919` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/theory/2026-10-08-uniform-value-entry-constructor.md` | `273e8dae447e9997d586fc07abf48883c76b90988c8906094dd428a48339c2e5` |
| `notes/design/2026-10-08-native-signature-formation-definition.md` | `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9` |
| `notes/theory/2026-10-08-source-signature-incidence-construction.md` | `7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a` |
| `notes/progress/2026-10-09-hreg-source-owned-constructor-attempt.md` | `a245b67b0f48d782191ea3367fcdc8b8b9f87f06620df597a8f37871758792cc` |
| `notes/progress/2026-10-09-hreg-local-scope-port-schema-attempt.md` | `5c016112447085d4c20792427955a9b99720245a2fe6117eef0c34277b688d39` |
| `notes/progress/2026-10-09-id-parameter-authentic-schema-manifest.md` | `269a38ed7a15e26f508b2ff96f4307cdd98ef13c43a15d1b2b6d4ccd85f3a860` |

Dependency hashes are stable between the opening snapshot and freeze;
equality to the pinned Git revision is not claimed. The prior reviewed local
schema note's current hash includes its frozen review header.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-09-hreg-parameter-introduction-rule-attempt.md`.
- Baseline SHA: `8738f5b084f01c00efa913bb7f591c124821c03c`.
- Changed dependency hashes: none during this attempt; primary must validate
  baseline bytes before integration.
- Review status: frozen producer, non-authoritative failed rule application;
  independent review pending. No gate promotion.
- Checks already run: bounded exact-section reads, dependency SHA-256 stability,
  leased output existence and final local link/fence/whitespace checks.
  No tests/builds/experiments/Git commands.
- Proposed research-checkpoint message:
  `research: stop Parameter introduction at original scope formation input`.
- Shared-record deltas intentionally left for primary/curator: retain open
  Hreg; record the first actual scope-introduction application input and that
  no semantic alternative is ready for user selection. No task/index/theory,
  authority, question-board, implementation or production status edits.
