# PE decode/new: fresh-root action falsification boundary

Date: 2026-10-10
Pinned baseline: `68ea68fa3b0a73fff05f28c631e9f49be076ebf6`
Status: frozen, unreviewed, non-authoritative research characterization
Gate/method: selected PE §4.2 allocation identity; source-clause attack and conditional impossibility derivation
Exclusive lease: this file only
Production implementation, semantic selection and gate closure: none

## Objective and governing inputs

Determine whether a lawful identity/equivariance counterexample follows from
the **selected** fresh ordinary-root decoder. An allocator invented for this
attack would not answer that question. No executable model is used.

The operative inputs are:

- Native projection selection, `notes/design/2026-10-08-native-projection-public-export-definition.md`
  §§2–4: native formation, actual public allocation and fixed anchors.
- PE, `notes/theory/2026-10-08-projection-public-export-construction.md`
  §§3–3.1,4.1–4.3: public boundary, extraction, actual fresh ordinary root,
  whole-frame action and exact retained fibers. §6.1 supplies the actual-root
  readout/certificate identity check used below.
- Native source Generalize, `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`
  §§3.4,5.2: source `new`/alias, declaration maps, Shared, ViewLogic,
  actual-event routing and EventProof dependencies. Its selected definition
  retains those clauses without selecting a production allocator.
- The previous equivariance pair,
  `notes/progress/2026-10-09-native-projection-interface-equivariance.md`
  §§2–5 and its `-falsification.md` companion: fixed semantic handles are
  explicitly assumed; supplied decoded records are covered; actual fresh
  allocation covariance is excluded. The two-slot external Lookup mutation
  is inadmissible and is not repeated here.
- `notes/progress/2026-10-07-successor-recursive-synthesis.md` §5.1:
  original identities and identity-sensitive external constants are rigid;
  authentic changed-operand laws require separate suppliers.

Accepted meanings remain fixed: the actual raw binding/provider is retained;
one original template and full incident inlet/IF/Delta/certificate telescope
are acted on together; all proof choices and independent VP alternatives
remain; aliases share an incoming frame; actual events have their original
ownership; and Omega is the same full external boundary. No chosen source
meaning is reopened.

**Established inputs:** the selected construction clauses above. **Result of
this note:** bounded falsification characterization, plus the conditional
two-atom theorem below. **Candidate assumptions:** any atom universe,
deterministic chooser, root-store action or fresh-allocation covariance law
introduced below is expressly hypothetical. No independent review of this
note has occurred.

## What the selected operation supplies

PE §4.1 constructs the finite public object at publication and removes source
body/root accessors. PE §4.2 then allocates one new ordinary root `u_i` at a
real source `new`, fixes Omega, and installs its Function head, instantiated
inlet/result, EntryValue dependency, independent admission constructors,
exhaustive production grammar with Echo and ordinary CE slots. PE §4.3
expands the source/public equations on the same complete proof tuple.

These clauses select an actual ordinary root and its meaning. They do not
specify its numerical representation, a deterministic fresh-name chooser,
an atom carrier and permutation action, or a commuting square for running
allocation on transported input states. Conversely, the absence of those
extra laws is not evidence that the selected allocation fails.

The source allocation operation in Generalize §5.2 supplies the following
incidences; it does not substitute for a law of the ordinary-root allocator:

| Item | Identity/ownership retained by the selected clauses |
| --- | --- |
| Real source `new(p,i,r)` | One component frame and `(i,q)` eligible declarations at their original scopes; same actual published binding/provider. |
| Alias of incoming handle i | Same frame, declarations and binders; PE returns the same ordinary root `u_i`. |
| Shared/Established/OneShot/Intrinsic | Original fields or the single original shared binder; initialization is not replayed. |
| ViewLogic | One pre-challenge binder per description frame, shared by every alias/challenge of that frame. |
| EventField | Original actual-event key and telescope; a type instantiation alone is not a fresh runtime invocation. |
| EventProof | Per-frame latent proof witness under the original actual-event telescope; actual runtime operands remain shared where the event is shared. |
| Ordinary root handle | Fresh `u_i` at PE decode, with all actual-root references and certificate checks attached to that record. |
| Omega | Same provider, captures, fixed contracts, intrinsic registrations and original scope/incidence operands. |

Renaming a variable that denotes `u_i` while keeping its value unchanged is
the earlier fixed-handle result. Moving the actual registered handle `u_i`
requires a different action: its root record, every incident reference and
every certificate naming it must move together. Neither changing the source
event identity i nor replacing the provider is licensed by this distinction.

## Smallest useful allocation/alias discriminator

Use one published bare native id and the finite source handle shape

```text
new(p,i,id); alias(i,k); new(p,j,id)
```

Choose equal lawful endpoint images `A_i=A_j=Int`. This is a proposed
source-clause discriminator, not an executed complete compiler program. Its
source legality still requires the original complete local witnesses; no
successful query or allocator is used to manufacture them.

From the selected fresh-root and alias clauses, any decode of this shape
must satisfy

```text
root(k) = root(i) = u_i
root(j) = u_j, with u_j fresh relative to u_i
provider(i) = provider(k) = provider(j) = Omega.provider.
```

Equal endpoint images do not merge the fresh roots or ViewLogic frames. The
alias does not allocate a third frame. No runtime event is introduced by this
shape; later uses of a common actual event would retain that event's actual
fields and their separate frame-indexed EventProof slots.

This uses the smallest handle shape that simultaneously distinguishes two
real fresh allocations from an alias: two `new` operations and one alias.
No global minimum over all source observations is claimed. It does not
reproduce the earlier external-slot mutation or shared-witness satisfiability
countermodel.

Two tempting mutations are already rejected by the selected clauses:
interning `u_i=u_j` because the printed descriptors agree violates freshness;
allocating another root for k violates the alias clause. They are named
contract violations, not lawful counterexamples and not executed mutations.

PE §6.1 gives a sharper identity check. A valid certificate for `u_i` cannot
be submitted at distinct `u_j` merely because their equations agree: the
consumer checks the named actual record. Keeping that certificate unchanged
while moving only the submitted handle is an incomplete action. A candidate
whole-root action must transport the certificate name and ordinary registry
readout together. A client W or opaque operation that reads a moved identity
as fixed data needs its own law or makes that identity rigid. Arbitrary-W
fiber equality in PE §4.3 does not supply this additional law.

## Conditional two-atom obstruction to an overstrong supplier

This derivation discriminates a possible missing-law specification without
inventing a selected allocator. Assume, solely for this theorem:

1. Actual fresh roots are atoms of a sort with at least two fresh atoms u,v.
2. Permitted actions include the transposition tau swapping u,v while fixing
   the complete pre-allocation input X: allocator state, public object,
   endpoint/declaration action, frame identity, Omega and all external inputs.
3. A deterministic function f returns one fresh root from X.
4. Strict equivariance is required as literal equality:
   `f(tau.X) = tau.f(X)`.

Set `u=f(X)` and choose the other fresh atom v. By hypothesis 2, `tau.X=X`.
Determinism gives `f(tau.X)=f(X)=u`; hypothesis 4 gives
`f(tau.X)=tau(u)=v`. Thus u=v, contradicting the distinct fresh atoms.

This is a conditional impossibility theorem for those four hypotheses. It
does **not** refute PE §4.2: PE does not select hypotheses 1–4. For example,
an input retaining an allocation supply need not be fixed by that swap;
a relational fresh allocation can transport one allowed output to another;
or a comparison can use correspondence of output allocations. These are
possible supplier forms, not semantic alternatives adopted by this note.
The theorem rules out demanding that particular strict law for an otherwise
fully symmetric deterministic chooser. It says nothing about the performance
or chosen representation of a real compiler allocator.

## Exact no-counterexample boundary and blocker

At supplied root records and fixed handles, the earlier fixed-fiber lemma
already covers structural checks. At changed actual handles, a bijection
preserves equality and the alias partition, and the displayed equations can
be renamed coherently as a presentation. This algebra does not show that an
authentic allocator or registry realizes that bijection.

No lawful counterexample to the selected decoder was obtained. The precise
missing supplier is an instantiated whole ordinary-root allocation/readout
law: identify the actual handle sort and admissible action at fixed Omega;
state the allocation input/output and freshness support; transport the
installed record and all dependent root/certificate references; preserve and
reflect root retrieval and actual-record matching; and specify how two
allocation results are compared. Every active external identity observer must
be fixed or have its authentic transport law. A law about only printed
descriptor equations does not meet this premise.

This note does not deny the selected fresh root exists. It isolates the
unsupplied operation law needed to compare a moved actual root with another
allocation. It also does not infer that opaque history, admission, Strict,
registry or client operations satisfy that law. The first attempted attack
was the selected new/alias identity partition; the second was strict fresh
choice symmetry. Neither yields a selected legal failure. Another allocator
toy with stipulated transitions would leave the same supplier untouched, so
no third equivalent probe is proposed.

Recommended next action: have the primary obtain one source-grounded
allocation/readout supplier for PE §4.2, explicitly resolving literal output
equality versus an allocation correspondence within the already selected
semantic scope, then review it independently. Keep aggregate equivariance,
CI-use and production correspondence statuses unchanged meanwhile.

## Checks, independence, resources and omissions

Commands used: bounded `cat`/`sed` section reads; `rg` locators in the source,
current task and research seed; `sha256sum` on the seven direct dependencies;
lease-path nonexistence check; the leased note write and final narrow file
integrity/dependency checks. A broad initial task capture was truncated;
operative task/section locators were subsequently read narrowly. This is not
an exhaustive repository or authentic-primitive search.

Oracle independence: there is no executable oracle, checker or differential
evaluation. The identity partition shares the selected PE/source clauses.
The two-atom proof independently derives a contradiction from its explicitly
candidate hypotheses; it proves neither those hypotheses nor the source
transition rules. The producer has not independently reviewed this note.

Coverage: the one finite three-handle shape; the selected seven root entries,
actual-record certificate check and native ownership table; one conditional
two-atom transposition. Seeds/ranges/shards do not apply. Mutations were
logical discriminators only. There were zero executed semantic experiments,
tests, builds, benchmarks, Git commands or heavyweight processes. No timeout
or killed search occurred. CPU, peak RSS and end-to-end wall time were not
instrumented; all commands were lightweight inspection or note writing.

Unverified: existence of a nontrivial authentic changed-root action, the
allocator/readout supplier, production representation/correspondence, opaque
operation laws, arbitrary foreign imports, full source-local witness
construction for the handle shape, general State/recursion and cutover.
Only this leased file was written. Writing stops before frozen review.

## Frozen dependencies and commit packet

Observed dependency SHA-256 at inspection and final freeze:

```text
aed6ef63b01f555a5f2804f87a599167c1a30fa999afc0b9d9f11b8ae974a919  notes/design/2026-10-08-native-projection-public-export-definition.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38  notes/design/2026-10-08-source-generalize-definition.md
4cf84e7a38153b893f1d339780598e2b79084c747ecb883acf0e4fdaa49cf631  notes/theory/2026-10-08-projection-public-export-construction.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240  notes/theory/2026-10-08-source-generalize-definition-and-proof.md
b55fed5b726995c307c12b94bee99c592ed056dc6ac3db192b8a127cfce5e818  notes/progress/2026-10-09-native-projection-interface-equivariance.md
20a79f8c226611ab7de76b333da1714a66909c27b933ac12457392bb3ce517ae  notes/progress/2026-10-09-native-projection-interface-equivariance-falsification.md
e34a568946f5c1946c01828aae34e890747477ee8c272775408438acd95aa43f  notes/progress/2026-10-07-successor-recursive-synthesis.md
```

- Exact leased path: `notes/progress/2026-10-10-pe-decode-new-action-falsification.md`.
- Baseline SHA: `68ea68fa3b0a73fff05f28c631e9f49be076ebf6`, supplied by the primary.
- Changed dependency hashes: none between inspection and freeze. No Git was
  used; primary integration must confirm these bytes against the pinned SHA.
- Claim/review status: frozen unreviewed research characterization and
  conditional impossibility derivation; no selected counterexample, semantic
  promotion, independent review or gate closure.
- Checks already run: governing-rule/section inspection, exact dependency
  hashes, lease-path existence and final note integrity. No tests/builds.
- Proposed commit message: `research: isolate PE decode fresh-root action supplier`.
- Shared-record deltas left for primary/curator: link this supplier boundary
  from the PE equivariance continuation if accepted; retain all aggregate
  statuses; distinguish fresh-root existence from changed-root action laws.
  No index/authority/question-board or production change is proposed.
