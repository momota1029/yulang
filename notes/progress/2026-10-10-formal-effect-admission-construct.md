# Formal effects: constructive admission reduction

Date: 2026-10-10
Status: frozen producer research; unreviewed, no production authority or gate closure
Baseline: `e3ddf9f19e08be74a8467a61b5415244f6f5ac0f`
Branch assigned: `research/simple-sub-intrusion`
Oracle source: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this note only
Method: pinned-source inspection and bounded hand derivation; no executable probe

## Objective and governing dependencies

Derive finite contextual admission for the Function-only annotation envelope,
or isolate the source premise needed by an exact observer. Governing authority
is `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1,4–5:
composed polarity, function-local concrete subtraction, connected symbolic
variables, authentic boundary identity, and natural Simple-sub inference.
No source restriction or semantic count cap is proposed.

Inputs at the pinned baseline are the paired Function construction gate,
explicit-effect termination source map, mixed-debt observer results,
correlated mixed replay discriminator, and formal filter transition contract,
all dated 2026-10-10. Their claims and exclusions remain distinct. In particular,
the independently reviewed observer covers debt recursion and finite mixed
consumers; it does not cover recurrent consumers adding unbounded PUSH mass.

During this assignment the primary supplied a later accepted correction:
the unexecuted callback acceptance target is
`(int -> ['b, io] 'c) -> int -> ['b] 'c`. The pinned notes' version without
the returned `int ->` is a mistaken transcription. None of the derivations
below uses either scheme as a premise.

## 1. Established source fact: the admitted formal envelope has one context

At the pinned successor, the carrier is precisely Int, Unit, named Value
variables, and Function (`yu-hir/src/module/source_annotation.rs:74–94`).
`candidate_source.rs:77–81` recursively requires `ty.effects.is_none()` for
formal annotations. `candidate_effect.rs:845–864` independently rejects
`ty.effects.is_some()` before constructing a pair. The Function branch allocates
two ordinary Effect rows and uses shared positive/negative coordinates; named
Value variables allocate ordinary Value rows at `:787–809`.

**Local theorem.** Fix a finite endpoint/attachment snapshot, with endpoint sets
of cardinalities V and E. Restrict to the existing paired formal constructor,
ordinary row insertion/replay, and ordinary Function comparisons, without any
new weighted constructor. Every contextual task has identity context. Its
context-qualified semantic task space therefore has at most `V² + E²` members.

Proof: the constructor introduces no weight or attachment. Bounds retain only
typed endpoints (`candidate_extrusion.rs:358–492`); their joins enqueue typed
endpoint pairs (`:589–637`). The four Function children are endpoint pairs
(`lib.rs:11903–11937`). Induction over those transitions preserves identity.
Identity under replay, variance swap, coordinate renaming, and same-kind row
identification remains identity. This is also visible in the current
`TypedPairKey` representation (`lib.rs:767–778`). With a fixed generation and
each pair processed once, semantic pair saturation is finite.

This is an exact statement about context cardinality and a fixed snapshot,
not a fresh proof of total compiler termination. Endpoint allocation,
generation reopening, diagnostic replay, and resource rejection have their
existing separate owners. Above all, refusal of explicit rows cannot establish
termination of the next constructor that admits them.

## 2. Conditional constructive extension: several debt IDs, one joint image

This extends the reviewed one-ID debt observer by product construction. It is
a new conditional derivation, not an independently reviewed result.

Hypotheses:

1. There is a finite retained derivation grammar G and a finite set I of
   authentic attachment instances. Every recursive grammar value is debt-only:
   `n_i = 0` for each i. Productions use the inspected bracketed replay, swap,
   both-from-right, debt prefix/suffix, independent choices, or explicit sharing.
2. The query is a fixed finite bracketed continuation C. Its expanded finite
   syntax has B_i PUSH occurrences for ID i, counting copied syntactic uses.
   PUSH family identity is consistent for each ID. Families/filters and
   authority references used by this query have finite exact representations.
3. Observations are the reviewed local ones: exact active counts, directed
   entries/pending debt, identity, and specified finite-family local
   filter/residual observations. No residual-gamma allocation or public support
   projection is inferred from those observations.

Define a joint image, without taking independent coordinate projections:

```text
q_C(W) = tuple_i (min(p_i,B_i+1), min(r_i,B_i+1)).
number of joint debt states <= product_i (B_i+2)^2.
```

For each ID, debt replay adds coordinates and branches only on zero; swap
exchanges coordinates, and both-from-right copies right debt. Clipped addition
satisfies `min(a+b,T)=min(min(a,T)+min(b,T),T)`. Zero is preserved. These facts
prove that q_C commutes with every debt operation, coordinate by coordinate.
The source mix early return when a whole side is empty causes no exception:
an ID absent from that side has zero coordinate, and its unchanged result is
also its per-ID mixed result. Finite filters are retained exactly as additional
state, not clipped into counts.

Saturate sets of **joint tuples** per nonterminal, preserving explicit shared
choices. Each update adds a previously absent tuple. Induction on finite
derivation height proves soundness; induction on the saturation additions
supplies a finite derivation witness, proving completeness. Thus saturation
terminates after at most `|NT| * product_i (B_i+2)^2` successful debt-state
additions, before finite exact filter/reference factors. Taking separate sets
per ID and their Cartesian product would invent unwitnessed combinations;
that alternative is excluded.

To evaluate C, apply the reviewed raw-state invariant independently for each
ID: at node v with subtree PUSH mass b_(v,i), set K_(v,i)=B_i-b_(v,i).
Exact and representative executions have equal n_i; p_i agrees or both exceed
K_(v,i); r_i agrees or both exceed K_(v,i)+n_i. Sibling budgets account for
every cancellation. Hence the listed observations agree at every node,
including local checks using unions of the preserved active-ID families.
Different IDs never cancel. Sharing uses one chosen joint tuple for each
shared grammar derivation and one consistent replacement at repeated query
holes. The original G remains retained; a larger later query requires a new
image from G.

**Boundary.** This is query-finite observation of a retained grammar. It is not
a permanent contextual bound quotient. The known smallest one-ID algebra
discriminator still applies: `PUSH_i ; POP_i` is identity, whereas
`PUSH_i ; POP_i²` leaves debt. No numerical rewriting or presence-only
permanent suppression is justified. Correlated mixed recursive schemas in
the assigned discriminator also remain outside hypothesis 1.

## 3. Source-directed reduction and the exact missing premise

The source provides a useful conditional cut by kind; it does not yet provide
the required Effect feedback theorem.

Oracle `annotation/constraints.rs:363–389` constructs a Function's positive
Value result with `NonSubtract`; `:848–851,921–926` makes that wrapper POP-only.
The PUSH stack is instead on the positive return-Effect endpoint at `:453–470`.
The ordinary Value argument swaps and Value result retains context; the two
Effect children leave the Value comparison at
`constraints/machine/propagate.rs:207–271`. Prefix normalization is at `:11–38`.
Oracle `lambda.rs:1571–1578` clears the pre-body output predicate of a top-level
Function annotation. That clearing does not remove its latent result wrapper.

If the successor's new constructor retains this placement and its actual
kind separation, with no whole-value Effectful annotation or cross-kind
symbolic coordinate, Value derivations are debt-only. Proof by induction:
initial Value contexts are empty; their wrappers prefix only POP; replay of
debt operands, swap, and both-from-right cannot create PUSH. Effect children
do not return a context into Value tasks. Current row insertion/replay checks
same-kind endpoints; intrusion explicitly rejects a mixed-kind merge
(`candidate_intrusion.rs:517–530`). This is a conditional owning-constructor
invariant for the next gate, rather than a theorem about unkinded Oracle
TypeVars. Parameterized effect payloads and a future cross-kind variable
connection would invalidate that cut and must be checked separately.

This reduces the unrestricted mixed problem to Effect feedback, after Value
grammar observations. It does **not** prove that Effect feedback is absent.
A Function call can prefix PUSH onto an Effect child carrying arbitrarily
large debt. A symbolic tail or an incoming recursive provider can return that
child to an annotation Effect coordinate. Separate allocation, the 128-depth
annotation bound, lexical owner labels, and top-level predicate clearing do
not preclude this path. Oracle paired annotation construction even has
bidirectional symbolic-tail connections at
`annotation/constraints.rs:641–654`; the assigned PUSH bridge demonstrates
why distinct initial coordinates alone are insufficient. Its Tuple and local
annotation source is not an admitted successor witness.

The minimum unresolved certificate is consequently this:

> For every Effect bound slot formed by the admitted new formal constructor,
> its **complete derivation dependency component**, after ordinary Function
> children, symbolic tails, recursive exposure, level transport, and canonical
> equality, factors into debt-only recursive grammar inputs followed by a
> finite consumer with a source-derived PUSH budget; or that component is
> handled by a separate exact mixed-recursion algorithm.

The dependency component must include PUSH-bearing subexpressions attached to
recursive productions, not only PUSH-labelled physical row edges. For example,
`X -> replay(X,PUSH_i)` contains one finite PUSH terminal outside X's SCC but
adds it on every unfolding. Checking only that all primitive PUSH terminals
are outside the SCC would falsely certify the premise. This is a structural
falsifier for a proposed certificate, not an admitted source witness or another
executed toy probe.

No inspected successor source constructs this certificate: explicit formal
rows are still refused. The exact missing owner is
`candidate_effect::candidate_formal_pair`, together with its same-kind named
Effect coordinate formation and the actual replay/equality dependencies.
Insertion filters must still be checked/registered and erased by the supplied
contract before stored contexts enter this analysis; proving a finite numeric
image cannot excuse those checks. Oracle support admission/self-drop is not
assumed, and the successor's unconditional equal-row shortcut is not extended
to contextual inputs by this result.

## Verification, resources, omissions, and next action

Commands were pinned `git show <SHA>:<path>` reads, narrow source-range reads,
and one `python3 -B` read/hash command using `hashlib` plus read-only Git object
access. Rules research-lab, design-authority and git-concurrency were read.
No Cargo, tests, executable arithmetic checker, mutation run, search, formatter,
child, or Git mutation ran. There are no seeds, enumeration ranges, or omitted
search shards. No execution result corroborates the new product derivation.
All its source equations are shared premises from the reviewed source contract;
there is no independent source oracle. Resource use: small serial source/hash
processes, zero heavyweight processes and zero benchmark samples; CPU/RSS and
aggregate wall time were not measured.

Unverified: mixed Effect recursive admission; actual new weighted constructor;
cross-kind source variable formation; complete support/residual projection;
attachment lifetime/freshening; parameterized families; passthrough consumer
construction; solver transaction/rollback; endpoint-allocation termination;
SCC reindexing of weighted dependencies; public inference and callback target.
The multi-ID derivation has no independent review. No existing gate changes
status, and no source program divergence or source restriction is established.

Recommended next action: the source-formation lane should return the actual
Effect derivation SCC certificate for the Function-only new constructor,
including PUSH subexpressions on recursive productions and reindexing after
equality. A debt/finite-consumer certificate enables §2; a mixed recurrent SCC
requires a different algorithm. More debt counts or another sign-summary probe
would leave this premise untouched.

## Commit packet

- Exact leased path: `notes/progress/2026-10-10-formal-effect-admission-construct.md`.
- Baseline SHA: `e3ddf9f19e08be74a8467a61b5415244f6f5ac0f`.
- Stable pinned source blobs: candidate Effect
  `40991e2f545e765ac04efe53422b6337e8f7a45d`; source preflight
  `ba7c39b31c860f025adfcd31bbb184b20d8bbccb`; extrusion
  `0e10d00fc9db845c03d14537a4ae4bcd5fd81a5f`; solver lib
  `2a43bea966b0ee78ec29f90a404e365710f0de97`.
- Live dependency SHA-256 changes observed, pinned copies retained:
  hygiene note `f96d8d2f577c46d2c09f6ac1bcf095bc9c14ddbe6a413acbff351e243df087c1`
  → `ff61df92a84185ef22aecbc6915208fbdee225dc647b51007ea28601e38a70f9`;
  explicit-effect source map `c95f42ccf8b9c294a7ffde21c37a95431db6321d8e34d6468ca076802d713565`
  → `5c5e58e7f0eae2e4e307b6ed50b42c59825ef55f4bf86ee66d8c377df276b3e5`;
  mixed-debt results `9e0d8a192db0451fc24aaa2920bc6b7f150e0ffd23522fb41978a1bdf41eb8e4`
  → `95671c516f1b927d1c45e6fbf58e5f32c9f01503852994fd771e0c1eb9a7798f`;
  HIR source annotation `5aa5025b49f7342f51b434d8594939bd119c0e623d41f5ad27cbae4d901d37f6`
  → `88c387a07279e2e13364e340c833cc5462126f369ed45fefc8370197b240fd0d`.
  Primary supplied the callback correction separately; no other live delta was
  consumed as authority. Paired gate, mixed discriminator, filter contract,
  solver source/preflight/extrusion/intrusion/lib matched pinned SHA-256s.
- Review status: producer-frozen, unreviewed research; original reviewed debt
  observer remains an external dependency, not review of this extension.
- Checks already run: source/object inspection and dependency hash comparison;
  no executable verification or compiler checks.
- Proposed commit message: `research: isolate formal effect feedback admission premise`.
- Shared deltas intentionally left for primary/curator: record identity-only
  admitted formal context bound, conditional joint multi-ID debt observer, and
  the Effect dependency-component certificate as the reduced source premise;
  retain the general mixed-context gate as open. No task/index/authority,
  question-board, manifest, lockfile, or compiler path was edited.

Writes stop at submission of this frozen artifact.
