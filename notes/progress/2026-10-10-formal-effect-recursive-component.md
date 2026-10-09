# Formal effect recursive components: a generated PUSH self obligation

Date: 2026-10-10
Status: frozen producer research; unreviewed source derivation, no gate closure
Baseline: `951953fc90886b873896452b7f7d740a605f18fc`
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this note only
Method: pinned owning-source derivation; no executable model or compiler run

## Objective and authority

Examine the complete derivation dependency component required by
[constructive admission §3](2026-10-10-formal-effect-admission-construct.md),
starting from the reviewed one-formal `f (f f)` certificate. Governing sources
are annotation hygiene §§1,4–6, the paired Function gate's Remaining production
seams, the falsification note and its independent review, and the mixed-debt
observer results. The selected callback target retains the returned `int ->`:
`(int -> ['b, io] 'c) -> int -> ['b] 'c`. This target is not used as a premise
and is not executed here. Rules research-lab, design-authority and
git-concurrency were read in full.

**Result:** even this formal's two annotation seeds generate a same-row Effect
obligation bearing PUSH. Oracle's same-Var canonicalization drops that
obligation before retention. Consequently the unfiltered source-generation
graph does not establish debt recursion followed by finite consumers. A
factorization of the retained prospective successor grammar needs an exact
contextual admission justification at this self obligation. This is a
source-generation counterexample to a certificate that ignores such generated
self obligations, not an admitted cyclic-PUSH counterexample or a termination
result.

## 1. Typed endpoints and minimized source route

Keep the reviewed control unchanged:

```yulang
type io
my knot (f: 'c -> [io] 'c) = f (f f)
```

Neither parsing nor successful lowering of this complete source is claimed.
The successor declaration producer would be a resolved nullary `act io`;
Oracle's `type io` is not equated with that producer.

Let `F`, `C`, `R`, `S` be **Value** coordinates: body formal, shared written
`'c`, inner result, and outer result. Let `T` be the **Effect** coordinate of
the annotation's return row. Let `i` identify this annotation-owned attachment
and `K={io}` its resolved concrete allowance/filter. No equation identifies
`C` with `T` or makes `i` canonical row identity.

At the Oracle's parameter Function boundary, annotation/constraints.rs
363–389,424–470,602–619 constructs:

```text
A+ = Fn(C-, Row([],Top), Stack(T+, PUSH_i[K]),
        NonSubtract(C+, POP_i/filter K))
A- = Fn(C+, Bot, Filter(T-, K), C-)

S1: A+ <: F- @ identity
S2: F+ <: A- @ identity
```

Here `Row([],Top)` is a negative Effect interface and `Bot` its positive
counterpart; the negative argument Effect is not `Neg::Bot`. The Function
constructor's result wrapper does not disappear when lambda.rs:1571–1578
clears the top-level Function's pre-body output predicate. Seeds S1/S2 come
from annotation/constraints.rs:124–138; lambda.rs:1247–1280 passes the actual
annotation-variable maps into that constructor.

The material new route is the opposite-bound replay at **F**, rather than a
new source constructor:

```text
S1 and S2
  -> A+ <: A- @ identity                         [replay at Value F]
  -> Stack(T+, PUSH_i[K]) <: Filter(T-,K) @ id   [Function return Effect]
  -> T+ <: Filter(T-,K) @ left PUSH_i[K]         [lower Stack normalization]
  -> T+ <: T- @ left PUSH_i[K], filter All       [upper filter normalization]
```

The replay owner is bounds.rs:3450–3470 (and its opposite insertion order
route). Function return Effect retains context at propagate.rs:258–263;
Stack normalization prefixes the left at :11–24. Upper Stack normalization
at :38–55 performs `constrain_pos_lower_by_filter` before changing the filter
to All and enqueuing the inner endpoint. A filter-only weight contains no POP
that cancels this PUSH. The exact intermediate obligation therefore has
typed endpoints `(Effect T+, Effect T-)` and one active same-ID PUSH. It has
the original annotation owner `i`, not a grant created from row equality.

This derivation is conditional on the owning calls being reached and on no
earlier resource/proof/acceptance failure. Source inspection proves which
obligation those calls generate; it does not supply an ordered successful run.
Filter registration/checking is part of the derivation, not assumed erasable
without its owner operation.

The generating core is smaller than the body debt circuit: one formal
Function annotation with one concrete return head and its two paired seeds.
Removing both applications leaves this generated self obligation. No global
minimality over other source constructs is asserted. Removing the concrete
head (using a direct symbolic-only tail) removes this PUSH constructor.

## 2. Generation, Oracle admission and prospective recurrence

Oracle entry.rs:1092–1106 tests `Pos::Var(lower), Neg::Var(upper)` and returns
None when their underlying TypeVars are equal, without inspecting weights.
Thus the final `T <: T @ PUSH_i` candidate is **not** a retained Oracle bound.
The intermediate Stack/filter structures have different endpoint constructors;
the drop occurs after normalization exposes the same Var pair. The analogous
generated Value result obligation `C <: C @ POP_i` is dropped as well.

This is sharper than inspecting physical PUSH terminals outside an SCC: the
primitive source route already produces a contextual self candidate. If an
exact prospective admission retained it, replay through T could have the
production

```text
X -> seed | replay(X, PUSH_i)
```

with one PUSH on every unfolding. Its expanded PUSH mass is k at unfolding
depth k. There is no finite consumer PUSH budget independent of k. This last
sentence is a **conditional algebraic consequence**, with retention and
repeat replay as hypotheses; it is not an established source recurrence.
The pinned Oracle instead removes precisely the candidate needed for that
argument. Alias-only subsumption and its count-forgetting behavior do not
need to be invoked to explain this particular drop.

The actual successor does neither trace: candidate_source.rs:77–81 refuses
explicit formal rows recursively, and candidate_effect.rs:845–847 refuses
them again. Its current pair at :854–863 shares ordinary argument/result
Effect coordinates without weights. The paired gate explicitly leaves
weighted endpoints, contextual memos/bounds, consumed filters and contextual
self obligations as a production seam. There is no pinned prospective rule
that establishes retention, safe discharge, or an exact quotient for this
new same-row PUSH obligation. Copying the Oracle drop is not derived here;
retaining it without a mixed-recursion algorithm is not certified either.

For symbolic-tail provenance, replacing `[io]` with `[io; 'e]` obtains
`T=E_e` directly from function_boundary_effect_stack_inner at :602–607.
Repeated annotation-tail identity follows annotation_var at :835–845.
This produces the same self obligation at a named **Effect** endpoint, with
`C` still separately a Value endpoint. Pure `[; 'e]` takes :430–439 and
introduces no attachment. This variant is a source-rule derivation, not a
parsed fixture or a second admitted counterexample.

## 3. What remains finite in the reviewed body control

The existing body certificate supplies `F -> C` at identity, `C -> R` under
left POP_i, and `R -> C` at identity. Actual applications allocate R/S and
Function demands at tail.rs:543–563; argument reversal and result preservation
are propagate.rs:226–270. For that retained **Value** debt grammar, the four
direct Function children have these source-derived extra PUSH budgets:

| Child | Operation on parent debt context | Additional PUSH occurrences |
| --- | --- | --- |
| Value argument | Swap | 0 |
| Argument Effect | Swap into Row([],Top) | 0 |
| Return Effect | Prefix the annotation's PUSH_i | 1 |
| Return Value | Prefix POP_i and consume/check its filter | 0 |

These local budgets remain exact even when Value debt is unbounded. They
explain why the reviewed debt observer handles those fixed consumers. They
do not prove the whole Effect component has finite PUSH mass: the paired-seed
self obligation from §1 must first be accounted for by admission. No
source-generated **distinct-endpoint admitted recurrent PUSH** was proved in
this assignment. The existing paired-annotation bridge's generation and alias
admission caveats are retained; no graph walk is promoted to an admitted bound.

Recursive declaration uses may connect published result Effect, invocation,
application, block and returned Effect through the owners recorded in the
explicit-effect termination source map. Such unweighted source routes do not
by themselves prove the missing PUSH candidate is retained. No new recursive
edge was invented to turn this self candidate into a distinct-row cycle.

Parent/copy handling uses the selected operation, not a new source constructor:
the parent is retained at actual extrusion, and only an already same-SCC
parent/copy pair is equated. Pinned candidate_intrusion.rs:470–486 checks that
condition; :517–530 permits only same-kind merges. A representative mapping
can identify T with its actual Effect copies while retaining owner i. It
cannot turn a Value coordinate into T, prove this candidate disposable, or
decrease its PUSH mass merely by lowering levels. Our new candidate is
already a same-row obligation before such equality, so neither distinct
allocation nor parent/copy transport supplies the missing admission proof.
No actual weighted extrusion/equality run or post-equality factorization was
proved.

## 4. Claim class, checks and precise blocker

Established external result: the independently reviewed local Value debt
certificate and fixed-continuation mixed-debt observer retain their scopes.
New unreviewed bounded source characterization: the paired-seed equations and
generated Effect PUSH self candidate, followed by Oracle's explicit same-Var
drop. Conditional theorem: if that candidate is retained as a recurrent
production, the finite-consumer hypothesis fails. Candidate assumption not
adopted: that the prospective weighted constructor must retain it exactly as
an ordinary bound. No all-source factorization, source divergence, safe
discharge theorem, or successor conformance is established.

Checks were serial pinned `git show` source reads, relevant-note reads, and
one read-only Python SHA-256/blob comparison. No arithmetic checker ran:
another checker assuming the displayed production would not decide its
admission premise. There is no independent execution oracle; all new source
equations depend on the pinned owners. The prior independent certificate
review is not independent review of this new derivation. No seeds/ranges,
enumeration shards, executable mutations, Cargo/build/compiler tests,
formatting, Git mutations, children, or benchmark samples occurred. The
structural head-removal and body-removal controls above are derivations,
not executed mutations. Resource use: small serial read/hash processes;
CPU/RSS and total wall time were not measured. No heavyweight process ran.

All ten directly hashed successor dependencies matched their baseline bytes
at the pre-write check. Concurrent uncommitted HIR edits were visible and
were neither consumed as authority nor modified. The artifact is frozen at
submission; no independent review is claimed.

The precise blocker is **context-sensitive same-row admission at the future
paired explicit-row constructor**: establish the meaning-preserving retained
derivation or discharge rule for `T <: T @ PUSH_i` after its real filter check,
including future opposite bounds and canonical equality. This seam is
cutover-critical compiler correctness/natural inference correspondence,
not resolved by larger debt enumeration. Unverified scope includes actual
ordered parsing/lowering, distinct-endpoint cyclic PUSH survival, full Effect
observation, public scheme/principality, residual projection, attachment
lifetime, freshening, weighted intrusion and rollback.

Recommended next action: independently audit the §1 paired-seed derivation
and then settle this exact self-obligation admission seam at the owning
constructor before attempting another global SCC factorization.

## Commit packet

- Exact leased path: `notes/progress/2026-10-10-formal-effect-recursive-component.md`.
- Baseline SHA: `951953fc90886b873896452b7f7d740a605f18fc`.
- Oracle pin: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none among the ten directly hashed baseline
  dependencies. Key SHA-256s: hygiene
  `ff61df92a84185ef22aecbc6915208fbdee225dc647b51007ea28601e38a70f9`;
  constructive note
  `519ecf417e6b55b6352c9c144526d7bc12d27799d8d229644dbf8baa995ca81e`;
  reviewed debt certificate
  `545f71dd9c343e38ed380ec491ef9fb95b13176c7b8aa4b93cb0c1a85e35c659`;
  candidate Effect owner
  `3e93caa74a8b04b32c57cd2d9d21e8c380e91d6758e46eed9ec99e908911d5b7`;
  candidate source owner
  `7a37c12e78f6f17486aaa8c76a6559ccd97e2d9a827664d2c22a47ee79191866`;
  intrusion owner
  `097aa65bfdac125ff1ed61de362e9302de6a1ef2a1ea94fd12ae29e77c8e9b8a`.
- Oracle blobs: annotation constraints
  `d2cf0e18266233c1e3c2943448244ee2a3499529`; entry
  `d75544523281cc7f5c6f1778fbe25eb42b7dfe7b`; propagation
  `d558e7b9c17d33e91c5bb39c4cd85ebbfa4a8b09`; bound owner
  `365ed25a8b3b7e468a7a4e57159125be53209708`.
- Review status: producer-frozen, unreviewed research; no gate/status promotion.
- Checks already run: pinned source/authority reads, read-only dependency
  hash comparison, and narrow leased-note whitespace check at handoff.
- Proposed checkpoint message: `research: isolate paired-formal PUSH self admission seam`.
- Shared deltas intentionally left to primary/curator: record the generated
  PUSH self obligation and the Oracle drop as distinct facts; require exact
  contextual same-row admission before claiming the complete component
  factors; retain admitted recurrent PUSH and production gates as open.
  No shared task/index/authority, question bundle, manifest, lockfile, compiler
  path or another worker's file was changed.

Writes stop at this frozen submission.
