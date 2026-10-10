# Ordinary Function argument Effect: counterexample audit

Date: 2026-10-10
Status: unreviewed research-only falsification audit; no theorem or gate promotion
Baseline: `3fab829c0683e4b3b06dfe61f4b60a12884560a5`
Exclusive lease: this note only
Method: minimized typed constructor witness and independent frozen-source inspection

## Objective and authority

Try to falsify the ordinary Function argument Effect order derivation in
[the conditional port proof](2026-10-10-function-argument-effect-contravariance-proof.md)
or its source bridge, preserving exact annotation/member identity, owner,
endpoint polarity, and construction lineage. Governing authority is
[contextual attachment admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§2–6, especially §3/§3.1 identity and §4 Function/positive-wrapper transitions.
The accepted bounded gate supplies no result for the retracted callback example.
[Annotation hygiene](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§1 and [formal integration](2026-10-10-selected-formal-contextual-integration.md)
§2 fix composed annotation variance independently of paired endpoint polarity.

No falsifier of the **stated conditional** order theorem was found. A smallest
nontrivial weight witness instead falsifies the mutation that swaps after
prefixing. This is an internal typed algebra witness, not a source-reachable
compiler counterexample. The current source bridge remains bounded; its missing
source formation and execution premises are explicit below.

The [conditional hygiene proof](2026-10-10-contravariant-effect-conditional-proof.md)
already supplies a two-contribution same-support witness. This audit does not
repeat that attack, derive attachments from support, or reinterpret subtraction.

## Exact target and inability to falsify it

Fix the same parent context P, actual child weight w, and ordinary Function
comparison throughout. Exclude the syntactic Oracle `Neg::Bot` argument-effect
passthrough, as the theorem itself does. The positive wrapper is encountered
at the positive child endpoint **after** argument endpoint reversal. Its local
template is precisely `PrefixLeft(w, Identity)`; it is not a general DAG.
No additional admission/normalization/replay occurs in the claimed two steps.

The prescribed steps yield Q = Swap(P), then PrefixLeft(w,Q). Thus a falsifier
of `PrefixLeft(w,Swap(P))` would have to contradict one of those transitions or
their encounter order. No algebraic choice of P,w satisfying the hypotheses
can do so. This is an audit of the supplied conditional claim, not independent
certification of all compiler transitions. Positive/negative endpoint reversal
does not itself establish an annotation's source-composed sign or attachment.

## Minimized typed witness against the reversed-order mutation

Use one ordinary Function comparison with otherwise inert, well-sorted Value
and result ports. Its relevant frozen-Oracle constructor fragment is:

```text
F_l : Pos::Fun { arg_eff: Neg::Var(e_l), ... }
F_u : Neg::Fun { arg_eff: Pos::Stack { inner: Pos::Var(e_u), weight: w }, ... }
F_l <: F_u under P = Identity
w = StackWeight::push(i, H), H = the resolved singleton family set {E}
```

`e_l` and `e_u` are fixed distinct effect coordinates. In particular `F_l.arg_eff`
is not syntactic `Neg::Bot`. Argument descent produces exactly
`F_u.arg_eff <: F_l.arg_eff`; consuming that positive Stack then produces
`Pos::Var(e_u) <: Neg::Var(e_l)`. The wrapper belongs to the positive argument
Effect endpoint of F_u after reversal, not to F_l or the parent Function.

For the conditional annotation reading, retain one supplied source occurrence
a, owner f, path p, lexical scope s, attachment-set identity i, member ordinal
0, resolved E, and wrapper-constructor lineage k. These are fixed labels of
the supplied formation witness. Neither mutation changes them. The source
composed sign of a is separately supplied; the arithmetic does not compute it
from endpoint polarity. No raw Yulang source or executed boundary is asserted
to construct this package. In particular i is not E's nominal identity.

Write a directed left entry as `(i, leading_pops, family, pushes)`. Directly
expanding the frozen implementations gives:

```text
Swap(Identity) = Identity
PrefixLeft(w, Swap(Identity)):
    left = [(i, 0, H, 1)], filter = All; right = []
Swap(PrefixLeft(w, Identity)):
    left = [], filter = All; right = []
```

The last line follows because `swapped()` converts the prior right side to
left, and converts only the **leading POPs** of the prior left side to right.
This PUSH has zero leading POPs. Swap therefore discards it when incorrectly
moved outside the prefix. It is not a lossless exchange of left and right.
The exact syntax also differs: PrefixLeft versus Swap at the root.

This is minimal for a semantic separation with identity P, an All filter, and
no POP: zero PUSHes yield identity on both routes, while one PUSH of one
attachment suffices. One Function argument descent and one positive wrapper
are sufficient. It asserts no minimality across arbitrary filters or nonidentity
parent contexts. No runtime effect disappearance or handler choice follows
from the weight difference alone.

## Independent source evidence and current bridge limits

This worker independently extracted the frozen Oracle blobs from commit
`6a18bd24bd0fa8b07e3eca5e099bfa8646320e3a`; their identities match the supplied
port-proof evidence. Relevant exact source locators are:

| Frozen Oracle path | Evidence | Git blob |
| --- | --- | --- |
| `crates/infer/src/constraints/machine/propagate.rs` | :226–255 reverses ordinary argument endpoints with `swapped()`; :19 and :31 subsequently use `with_left_prefix(weight)` | `d558e7b9c17d33e91c5bb39c4cd85ebbfa4a8b09` |
| `crates/infer/src/constraints/mod.rs` | :3566–3582 implements directed Swap and left prefix | `14860e3664a7ac05f7493f1d51fe69a6f34216e5` |
| `crates/infer/src/constraints/directed_weight.rs` | :92–115, :230–239 and :349–355 preserve PUSH on left and extract only POPs on right | `a5998519c74f89a8bd65b22defd8f0a1e4fd59d9` |
| `crates/poly/src/types.rs` | :350–353 constructs a single PUSH with the same supplied SubtractId/family | `472e3ae280cf5aaeb81fa49f9104fcde83214d0a` |

Independent extraction authenticates these source bodies; it does not make
this worker an independent reviewer of this jointly investigated gate. Oracle
and this derivation share its exact directed-weight rules. There is no separate
executable semantic oracle, mutation runner, or compiler execution.

At the pinned current baseline, `candidate_context.rs:1675–1726` composes a
nonidentity parent's Swap before a child-local PrefixLeft. It retains the exact
parent relation and a FunctionPort dependency. `lib.rs:12020–12084` reverses
argument Effect endpoints and admits each child with that field. These reads
found no contrary ordinary nonidentity ordering.

The current fragment does not realize the full witness: LocalWeight's left
word and right POP carrier are `[(); 0]` (`candidate_context.rs:17–19`), while
source attachment unit PUSH is dormant. `candidate_source.rs:92–105` keeps
negative concrete annotation rows disabled. `candidate_effect.rs:1384–1395`
does not construct their concrete subtraction wrapper. Context execution
accepts identity or the supplied zero-word filter fragment; Value nonidentity,
Swap, and non-flat PrefixLeft fail availability (`candidate_context.rs:1729–1830`).
These are observed implementation limits, not new source rejection authority.

There is also a deliberate identity distinction: argument admission omits the
structural Swap node when the post-check parent is Identity, retaining Swap in
FunctionPort incidence instead. Consequently the current context tree for
that case is not literally the primitive pre-normalization tree in the theorem.
This is no counterexample to the theorem's excluded normalization stage, nor
evidence that a nontrivial Swap may be omitted. A source correspondence theorem
must state its observation point and account for that existing distinction.

## Coverage, stopping condition, and omitted premises

Two distinct attacks were performed: invert the primitive order using the
minimal directed PUSH witness, and inspect actual frozen/current constructor
and consumer ownership. Neither falsifies the stated conditional theorem.
Neither supplies the missing source-owned positive wrapper/attachment and
actual complete activated worklist trace. Another supplied-transition checker
would leave those premises untouched, so no third model probe was launched.

This is analytic coverage of one nontrivial weight, one reversing port and one
wrapper, plus the named source branches. There are no seeds, numerical ranges,
random cases, exhaustive-source search, timing samples, or mutation runs. An
initial broad task-record capture was output-truncated; no completeness claim
relies on its missing portion. Subsequent source reads were narrow and bounded.

Remaining premises are authentic annotation formation (owner/path/sign/identity
and lineage), typed transport, current/future lower checks, activation and
complete replay, and downstream observation of the actual context. General
effects, source reachability of this PUSH witness, Bot passthrough/inferred-entry
`both`, mixed recursion, residual generation, lifetime/rollback, soundness,
principality, concrete-formal enabling and public/F5 cutover are unverified.
Failure conditions for extending the result include relocating the wrapper to
the wrong endpoint, substituting an arbitrary local DAG for its closed template,
deriving source sign from endpoint polarity, changing attachment or member
identity, observing after an unaccounted discharge, or using a Bot branch.

Recommended next action: assign the actual negative annotation formation and
positive wrapper consumer bridge, retaining its source certificate and the
precise post-check/primitive observation point. That is a safety/correctness
construction seam with reconstruction-debt risk, not a reason to alter meaning
or enlarge this algebra search.

## Frozen dependencies, checks, and commit packet

Direct workspace SHA-256 snapshot:

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/progress/2026-10-10-function-argument-effect-contravariance-proof.md` | `7377dc89973b5b380c1466161f0c20e94d0cf39fb860aa1477e9a3b3aec1730c` |
| `notes/progress/2026-10-10-contravariant-effect-conditional-proof.md` | `3ef7fd4b45dc55b7e2d7ffb32f28ae2a9912176570d96756658a1f6896033c02` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/progress/2026-10-10-selected-formal-contextual-integration.md` | `0a07713df99571d19705333e73c195c3ad29b6165af92cb6821c02cd407da507` |
| `crates/yu-solver/src/candidate_context.rs` | `2897c168c02640443a2f1280286a648853afe08324294c53f1c95d373ac3a337` |
| `crates/yu-solver/src/candidate_effect.rs` | `2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e` |
| `crates/yu-solver/src/candidate_source.rs` | `8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0` |
| `crates/yu-solver/src/lib.rs` | `9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1` |

Checks already run: read-only `git show`/`git rev-parse` authenticate the four
Oracle blobs; `sha256sum` freezes workspace inputs; baseline comparison and
final note/dependency integrity check PASS. These are document/source checks,
not tests. No build, compiler test, benchmark, checker run, delegation, external
contact or Git mutation occurred. Resource use was lightweight reads and one
note write; peak read-command concurrency three. CPU/RAM and total wall time
were not instrumented. Only this leased note changed; shared records are untouched.

Commit packet: exact leased path
`notes/progress/2026-10-10-effect-variance-counterexample-audit.md`; baseline
`3fab829c0683e4b3b06dfe61f4b60a12884560a5`; changed dependency hashes none at
final recheck; frozen Oracle commit/blob identities above; review status
unreviewed producer artifact, research-only, no closure. Proposed message:
`research: audit ordinary Function effect order with a minimal PUSH witness`.
Shared-record deltas intentionally left for the primary/curator: record no
conditional-theorem falsifier, the one-PUSH reverse-order mutation witness, and
the exact source formation/execution and identity-observation gaps; retain all
broader proof/implementation/cutover gates unchanged. The artifact is frozen
on handoff; this worker makes no further writes during review.
