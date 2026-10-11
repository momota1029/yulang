# Value Generalize: source levels and discarded recursive dependencies

Status: frozen, unreviewed research checkpoint; bounded static characterization.
Owner: primary-assigned complementary source falsifier, leaf only.
Baseline: `391779c91981ab75d6cf13b0ee331e93bfabd3e3`.
Lease: this file only. No compiler, test, Oracle, design or Git mutation.
Budget: 30 minutes of static investigation; no builds or executable probes.

## Objective, authority and claim class

Attack two premises of the current private native candidate path: (1) every
source-shared Value coordinate is protected from freshening despite ordinary
`non_generic=false`; (2) a graph captured from a member root retains every
dependency required by the selected source Generalize.

The governing contract is
`notes/design/2026-10-08-source-generalize-definition.md`, §§2–4, selecting
`notes/theory/2026-10-08-source-generalize-definition-and-proof.md`,
§§3.1,3.3,4,5.1–5.3. In particular, §5.1(1,3) retains the **entire joint
component relation**, including current members and live peers; §5.1(2,4)
fixes actual established and one-shot free dependencies; §5.1(5) selects
ordinary Desc declarations by constructor/provenance and dependency traversal.
§5.2 allocates a whole component frame per independent incoming use.
The 2026-10-11 top-level inference principles §§1,3–5 preserve mathematical
Simple-sub operations, proof-derived implementation and necessary abnormal
safety. This note changes none of those meanings.

Result: no source-qualified misgeneralization or semantic counterexample was
established. The source construction below gives a concrete **representation
gap**: a member's captured graph can omit a peer's Value descriptor and
Function clause from the actual static recursive component. The additional
claim that this omission changes a lawful source-use fiber is OPEN. In
particular, the omitted unused formal has no demonstrated observation through
an incoming use of the selected member. Compiler/HIR retention outside the
graph could potentially support a reconstruction; no such correspondence is
proved here. Do not promote this finding to unsoundness, impossibility,
principality failure, or parent-gate closure.

The reviewed Value SCC rank proof and synthetic parent/copy SCC searches are
not reproduced. This method follows source construction, lexical levels,
actual recursive-use owners and capture/freshening consumers.

## Actual construction and incoming-use owners

The relevant native route uses `lower_module_with_local_source` and
`ConstraintBatch::collect_candidate_mode(..., true, true)`, rather than the
historical fixture carrier. `lib.rs:1124` selects `emit_candidate_source` for
the retained LocalSource. Existing source-retirement tests use these exact
entrypoints; they were inspected, not executed for this note.

| Owner | Static fact used |
| --- | --- |
| `yu-hir/src/module/local_source.rs:288` | Top-level formals become Lambda occurrences and lexical Parameter identities. |
| `local_source.rs:329` | A function initializer gets a temporary self Local identity, followed by its formal identities; publication restores and installs the local. |
| `local_source.rs:638` | Name resolution first uses lexical bindings, then the complete module namespace; a unique module binding becomes ModuleDef. |
| `local_source.rs:698` | Every private binding before the final expression receives a LocalSourceBinding and initializer work; discarded bindings are not deleted. |
| `candidate_source.rs:213` | A formal Name's Value endpoint is its actual parameter row, not its unused occurrence facade. |
| `candidate_source.rs:257` | Top-level traversal begins at level 1; Lambda keeps that level; a Block raises initializer level by one and publishes at the Block's level. |
| `candidate_source.rs:369` | ModuleDef Names create PendingDefinitionUse with the enclosing module definition as parent; active self initializers use Link; published locals use Local routing. |
| `lib.rs:1280`; `scc.rs:276,416` | Each pending use becomes a parent/target DefinitionUse; both opposing uses form one SCC, including uses inside discarded initializers. |
| `candidate_source.rs:445,461` | Lambda uses its final body endpoint; Block Value is linked only from its final expression. Initializer effects flow separately to Block effects. |
| `lib.rs:11233` | Lambda emits a positive four-port Function into its Value row; its two Value children are the formal and final body. |
| `candidate_scheme.rs:842` | Execute every member schedule before publication, then independently capture each member root at boundary 0. This is not one multi-root capture. |
| `candidate_scheme.rs:306,589,744` | Start capture at one root; a row is local iff level exceeds boundary and `non_generic` is false; follow local row bounds and forward Function children. Stop expanding older/nonlocal rows. |
| `candidate_scheme.rs:947,1009,1363` | Incoming module/local use recaptures its selected root and creates a canonical remap for captured rows only. Older/nonlocal rows keep their canonical source identity. |

## Older formal and recursion attacks

### Self recursion returning an older capture

Consider this authentic LocalSource-shaped source:

```text
my outer a = { my loop x = { my unused = loop; a }; my first = loop; loop }
```

The construction trace, assuming successful syntax/HIR construction and no
resource abort, is:

1. `a` is declared at source level 1. The outer Block's boundary is 1.
2. `loop`'s initializer Lambda and formal `x` are at level 2. Its inner Block
   remains at 2; the discarded `unused` initializer is at level 3.
3. The temporary self identity makes `unused = loop` a monomorphic Local
   reference to the active initializer endpoint, not a fresh scheme use.
4. The inner Block's final Name `a` uses the same parameter row at level 1.
   Its result row is linked from that row; the Lambda's result port reaches
   that Block row. The local loop capture thus reaches the older `a` anchor.
5. Publishing `loop` stores its root and boundary 1. The two later loop Names
   are separate incoming local occurrences: one in `first`'s initializer at
   level 2, one in the outer final expression at level 1.
6. Both routes preserve canonical `a`, since `1 > 1` is false. The unconstrained
   formal `x` at 2 is eligible for fresh rows at each actual use level. This
   traces the rows actually reached; it does not prove that the discarded
   self Name's source clause is captured. Its source monomorphic-frame law
   remains a separate correspondence requirement.

This candidate fails to demonstrate shared-Value freshening. False
`non_generic` alone is insufficient: the level/boundary test protects the
older captured row. This is a static trace, not an executed acceptance or a
proof that every established contract field is represented by that row.

### Captured callable demand

Replace the final `a` in loop's body with `a x`. The Apply demand has older
callee row `a` at 1 and younger argument/result coordinates at 2. The candidate
typed drain (`lib.rs:12418,12431`) extrudes the structured bound to the receiving
row's level. `candidate_extrusion.rs:87–172,220–250` creates polarity copies
at level 1, keeps parent/copy links, and flips Function argument polarity.
For this negative Function demand, the Value argument's positive copy obeys
`x <= x_copy`, while the negative result copy obeys `r_copy <= r`.
Capturing local loop may still freshen `x,r`, but it retains their constraints
to these older copies. Therefore “a younger row occurs in an older callee
demand” does not by itself show that the raw younger coordinate must be fixed.

The exact source-semantic premise is still OPEN: identify the actual complete
Mono contract and each free Desc dependency, then establish its correspondence
to those polarity copies and retained constraints. Scalar Function bounds
are not complete Call or whole-contract evidence. This attack was stopped at
that owning premise; no larger synthetic probe was substituted.

### Bare mutual references and lexical limitation

For the selected bare pair `my f x=g; my g y=f`, each positive Function's
result is the peer Name, so lower-bound replay exposes the peer Function and
its formal descriptor during capture. There is no immediate missing-parameter
witness from that pair. The native rule requires both Desc declarations and
the full relation, independently of whether a raw provider identity is fixed.

Nested sibling forward references are not a replacement attack: the inspected
LocalSource builder installs a local after its initializer and temporarily
installs only its own function self identity. An unresolved forward local
Name is rejected by candidate preflight. This observation describes the
current constructor, not a newly selected restriction on Yulang semantics.
The next attack therefore uses supported module mutual references.

## Minimized source representation witness

```text
my f x = { my u = g; x }; my g y = f
```

No Call, annotation, literal, operation, handler or type conflict is needed.
The parser has ordinary `my` BindingStatement construction
(`yu-syntax/src/declaration/binding.rs:185`) and braced statement sequences
(`yu-syntax/src/statement.rs:562`). The retained HIR block constructor supplies
the private `u` binding, its initializer Name `g`, and final Parameter Name
`x`. Whole-module namespace lookup resolves `g` even though its definition
follows `f`. These are actual constructor paths; the exact string was not
parsed or compiled in this static-only assignment.

Let `R_f,R_g` be definition roots, `L_f,L_g` Lambda Value rows, `B_f` the
Block result, `N_g` the Name g in u's initializer, and `N_f` the Name f in
g's body. `x,y,R_f,R_g,L_f,L_g,B_f,N_f` have level 1; `N_g` has level 2.
The source-generated Value constraints are, up to administrative replay:

```text
F_f = Function(x, entry_f, return_f, B_f)
F_g = Function(y, entry_g, return_g, N_f)
x <= B_f; F_f <= L_f <= R_f
F_g <= L_g <= R_g
R_g <= N_g                 # internal module use f -> g
R_f <= N_f                 # internal module use g -> f
```

`u` stores `LocalScheme(root=N_g,boundary=1)`; there is no incoming u Name and
therefore no local-u graph freshening. Executing/storing that unused initializer
does not link its Value to `B_f`. Its Name effect is bounded by empty and flows
to Block effects, as do all initializer effects. It remains an actual source
Bind/Return/rebind clause inside f's invocation region in selected Build; it
is not a top-level initializer rerun or an erased source clause.

The two module uses have parents f and g respectively, hence one static SCC.
Per-component source execution constructs both descriptors before publishing
either. Actual capture nevertheless calls `capture_candidate_graph(R_f,0)`
and `capture_candidate_graph(R_g,0)` separately, not a shared whole-component
capture.

The key storage fact is `candidate_extrusion.rs:808`: for `a <= b`, if
`level(b) <= level(a)` store b on a's upper side, otherwise store a on b's
lower side. `candidate_insert_bound` installs only that side. Thus
`R_g <= N_g` is stored on younger `N_g` only, while `R_f <= N_f` is stored
on `R_f`. Replaying positive Function lowers can additionally install
`F_f <= R_f,N_f` and `F_g <= R_g,N_g`; it creates no constraint from `N_f`
to its enclosing Lambda g. There is no negative Function in this source,
so Function/Function decomposition cannot add a hidden bridge.

Starting at `R_f`, capture reaches the f Function, its `x,B_f` Value children,
and possibly the `N_f` upper-bound occurrence. It never reaches `R_g,N_g`,
`F_g`, or `y`. Returning from a structural result child to the containing
Function is not a capture rule. Effect paths cannot add y: capture's extra
context-payload traversal imports only effect views and their effect tails.
Evidence snapshots name captured bound fibers, not a peer-member Value seed.
`candidate_scheme.rs:755–803` adds neither all active roots nor all SCC
member clauses to the capture worklist. With no Value extrusion parents in
this all-level-1 Function construction, parent/copy equality cannot add the
missing peer either.

Capturing `R_g` can reach `F_g,y,N_f`, and the replayed f Function at `N_f`;
the asymmetry is therefore important. This is a member-f coverage finding,
not an assertion that both graph captures have the same omissions.

Removing `u = g` removes the f→g SCC edge. Returning g instead of x exposes
the peer Function through f's result and removes this witness. Replacing g
with an external nonrecursive binding removes the whole-component premise.
This is a minimized witness within these checked mutations, not an exhaustive
minimum over all source programs.

## Required relation versus observable difference

Generalize §5.1(1,3) requires the actual whole component relation at f
publication, including g's Parameter Desc and Function/body clauses. Its
classification as fixed versus eligible may require the exact installed local
u contract and event provenance; this note does **not** assert that y is
eligible merely because it occurs in the SCC. Retention is required in either
case, and §5.1 forbids dropping a component conjunct.

Append `my first = f; my second = f` for two actual external source Name uses.
`route_candidate_graph` recaptures `R_f` at boundary 0; fresh-use preparation
remaps captured rows only, so there is no y entry or peer F_g clause in those
incoming graph frames. This is a static consumer trace, not executed evidence.

No legal client observation distinguishing this graph from full ScopedClosure
was constructed. f returns x and merely binds the discarded g value; g's y
may be semantically unobservable in this example. The session retains HIR,
source schedules, peer graphs and live bounds outside f's graph. Those retained
artifacts have not been shown to reconstruct the mandatory whole-component
frame under §5.2 or to preserve its shared/event scopes. Conversely, this note
does not prove that such a reconstruction is impossible. A scalar graph's
literal lack of y proves neither a semantic mismatch nor a valid elimination.

Ordinary collected and fresh metadata start false (`lib.rs:10063–10172`);
candidate equality only ORs existing flags (`candidate_intrusion.rs:578–590`).
This establishes no source-provenance characterization of `non_generic`.
The exact all-source protection premise remains: for every Desc reached in
fix mode at a publication, the candidate must share its correct free semantic
fields through the actual incoming frame, including dependencies absent from
that frame's scalar bound closure. False flags and successful simple captures
cannot establish that premise.

## Checks, coverage, resource use and next action

Only bounded `rg`, `sed`, `cat`, `sha256sum` and read-only Git inspection ran.
No test/build/checker/Oracle command, mutation run, sampling seed, or numeric
enumeration was authorized or performed. The case set consists of the older
formal self-recursion source, its callable mutation, the selected bare mutual
pair, and the discarded-peer mutation above. Existing tests were read for
entrypoint correspondence and were not counted as newly verified results.

The supplied 30-minute wall-time limit was respected. No heavyweight process
was started; tool calls used at most three concurrent lightweight read-only
shell commands. Peak RAM/CPU and exact cumulative process CPU were not measured.
`spec/` does not exist in this checkout; attempted narrow lookup returned that
fact. Exact parse acceptance, resource-abort paths, full source local laws,
OneShot/Established classification through u, ordinary/public inference,
complete Call, soundness and principality remain unverified.

Recommended next action: give the existing prover the concrete f-root gap and
require the source-to-ScopedClosure bridge to account for g's full relation,
its Desc scope, and u's actual invocation Bind/rebind fields using the retained
source/component owners. Establish a lawful elimination/reconstruction under
the unchanged §5.1–5.2 contract or expose a discriminating lawful-use witness.
Do not repair production capture or change the selected semantics from this
unreviewed note alone.

## Dependency snapshot and commit packet

All listed production/authority dependencies matched the pinned baseline in
read-only `git diff --name-only 391779c91 -- <exact paths>` checks. HEAD moved
to `5248980570e966c70afbafb28b9810df3a47dc7f` during unrelated primary work;
that movement did not change these dependencies.

```text
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6  crates/yu-solver/src/shadow_apply.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
3cfce9acfddd77838398cd95cd13c053f71f27a8367b07175a83c825d68a8df8  crates/yu-solver/src/scc.rs
dc18a26663b4351b774a930bfcc8b343cf0c41651960b49ec2f2c6e744b0e89d  crates/yu-syntax/src/statement.rs
eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544  crates/yu-syntax/src/declaration/binding.rs
2349dcd2098ecaaa43ac3a19c8172a97dcab68a20853ae22cd3da75efa8b3a5e  crates/yu-solver/tests/simple_sub_local_source_retirement.rs
61e30f6fc52097ac8a3be3577284d45baa27ab528c4a7f109e3bfcedb405fd46  crates/yu-solver/src/candidate_intrusion_tests.rs
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38  notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240  notes/theory/2026-10-08-source-generalize-definition-and-proof.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
```

- Exact lease/changed path: `notes/progress/2026-10-11-value-generalize-level-falsification.md`.
- Baseline SHA: `391779c91981ab75d6cf13b0ee331e93bfabd3e3`.
- Changed dependency hashes: none at final recheck; primary verifies again before integration.
- Review: unreviewed producer artifact; no independent review claimed.
- Checks run: bounded static source reads; baseline dependency diff and SHA-256 inspection; final note whitespace/diff inspection and hash recorded in the returned packet.
- Proposed message: `research: trace Value generalization levels and discarded peer coverage gap`.
- Shared deltas left for primary/curator: record the whole-component source bridge as OPEN with this concrete coverage case; keep complete Call/soundness/principality and all production gates OPEN. No shared record was edited.
