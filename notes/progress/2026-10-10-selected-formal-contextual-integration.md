# Selected formal annotations: covariant delivery and the contextual remainder

Date: 2026-10-10
Status: scoped source/semantic and lifecycle review complete; covariant formal subtransition verified; full negative contextual inference unresolved
Successor integration baseline: `3b263e110074cb17a04cae0b1eb529d879595e0f`
Original research baseline: `658b914f319dbc079cd140bfa4698a44185f4c93`
Implementation dependency: current formal-covariance delta; final code hashes and test outcomes are primary-owned synchronization
Historical Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Integration: primary-owned reviewed checkpoint; no new semantic authority

## 1. Result, authority, and the remaining task

Composed variance separates two different implementation cuts. Concrete rows
inside a Function-valued argument of a formal can be **covariant**, despite
appearing textually inside a formal. Those rows use the existing source-owned
Support/Allowance constructor. A concrete row on the direct formal callback's
return is **contravariant** and requires the unfinished attachment/subtraction
constructor. Delivering the first cut does not complete the second.

The selected policy is [annotation effect hygiene](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§1: reverse variance at Function arguments and argument effects, preserve it at
results and result effects; negative concrete annotations permit local
subtraction, positive ones permit their concrete effects. Symbolic variables
remain connected, and concrete identity is resolved declaration identity.
The [residual-lineage selection](../design/2026-10-10-contextual-residual-lineage-selection.md)
keeps independently constructed recipes distinct and requires current/future
fan-out after source equality. It does not choose a numeric saturation method
or close contextual lifecycle, complete Call, hygiene, soundness or principality.

This note consolidates corrected source construction, the actual covariant
Rust constructor and consumer, a nullary sort theorem, one conditional exact
numeric closure, and a concrete residual-owner obstruction. It replaces the
useful content of three unpublished research drafts without preserving their
incorrect source bridges as active theorems. The primary owns their archival,
verification results, shared status synchronization and Git integration.

The full negative-formal task remains unsolved. No source-specific fallback,
registry prerequisite, satisfiability prerequisite, arbitrary count/depth cap,
input restriction, or F5/default-inference cutover follows from this report.
There is no proof here that Yulang is undecidable or that its required ordinary
inference behavior is impossible. The unresolved engineering/proof seam is
phase-aware Effect replay together with indexed residual recipes and their
actual lifecycle, after the source sort reduction below.

## 2. Source grammar and composed variance

The current HIR annotation alphabet is finite per source and has two sorts:

```text
Value ::= Unit | Int | value-name | Function(Type, Type)
Type  ::= optional EffectRow together with Value
EffectRow ::= resolved nullary effect declarations together with effect-names
```

`SourceEffectId` contains module and declaration identity. Its concrete row
carrier has no type-argument/payload coordinate. `SourceAnnotationValue` owns
Function; `SourceEffectRow` owns concrete declarations and symbolic effect names.
The current candidate admits at most one symbolic tail in an explicit row.
This grammar describes the implementation inspected here, not a new approved
restriction on future parameterized effects or the whole language.

Let variance be `+` or `-`. Whole-binding annotation construction starts at `+`;
formal annotation construction starts at `-`. For a Function at variance s:

```text
argument Value and argument Effect : reverse(s)
result Value and result Effect     : s
```

These equations are recursive. Endpoint polarity, which selects the positive
or negative member of a paired interface, is a separate coordinate. A negative
endpoint at a covariant position still represents an allowance; endpoint
polarity alone does not authorize subtraction.

| Written occurrence | Variance derivation | Selected concrete constructor |
| --- | --- | --- |
| formal `cb: int -> [io, 'e] ()` | formal `-`, result preserves `-` | negative attachment, unfinished |
| formal `consume: (int -> [io, 'e] ()) -> ()` | formal `-`, outer argument flips to `+`, nested result preserves `+` | covariant Support/Allowance |
| formal `consume: ([io] int) -> ()` | formal `-`, argument flips to `+` | covariant Support/Allowance |
| formal `cb: ((int -> [io] ()) -> ()) -> ()` | formal `-`, two argument flips return to `-` | negative attachment, unfinished |
| whole annotation `'a -> (int -> [io, 'u] ())` | whole `+`, two result descents preserve `+` | covariant Support/Allowance |

The old `consume` witness was misclassified as a negative constructor source.
Historical Oracle annotation lowering `lower_value_bounds` constructs PUSH
wrappers on written return rows without carrying this selected composed
variance coordinate. Its paired shapes can motivate a negative-position
construction, but cannot be copied wholesale to every selected source position.
In particular, the double-flip `consume` case must not gain PUSH merely because
that historical annotation builder would put one there.

The same correction invalidates the proposed three-concrete source bridge:
the middle argument Function row is covariant in the relevant shape. The
algebra generated by `(P_i, R_i P_j, L_i P_k)` is not established as the selected
source theorem. Its arithmetic does not repair the missing variance derivation
and is not carried forward as a compiler result.

A whole-binding row `: ['t] 'v` checks the initializer computation. For a named
lambda, that computation is its creation, not its latent body invocation.
Attaching that row does not seed `'t` with a later body operation. Concrete
ingress below instead comes from an actual operation in a named inner body,
whose Function result-effect port is compared at an actual provider use.

## 3. Implemented paired formal construction and covariant consumer

The inspected delta is in `candidate_source::preflight_formal` and
`candidate_effect::{candidate_formal_pair,candidate_formal_effect_port}`.
Preflight starts negative at the formal root and recursively flips arguments.
At a positive position it permits an explicit row with at most one tail,
including `[io]`, `[io, 'e]`, and `[]`. At a negative position it keeps only
the existing singleton symbolic row; negative concrete/closed-empty rows
remain unavailable. A root computation row on a formal is still rejected.

For a source formal Value owner b, the paired interface has two owner edges:

```text
annotation-positive <= b-negative
b-positive <= annotation-negative
```

The negative interface is the formal demand retained for incoming actuals.
It is not substituted for the raw body row, which would destroy ordinary
provider-to-body flow. A paired Function has exactly these four children:

```text
F+ = Function(argument-negative, argument-effect-negative,
              result-effect-positive, result-positive)
F- = Function(argument-positive, argument-effect-positive,
              result-effect-negative, result-negative)
```

The constructor recurses with composed variance while building both polarities.
Omitted formal effect ports keep their existing shared fresh row. Singleton
symbolic ports keep the scoped Effect row. Concrete/empty covariant ports call
`candidate_signature_effect` twice with one shared occurrence-to-view map.
Both calls therefore reference the same annotation-owned view, rather than
creating two independent permissions or identifying unrelated source positions.

For a covariant row with concrete set H, tail t, view a and paired fresh ports:

```text
Support(a)   <= q-positive-port       // retained positive lower membership
q-negative-port <= Allowance(a)       // retained negative upper membership
a = (annotation owner, row occurrence, H, optional t)
```

The implementation's `candidate_insert_bound` stores those typed memberships;
the equations state their logical direction, not paired physical row adjacency.
`Support(a)` emits one `AnnotationMember(a,h)` per h in H, and forwards the
same view's tail as an Effect task if it exists. `Allowance(a)` accepts a
resolved member/contribution exactly when its declaration is in H; otherwise
it forwards that intact operand to t, or records an effect mismatch when no
tail exists. No attachment ID, PUSH/POP context, or subtraction is constructed.

Consequently `[io]` permits io and rejects an unmatched operation; `[io, 'e]`
permits io and forwards an unmatched operation into `'e`; `[]` has no members
and rejects every concrete operand. A symbolic-only formal row still names
its shared row directly. An allowance itself creates no contribution. Positive
support publication and negative checking are separate constructor duties.

### Finite local closure proof for this delivered cut

Fix one finite admitted source action and a finite pre-existing candidate
state. Its annotation tree allocates at most a constant number of paired
ports/Function nodes per tree node, one view per written covariant row in the
local view map, and one scoped row per newly seen Value/Effect name. The maps
are kind-separated and the formal tree is finite; no operation in this new
constructor unfolds a recursive type or creates a count-indexed owner family.

Fix a propagation phase after those allocations, with endpoint sets V and E
including every `AnnotationMember(view, member)` key of its finite views. The
universe is closed under the scheduled Function/support/allowance consequences;
this phase contains no further extrusion/copy endpoint allocation.
The typed pair universe is bounded by `|V+| |V-| + |E+| |E-|`. Ordinary row
insertion retains finite memberships, memoizes a pair before scheduling its
consequences, and Function decomposition has four children. Support expansion
has exactly `|H|` member children plus at most one tail child. Allowance
checking has at most one tail child. Neither effect consumer allocates a fresh
endpoint. Thus this extension preserves the finite-pair worklist argument for
such a fixed phase, including cyclic symbolic tails; a tail cycle cannot
create a new weighted task key because the delivered cut has no weights.

This is a local extension theorem, not a fresh proof of all source inference.
The older [directional source theorem](../theory/2026-10-10-candidate-directional-source-correspondence.md)
§6 has an explicit equal-level/identity-extrusion source envelope. Its argument
cannot silently certify every unequal-level copying path. General orchestration,
copy-event finiteness and accepted resource failures keep their existing proof
and implementation boundaries. The new finite annotation allocation and
nonallocating consumers introduce no new unbounded context mechanism there.

The existing [mixed allowance lifecycle](2026-10-10-mixed-covariant-allowance-capture.md)
is reusable for these same executable views: capture retains incoming typed
allowance incidence; positive extrusion reconstructs source and exact copied
tail; freshening remaps the retained view and tail; equality splices incidence
buckets without adding reverse solver/SCC edges. Copying preserves owner,
source occurrence and resolved members. This reuse is justified by calling
the same view constructor and consumers, not by similar printed row syntax.

The constructor reserves temporary maps before use and releases its scratch
charge after construction. The ordinary transaction journals new views,
scoped names, memberships and formal-domain installation. Failure restoration
must restore those records and resource accounting before retry. Focused
runtime verification of the delta is primary-owned; test outcomes below are
not inferred from this proof or from the existence of a test function.

## 4. Correct direct negative source and executed boundary

The corrected source fixture is
`/workspace/scratch/15155572c47b/source_context_witness/negative_direct_provider_current.yu`:

```yulang
act io:
  pub ping: () -> ()

my witness (cb:(int -> [io, 't] ((int -> ['t] ()) -> ['t] ()))) = cb
my provider x = { my inner f = io::ping (); inner }
my answer = witness provider
```

All lambdas are named bindings retained by LocalSource. The declared operation
is real; there is no anonymous lambda, expression `as`, fabricated concrete
lower, or whole-lambda creation-row seed. The control removes only io from the
formal row, leaving `['t]` and the same provider/operation. The provider's outer
creation/call body returns the named inner Function; `io::ping ()` is the
inner Function's latent body effect, not the outer creation effect.

The primary executed the public inventory harness on the direct provider,
its symbolic control, and the direct consumer below. All have no parser
recoveries and form LocalSource. Both concrete direct fixtures report candidate
`Unsupported`; the symbolic control solves without conflicts and records two
source calls. The carrier retains legacy HIR placeholder errors separately;
LocalSource formation and candidate availability are the discriminating checks.
Ordinary collect/solve success in that inventory is not execution of the
contextual successor. The output is `inventory-direct-output.txt` in the same
scratch directory. No weighted negative-source execution has occurred.

### Required negative-position constructor equations

These equations define the source-derived construction obligation being
investigated, conditional on installation of its unfinished contextual owner.
They do not describe a currently present Rust weighted representation.
For the direct formal's concrete negative return row, let i be its actual
attachment occurrence, H={resolved io}, and t its scoped Effect tail. The
paired local interface uses a positive Effect PUSH, an owned negative filter,
and a POP wrapper on the returned Value:

```text
positive return Effect : Stack(t+, PUSH_i[H])
negative return Effect : Filter_H(t-)
positive returned Value: NonSubtract(C+, POP_i/filter_H)
negative returned Value: C-
```

Other omitted formal ports retain their ordinary paired ports. Variable-only
rows share the same t only in Effect positions. In the written direct source,
B is the outer callback Function, C its returned Function, and D the Function
in C's Value argument. The concrete row occurs only at B's result Effect,
which is composed negative. C and D return rows are symbolic-only.

Paired insertion at the authentic body formal b gives B+ <= b- and b+ <= B-.
The required comparison B+ <= B- begins at identity. Its structural children
emit the following owned obligations:

| Child comparison | Context at t | Reason |
| --- | --- | --- |
| B result Effect | left PUSH_i[H] | negative-position attachment/filter pair |
| C result Effect | left POP_i | B returned-Value NonSubtract wrapper |
| D result Effect | right POP_i | C Value argument reverses inherited POP |

The D obligation is supplied by a **finite Value descent**, not by swapping a
recursively generated positive Effect context. Owned filter registration must
occur before filter erasure on forwarding, including existing and future
concrete lowers. Equal Var endpoints alone do not prove these contexts identity.
Historical Oracle omits its equal-Var self before retaining it; its omission
does not establish the selected contextual successor's obligation redundant.

The real provider's inner Function supplies an io Row to t through C's
result-Effect comparison at the use of `witness`. That use requires joint
capture/freshening of b, its Function children, t, and all three contextual
obligations. The current symbolic control verifies the source topology and
ordinary connection, but not that future weighted transport. Without that
transport there is no executed source recurrence theorem to claim.

## 5. Nullary source sort separation and constructive replay grammar

**Endpoint theorem.** The inspected current candidate preserves Value/Effect
sort through source construction, propagation, capture, freshening, extrusion,
intrusion and rollback. Function descent may emit Effect children from Value;
no Effect task emits a Value child in this nullary source alphabet.

The proof is an induction over owning transitions. `ValueEndpointKey` owns
Function and Value rows; `EffectEndpointKey` owns bottom/empty, contributions,
members, Support/Allowance and Effect rows. `TypedPairKey` and
`LiveConstraintTask` preserve that disjoint union. Function dispatch has child
sorts V/E/E/V. Effect support expansion and allowance forwarding are E-to-E.
HIR supplies no concrete effect type arguments whose invariant comparisons
could produce a reverse Value task. Annotation names use separate maps even
when the spelling is equal in both sorts.

`candidate_extrusion` copies each tagged row through its same-sort allocator
and restores typed bounds. `candidate_scheme::RowKey` keeps kind; freshening
maps an Effect view tail only to Effect. `candidate_intrusion` records only
same-sort parent/copy pairs, uses separate representative forests and rejects
cross-sort equality. Capturing a Function discovers its Effect child, but this
structural discovery is not an Effect-to-Value propagation edge. Rollback
restores the tagged records; it introduces no reverse constructor.

**Context corollary for the required negative extension.** Its source PUSH
starts only on Effect ports, and its returned-Value wrapper supplies only
POP. Value composition, swap, correlated both, filters and normalization of
debt-only contexts never create PUSH. Residual-head decomposition emits two
Effect-to-Effect equations. Therefore a constructor-faithful extension keeps
recursive Value contexts debt-only, while Effect contexts may contain PUSH.
This second statement is a contract for the unfinished weighted extension;
current Rust does not implement contextual PUSH/POP and cannot execute it.

The reduced construction can be written as a typed owner grammar. For each
retained Value task owner v and Effect task owner e, let V_v and E_e contain
contexts produced by finite derivations, using authentic retained owners:

```text
V_v ::= debt-only source constants
      | replay(V_a,V_b) at an actual Value lower/upper owner
      | swap(V_a) at an actual Function argument child
      | both(V_a) at an actual atomic Function branch
      | debt-only wrapper/transport at its actual Value owner

E_e ::= source Effect constants or a debt context emitted by a Value port
      | PUSH_i[H](E_a) at its actual negative annotation owner
      | replay(E_a,E_b) at an actual Effect lower/upper owner
      | filter/allowance/head-reduction at its actual Effect consumer
      | typed transport and residual feedback at its retained owner
```

Binary replay means independent Cartesian lower/upper choices, with its
actual tree bracketing. There is no production `swap(E)` or `both(E)`, and
no E-to-V production. Wrapper/filter phases and residual constructor identity
are retained; the grammar does not normalize them away in advance. Its owner
graph is source-constructed rather than an externally supplied arbitrary
grammar. This rules out importing a recursive positive swap/both or shared-child
PCP obstruction without proving a missing reverse source bridge.

It does not make Effect replay debt-only. The direct source's finite Value
descent emits right debt to the positive Effect component. Exact mixed Effect
replay and indexed residual feedback remain required. Nor does a sort theorem
prove finite recipe allocation or a full mixed decision procedure.

The integrated `8921c333` local self-recursion delta contributes ordinary
Value `Action::Link` seeds to its active initializer; later published uses
still follow the scheme route. It adds no Effect-to-Value constructor and
does not widen the older identity-extrusion theorem by implication. The
`c8da9dff` [historical bridge correction](2026-10-10-paired-annotation-push-bridge-correction.md)
withdraws a same-formal source attribution: its tuple owners were distinct,
and the observed reconnection cancelled PUSH with right POP. The integrated
`3b263e11` [attachment admission proposal](../design/2026-10-10-contextual-attachment-admission-design.md)
is reviewed but unapproved. Its historical two-circuit acceleration premise
does not establish selected composed variance or current contextual source
transport. Neither certificate admission nor private publication deferral is
authorized or implemented by this consolidation. Retained shared operation
inputs also do not replace Cartesian replay with a shared-child equality rule.

## 6. Exact conditional singleton closure and its limit

One useful arithmetic result survives the source repair. For an authentic ID i
write a normalized coordinate as `(p,n,r)`, where the left word is
`POP_i^p PUSH_i^n` and the right debt is `POP_i^r`. Replay first computes

```text
p = p1 + max(p2-n1,0)
n = n2 + max(n1-p2,0)
r = r1+r2
```

Then mix returns `(p,n,0)` if r=0; `(p,n-r,0)` if n>r>0; otherwise
`(0,0,p+r-n)`. Thus its normal domain is

```text
N = {(p,n,0): p,n natural} union {(0,0,r): r natural}.
```

Suppose an actual owner retains singleton unit self contexts P_i, L_i, R_i,
has a concrete identity seed C, and every admitted replay result is normalized.
Suppose no raw pre-mix consumer is silently replaced by a normalized one and
the family decoration at this coordinate is fixed on these generators; each
generator replay must also pass its actual retained filter checks. Then
the exact replay closure of C's contexts is N: L_i repeated p times followed
by P_i repeated n times constructs every left point; R_i repeated r times
constructs every right point. Each witness is a finite sequence of actual
retained self replays. The mix equations put every replay result in N, proving
the reverse inclusion by induction on its actual replay tree.

For a nonidentity normal seed, one may also reset this coordinate: R_r followed
by P_r resets right debt; a left `(p,n,0)` followed by R_(n+1) becomes R_(p+1),
then P_(p+1) resets it. Unit repetitions realize those larger contexts. Rebuild
then gives N, while singleton generators leave every other ID unchanged.
The exact finite description is `(r=0) or (p=0 and n=0)` over natural counts.
It permits fixed finite continuations to be expressed by piecewise-linear
relations; that observation does not erase filters/origins or identify gammas.

This is an **actual-transition theorem given owned records**, not a theorem
that all source SCCs contain those records, or that the corrected source's
freshened weighted component has already been built. The direct negative
source supplies a construction route for the required P/L/R records, but its
implementation/transport prerequisite is still missing. Arbitrary mixed
components, families that change during residual projection, raw phases and
indexed owner recursion are outside this finite formula's completeness claim.

Even without swap/both, replay is phase-sensitive and cannot be flattened by
signed debt alone:

```text
replay(replay(P1,R1),L1) = L1
replay(P1,replay(R1,L1)) = R1.
```

Both have signed debt 1. A raw PUSH wrapper followed by a filter can distinguish
left debt from right debt before mix: prefix_P1(L10)=L9 has no active family,
whereas prefix_P1(R10) retains raw `(P1,R10)` with an active family. A retained
Empty filter observes that difference. Therefore N's normalized formula does
not justify moving a filter check across a wrapper or forgetting its phase.

## 7. Residual consumer, lineage, and a concrete owner obstruction

The corrected direct consumer fixture adds a whole-binding annotation:

```yulang
my witness (cb:(int -> [io, 't] ((int -> ['t] ()) -> ['t] ()))):
  'a -> (int -> [io, 'u] ((int -> ['u] ()) -> ['u] ())) = cb
```

It uses the same declared io, named inner provider and `witness provider` as
§4. The actual one-line fixture parsed and formed LocalSource; the direct
negative formal still makes the candidate unavailable. The whole result row
is positive and must be constructed as an Allowance/Support view, not as a
second subtraction attachment. Historical Row-head decomposition below is
an owner-level correspondence candidate for this allowance consumer, not a
currently executed Rust residual implementation.

For one genuine incoming task `s <= Row(H,u) @ w`, let rho be its actual
residual-constructor lineage and gamma_rho its fresh Effect owner. Head
retention/subtraction at that consumer preserves authentic ID/count fields
and emits the two owner equations:

```text
s <= Row(retained-heads,gamma_rho) @ identity
gamma_rho <= u @ residual-left(w) with the original right debt
```

Left active families are projected by head removal; POP/PUSH multiplicities
and retained context remain exact. The selected policy keeps different rho
distinct even after source equality. In a finite already-constructed recipe
family, Cartesian bound replay plus transferred bound collections proves
current/future fan-out: each admitted source lower meets every retained Row
upper, and each gamma lower meets its retained outgoing upper. Qualifying
parent/copy equality must transfer both sides and contextual obligations.
That local induction proves delivery of each finite replay; it does not prove
there are only finitely many rho or that an indexed family is decidable.

For incoming P_i^k[io], k>0, head removal can emit
`gamma_rho <= u @ P_i^k[Empty]`. Count k is unbounded in the conditional
singleton closure. Keeping a finite supplier formula alone cannot justify
merging those gammas. A symbolic family must retain constructor lineage,
count parameters, head case and correlations to all outgoing relations.

Unbounded concrete-lower contexts do not by themselves imply unbounded
Var-to-Row upper contexts or unbounded recipe construction. The current
candidate retains one level-selected side of an alias constraint, and two
upper records alone do not replay. Negative extrusion can install a lower
copy record, but an actual source derivation must establish that record and
its consumer before a source-level pumping claim follows. No theorem of
infinitely many source-generated recipes is asserted in this section.

### Existing Oracle reduction refutes a naive family invariant

Consider constructed Oracle owner rows s,u with lowers `C@I` and
`C@P_i[io]`, C=Row(io), and a retained recipe that has the two equations
above with outgoing `P_i^k[Empty]`. This is an owner-level falsifier; a complete
weighted source execution of it has not been obtained.

`row_effect::add_unweighted_effect_row_upper_bound_from_existing_lowers`
matches only alias-neutral weights: no left filter and no active PUSH count.
The neutral C@I consumes the io head; C@P_i[io] cannot match. The optimized
remaining upper `effect_row_upper([],gamma_rho)` is gamma_rho directly.
Initial unmatched replay enqueues the original C and unchanged P_i[io]
against that gamma. Future-lower routing repeats the same alias-neutral test
and directs a later unmatched weighted lower to the current reduced upper.
Hence this actual owner path yields

```text
C <= gamma_rho @ P_i[io]
gamma_rho <= u @ P_i^k[Empty]
ordinary replay tries P_i[io] composed with P_i^k[Empty].
```

`LeftStackWeight::push_entry` calls `merge_same_id_family` before count
composition; both family fields are present and disagree. Its debug assertion
fails; release selection retains the left io family. Thus a premise that all
active same-ID families remain equal is false for these constructed owner
transitions. A naive invariant that gamma sees only head-complement families
is also false: the unmatched weighted route preserves its intact family.

This route needs no independent gamma ingress, recipe coalescing, or intrusion.
It is concrete evidence against that proposed ownership invariant, not a
source counterexample to the whole language or a proof that the replacement
family algebra cannot exist. The corrected formal/provider/consumer supplies
the source topology to test once its contextual constructor and freshening
exist. Claiming it already executes would hide precisely the missing bridge.
Deleting the unmatched route requires a semantic argument preserving
independent surviving contributions; equal family spelling supplies none.

## 8. Source/proof review and dependency boundary

This producer ran no Cargo/rustc, compiler probes, algebra probes or Git
mutations. It read the primary's existing executed direct-source inventory.
The primary owns focused tests for the Rust delta, rollback accounting,
final checks and exact final status counts, recorded in §9. Results must be recorded from
those executions before any implementation completion claim. This note's
proofs do not convert pending tests into passes.

The new test packet `candidate_formal_effect_polarity.rs` targets double flips,
closed-row own/foreign operation checks, mixed tails after independent uses,
omitted/symbolic compatibility, positive argument-effect ports, and continued
negative concrete/empty refusals. Their intended coverage is the delivered
covariant cut, not execution of §4's negative contextual recurrence.

Read set: root AGENTS; research-lab, design-authority and orchestration-budget
rules; current/research task entries and design index; annotation hygiene,
residual owner design and lineage selection; the three unpublished source
drafts; local covariant, mixed allowance, root computation and paired formal
records; directional source/capture theory; HIR source_annotation; solver
candidate_source/effect/extrusion/scheme/intrusion and typed dispatch; the
new polarity test; corrected direct fixtures and inventory output; integrated
local-recursion diff, historical bridge correction and unapproved attachment
proposal. The historical row-reduction/weight owners in §7 were checked
directly in scratch `mixed_independent_bridge/row_effect.rs` and
`directed_weight.rs`, against the supplied pinned-source derivation. No new
Oracle execution ran.

Direct code dependencies for final synchronization are
`crates/yu-solver/src/candidate_source.rs`, `candidate_effect.rs`,
`candidate_extrusion.rs`, `candidate_scheme.rs`, `candidate_intrusion.rs`,
the typed endpoint/Function dispatch in `crates/yu-solver/src/lib.rs`,
`crates/yu-hir/src/module/source_annotation.rs`, `module/local_source.rs`, and
`crates/yu-solver/tests/candidate_formal_effect_polarity.rs`. The reviewed proof
dependency is the integration baseline above; final code hashes and executed
verification after the test/lifecycle repairs are recorded in §9.
Changes to formal variance, Support/Allowance consumers, kind transport, or
the direct fixtures invalidate their proof dependency and require a scoped
recheck. Unrelated branch movement does not.

Remaining concrete work is one coherent seam: retain negative-position
attachment/filter/POP owners, carry their exact contexts through actual
scheme use, implement phase-aware sorted Effect replay and indexed residual
feedback with lineage/current-future fan-out, and execute the corrected
provider/consumer trace including the family-mismatch path. The requested
`(int -> ['b, io] 'c) -> int -> ['b] 'c` callback scheme, run_io residual behavior,
independent effect preservation and returned-function use remain end-to-end
hygiene obligations. Complete Call, ordinary inference, soundness, required
principality and production migration are not completed by this local cut.


## 9. Primary integration and executed verification

The production subtransition and this source consolidation were reviewed in
M2 by two independent reviewers: source/semantic correspondence and
lifecycle/resource ownership. The latter found an accepted test-accounting
defect: the old formal-storage witness assumed no views. The repair retains
independent accounting of names, allowed-vector capacity and evidence. Its
delta review closed that finding. Source review found no blocking or major
claim defect; the final minor fixed-phase clarification above names all member
keys and excludes further copy allocations.

Actual tests also exposed an incorrect new test invariant, not duplicated
production ownership. A paired formal first records the checking port's
Allowance. Ordinary reciprocal formal replay propagates it to the exposed
port as well, yielding two distinct `(source, view)` incidence records. The
independent lifecycle review derived this from the owners before the test
expectation was repaired. The new witness now compares incidence to exact
Allowance-bound owners, traverses the shared tail bucket, verifies mapped
source/view relations after two independent freshenings, and asserts rollback
plus retry at each injected publication failure. No pre-existing test
expectation was changed.

Root verification ran on `3b263e110074cb17a04cae0b1eb529d879595e0f` plus
this patch, using Rust/Cargo 1.99.0, offline locked dependencies, one Cargo job,
no incremental compilation, no debug information and one codegen unit. The
initial multi-unit builds produced zero-length objects and failed linking;
those failures are not counted as passes. Single-unit recompilation and all
listed executions completed successfully.

The test invocations, with the toolchain's `cargo`/`rustc` selected and its
offline dependency cache available, were:

```sh
export CARGO_INCREMENTAL=0
export CARGO_PROFILE_DEV_DEBUG=0
export CARGO_PROFILE_DEV_CODEGEN_UNITS=1
cargo test --locked --offline -p yu-solver --features shadow-apply-candidate --lib formal -j1 -- --test-threads=1
cargo test --locked --offline -p yu-solver --features shadow-apply-candidate --lib candidate_effect::tests:: -j1 -- --test-threads=1
cargo test --locked --offline -p yu-solver --features shadow-apply-candidate --test candidate_formal_effect_polarity --test candidate_annotated_function_formals --test candidate_effect_annotation --test candidate_local_self_recursion -j1 -- --test-threads=1
```

| Target/filter | Passing tests | Evidence |
| --- | ---: | --- |
| `--lib formal` | 12 | paired formal storage, failure hooks and existing symbolic/deferred flow |
| `--lib candidate_effect::tests::` | 23 | allowance ownership, copy/capture/future lower, intrusion splicing, rollback and new formal view use |
| `candidate_formal_effect_polarity` | 6 | selected variance and actual own/foreign operation source cases |
| `candidate_annotated_function_formals` | 10 | existing paired/symbolic formal source behavior |
| `candidate_effect_annotation` | 17 | existing annotation/source/future-lower behavior |
| `candidate_local_self_recursion` | 5 | incoming remote's local recursion compatibility |

There are **66 distinct passing tests**, or 73 executions in this table because
seven formal tests also occur in the effect-owner group. Eight tests are new
(six source and two owning unit tests). These are focused correctness checks,
not benchmark samples, a whole-workspace test, an Oracle execution, or proof of
negative contextual inference. The existing `AtomicU64::fetch_update`
deprecation warning under this toolchain remains; switching to the newly named
API would change compatibility with older compilers, and no minimum compiler
version change is selected by this patch.

Final frozen code SHA-256 values:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_effect.rs` | `30b9bc5df7bac34cdb013961e8fff84d0bac82fb0e0496072b88c1dd63984e98` |
| `crates/yu-solver/src/candidate_source.rs` | `b9c368ec7bee9212beff17904b7975e1a37dd2b567fde0e2af140ec32114c10c` |
| `crates/yu-solver/tests/candidate_formal_effect_polarity.rs` | `dc89def4c2653960e29474135d4e2f91c076bd8a27eb54b048088820a915d636` |

The new constructor reuses the existing executable Support/Allowance views and
ordinary bound owner; it adds no context solver, residual recipe, annotation
subtraction grant or early provider resolution. Concrete negative formals
remain unsupported in the private candidate. The principal user task is
therefore **not complete**. No unresolved theorem is promoted to CLOSED, and no
public/default `yulang3` F5 cutover is made.

Before publication, remote advanced to
`5fc8acfc0384e753c4ea089af5b15766233ab5ce`; its Catch source-bridge audit and
shared status update were fast-forwarded without code changes. The tested
source hashes above therefore remain exact. That audit independently confirms
that parser/HIR arm ownership and the contextual handler consumer are still
missing from the end-to-end `run_io` route.

A further documentation-only remote advance to
`1d5d8e75e0a2439a4f2d7803d5b8d701cb511627` was also integrated. It records
the user-approved private contextual carrier/two-cycle gate and an unapproved
ordinary-HIR carrier proposal. The approval is preserved; this covariant patch
does not implement that separate carrier, defer a formerly supported result,
or broaden negative-formal admission. No tested code dependency changed.
