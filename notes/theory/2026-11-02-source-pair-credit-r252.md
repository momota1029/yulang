# R252: finite constructor templates and the receiver-ancestry equation

Revision 1. **Candidate static source-native derivation; entry-only productive-pair bound NOT ESTABLISHED.**
Sole author `/root/sol_r252_source_pair_credit`; no descendants or coauthors.
Contract `tasks/agent-loop/sprints/source-pair-credit-r252.md`, SHA-256
`c54b7c3da6e93e358b410569d628369a4b7a6e51759e4015dd761fd65d7cd057`.
Admission SHA-256 `dbe5916ce12db3f53c875b873538b6bd8a74cd57c8a38f8e5aea3e31b805ceaf`.
Frozen baseline `e6aadca4b4cec57da2e614db4f016bbe301dc3d5` matched by reading
HEAD/ref files, without a Git command. All 20 contract pins matched before
their bodies were read or cited. Independent review belongs to Luna.

## 1. Unchanged parent and exact outcome

The parent is Yulang inference soundness and its Rust implementation, with
the original accepted source domain, Simple-sub A/B, independent satisfying
assignments, shared witnesses, F1/FK1 and foreign continuations unchanged.
Immediate edge: `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1` / `R70-DRAIN-1` /
`NEWPAIR251`. Use R250/R251's successful forward initialized-session domain,
including finite successful prefixes producing diagnostics. Do not assume
eventual queue emptiness or drain return. Inherited R70 entry W and source
authenticity obligations remain premises, not consequences of this analysis.

There is a finite entry set of **row-erased Value constructor templates**.
Keeping exact raw row leaves gives a finite-prefix polynomial bound on
productive full pairs in the physical row population. Projecting those leaves
to strict parent-birth ancestry makes the descriptor carrier entry-finite,
but its uniform fiber bound is unproved. Adding receiver ancestry restores
more provenance but introduces same-level dependencies. Sections 4 and 5 give
the actual constructor equations and their guards, including two different
owners of those dependencies; they are more specific than asking for a new
unused credit.

No accepted source prefix repeating a proposed credit, candidate-map
collision, infinite execution, production defect or need for global sharing
is claimed. These equations are source-code transition laws under their
stated guards; no particular source program realizing their combined
antecedents is supplied. The result is not a source-qualified counterexample.
The entry-only bound on C remains OPEN; semantic parent/A/B delta **0→0**.
Lean declarations, kernel theorem types and axiom dependencies: NOT APPLICABLE;
checker NOT RUN under the explicit no-Lean contract.

## 2. Source entry and finite constructor support

The entry is one actual typed drain, after its supplying source constructor
has formed the initial task. The source frame does not execute another action
while this synchronous drain runs. Thus Lambda-created rows/functions before
this entry are entry data, not births inside its row account.

| Owner | Exact source-to-drain construction |
| --- | --- |
| source:2481 | Fact calls `admit_collected_fact`; lib:11546–11591 admits the stored occurrence/provenance, translates same-kind endpoints, and calls the typed constrain route. |
| source:2482–2492 | Link translates its CandidateEndpoint and component target; ValueConstraint translates its lower endpoint and retains its stored upper. Both use `admit_candidate_value_link` with the actual occurrence/slot. |
| source:2493; lib:11620–11821 | Lambda constructs its actual four-port Function, including argument and both effects, admits Function-to-root occurrence slot 2, then enters the same drain. Its earlier effect drains are separate entries. |
| lib:14096–14109,14340–14366,14447–14474 | Candidate typed route executes Transport, Context, then Dispatch on the retained task/relation. These checks precede endpoint memoization and extrusion. |

This uses constructor positions as provenance, not source labels as consumable
credits. Graph Apply events are appended at graph:332–345; qualification reads
the sealed components. Source union at context:3514–3538 preserves finite
support. Neither operation decrements a credit or bounds its uses.

Fix entry storage sigma0. Expand each visible entry structural Value term
as a finite ordered tree under W, stopping at Component/LiveVariable leaves.
Keep constructor tag/sign, Function's four port names/kinds, tuple index,
record field name/requiredness/order, and variant alternative/tag/payload index.
Keep nonrow leaves exactly. Replace each row leaf by a hole annotated with its
kind and sign. Let T0 be the finite set of resulting templates, including
templates of structural subterms. Choose one fixed entry witness for identical
templates. An entry witness is a descriptor choice, not equality of compiler
Terms. Let T=|T0|, n=max internal constructor occurrences per template and
h=max row-hole occurrences (zero maxima if T=0). Let A be the number of all
entry-visible term handles, including row-leaf and nonrow-leaf handles.

The following induction uses the current bytes, not R70's historical line
numbers:

1. Extrusion visits existing children: Function flips Argument/ArgumentEffect
   and preserves ResultEffect/Result (extrusion:293–340); Tuple/Record/Variant
   retain their ordered selectors (:225–288). Row Visits stop or allocate a
   same-kind leaf; following a row bound discovers another stored term, not a
   constructor wrapped around the row in the current template.
2. Reconstruction uses the same constructor and metadata and the mapped
   children (extrusion:413–575). An unchanged child retains its original Term;
   a changed child reifies a row or structural endpoint (:597–619). The
   reifier is partial: success is required, and an unsupported changed effect
   view is not silently converted into an invented term constructor.
3. Bound copying and Parent merging store/transport existing endpoints;
   they do not substitute a bound's structure into a row leaf of another
   term (extrusion:395–412,702–875; intrusion:632–710). Replay selects its
   lower/upper endpoints (extrusion:1070–1112). Structural dispatch selects
   existing children (lib:14905–14947,15059–15161). Therefore these steps
   select an existing template or its entry subtemplate, and do not grow a
   template by unfolding recursive bounds into term syntax.
4. Value/effect canonicalization redirects top-level row endpoints only;
   `canonical_value` (lib:11925–11932) leaves structural Term handles intact.
   Child translation can canonicalize the row read at a leaf without
   changing the template. Context transport/rewrite changes relations and
   queue entries, not Value constructor shape. Effect Support/member/tail
   expansion (effect:1606–1673) creates no Value constructor.

The Value constructors elsewhere in the pinned effect owner (for example
effect:1447–1448,1844–1845,1876,2094–2095,2607–2669) belong to source signature,
formal/annotation or endpoint construction, outside this admitted drain SCC.
They are not silently allowed to run during this induction. The scope here
is the same SCC as R251, not every constructor in the compiler.

Consequently every structural Value endpoint encountered in this drain has
a template in T0. This is finite **shape support**, not finite Terms, pairs,
relations, ContextExprs, fibers, invocation counts or physical bound slots.

## 3. An exact descriptor bound parameterized by raw rows

Retain all raw identities. Let q_t=P0+B_t be physical kind-qualified rows
allocated by a finite successful prefix; merged rows remain in this count.
At each hole record either its retained entry row-term handle or its actual
LiveVariable `(kind,sign,raw ordinal)`. At most A+4*q_t+1 choices suffice;
the extra one only makes the zero-size case harmless. The template already
checks kind/sign, so this deliberately overcounts.

To avoid an interning assumption about collected versus live handles, annotate
each internal constructor occurrence by either its exact entry handle, or
`new` when its Term was first allocated after entry. There are at most A+1
choices per occurrence. Recursively, a `new` node's exact tag/metadata and
exact child handles determine at most one post-entry Term: `with_term_events`
uses the same branch arena (lib:10659–10690), whose `intern` retains exact
TermNode→Term entries (term:1166–1203). Entry handles remain explicitly
distinguished. No assumption that equal row-erased syntax has equal identity
is used. No failed-route rollback/resume or branch replacement is admitted.

By induction on the finite template tree, this annotated descriptor determines
at most one exact endpoint. Thus, with

```text
U(q) = T * (A+1)^n * (A+4*q+1)^h,
```

the number of structural Value endpoints observed by prefix t is at most
U(q_t). A productive full original pair has exactly one structural endpoint
and one receiving ValueRow: atoms cannot allocate a row in the local Visit,
and Function/Function dispatch decomposes before the extrusion branches.
Direction and receiving raw ordinal give the candidate finite-prefix lemma:

```text
TEMPLATE252(sigma0, successful valid finite SCC prefix t):
  C_t <= 2*q_t*U(q_t),     q_t=P0+B_t.
```

The hypotheses include W's relevant structural/identity conditions at the
actual calls. This is a static inductive source argument, not a checked Lean
declaration or an all-source proof of W. The descriptor's fiber is at most
one at fixed raw identity; replay relations with different contexts/sources
can share a pair without being identified as relations. Equality retains old
raw term leaves/handles; counting all physical rows rather than current
representatives covers those historical leaves and earlier canonical keys.

This lemma removes arbitrary structural growth as an independent carrier
problem. It does **not** remove B_t from the descriptor alphabet. In
particular, inserting R251's inequality yields only a self-dependent pair
inequality, not a bound obtained from entry storage.

## 4. Entry-finite parent words and the first receiver equation

Reuse R251's ghost labels: entry rows have entry level, fresh rows have their
allocation level. Merge only lowers current levels. The finite entry alphabet
J has d levels, and every raw Parent birth strictly decreases its label.
Describe a row by its entry raw ancestor followed by `(polarity,target)`
along raw Parent edges. There are at most `D=P0*3^d` such words (a coarse
bound: choose decreasing target levels and one of two signs per edge).
Kinds are inherited from the entry ancestor. Descriptors for retained entry
row terms still distinguish their fixed handles; fresh live leaves can use
these parent words. Therefore projecting §3's raw leaves and receiver to
parent words really gives an entry-finite carrier, for example of size at most

```text
2*D*T*(A+1)^n*(A+4*D+1)^h.
```

There is no derived bound on the projection's fibers: two invocations can
have the same parent/sign/target word and different receivers. This note does
not assert that any particular accepted trace realizes such a collision.
Encoding the receiver recursively is the next natural construction, but its
dependency has a different level equation from the Parent edge.

Here is the first concrete source-construction equation, using **Value** rows.
For a successful deep Visit of parent r at level H>L producing c at L:

```text
p=Positive: Parent(c,r,+,L),  install BoundKey(r,Negative,c)
p=Negative: Parent(c,r,-,L),  install BoundKey(r,Positive,c)
label(c)=L;  current_level(r)>L;  original receiver x has current_level(x)=L.
```

This is extrusion:96–185, with Parent/sources/comparison from intrusion:306–343.
The source link has an executable fiber: effect:890–917 chooses
`candidate_context_extrusion_link` in scoped mode (ordinary bound construction
in unscoped mode); context:4314–4358 retains the actual processing parent,
post-check context and source set and attaches the resulting relation.
Value extrusion links reset their scoped payload to the default at
context:3471–3472; this does not erase their dependency/source provenance.

The physical source-link insertion itself performs **no opposite replay**.
It does not immediately emit `(T,c)` merely because an old T is a lower of r.
If a later actual `candidate_replay_bound(r,Positive,T,...)` observes that
upper link, however, its exact constructor equation is:

```text
lower_input=(r,Positive,T), upper_input=(r,Negative,c)
task=(T,c)
child_relation=Relation(task,
  Replay(stored_context(lower_fiber),stored_context(link_fiber)),
  union(actual source labels), actual composed scoped payload)
dependency=Replay(child_relation,lower_fiber,link_fiber,lower_input,upper_input).
```

Both identity contexts take the actual identity shortcut. The negative dual
replays `(r,Negative,U)` against `(r,Positive,c)` and produces `(c,U)`.
Owners: extrusion:1070–1112 and context:4411–4497. This requires both actual
fiber inputs, a successful payload composition and a frontier/dependency not
already suppressed by the ordinary replay checks. It is not derivable from
endpoint shapes or an origin table alone. Subsequent Transport/Context,
canonicalization and the full-pair memo/rewrite guards still execute before
any birth. If c is merged before dispatch, use its actual representative/key;
the unmerged equation cannot be applied by pretending c survived unchanged.

When one of those emitted tasks is productive, its target is the current
level of c, namely L before any merge. A descendant born in that invocation
also has label L. A description recording receiver ancestry therefore has
an L→L edge even though each of its raw **parent** edges strictly decreases.
The missing equation is not a second proof of raw birth depth: it must bound
how often these actual source-link fibers become receivers of newly productive
root-template tasks across replay snapshots. Labels alone do not do that.

## 5. Independent structural-selector equation at the same level

A receiver can also enter the next productive pair through an ordinary
Function port, without replaying its parent r's source link. This rules out
using a bound solely on the source-link route to certify the combined map.

Use the following guarded equation; other ports retain their actual kinds,
signs and identities. Suppose a productive canonical pair `(F+(...,r),x)`
has x at L and the positive result row r above L, and the successful local
map gives c at L. Its rewritten structural endpoint is `F'+(...,c)`.
When that rewritten task is actually applied as a lower of x, and x's
actual opposite snapshot has `U-=F-(...,S)`, replay emits `(F',U)`.
If this comparison passes Context/memo guards, Function Result dispatch emits
exactly `(c,S)`. If S is a nonrow negative structure with a deep visited row
s above L, this is the negative extrusion branch and it produces d at L:

```text
(F+(...,r),x_L)
  -- successful Positive extrusion / full-pair rewrite --> (F'+(...,c_L),x_L)
  -- actual x-bound replay against F-(...,S) --> (F',F-)
  -- FunctionField::Result --> (c_L,S)
  -- successful Negative extrusion --> d_L from a deep row s in S.

raw parent edges: r -> c has strict label decrease; s -> d has strict decrease.
receiver edge:    c -> d has label(c)=label(d)=L.
```

Owners: rewrite lib:14814–14866; apply/replay extrusion:1115–1138,1070–1112;
Result pair lib:14934–14947; actual port admission/enqueue lib:15059–15088;
negative extrusion lib:14830–14840. The parent comparison and exact Function
port dependency are retained, rather than inferred from a matching row.
The other three Function ports remain present, including both effects and
contravariance of Argument/ArgumentEffect. They can independently add work.

Each displayed arrow is conditional on its actual production guard, valid
inventories, successful helpers, queue processing, replay fibers and unchanged
representatives at that arrow. No scheduling assumption manufactures the
arrows, and no accepted source witness for the whole diagram is claimed.
There is no assertion of repeated credit. This is the source's exact equation
that a proposed ancestry proof must handle, not an abstract transition invented
to test it.

This route consumes a structural selector of U. Finite templates bound one
uninterrupted selector descent. They do not yet bound the number of returns
to template roots via selected row bounds and the replay equation in §4.
Thus a receiver-inclusive descriptor needs a justified bound on its combined
selector/replay ancestry, not merely the finite number of selector names.
No theorem ruling out such a bound is claimed.

## 6. Merge/rewrite fibers and application to the unchanged edge

Retained full-pair rewrites persist across equality generations by R251.
They cap successful birth invocations for each **exact original pair** at one;
they do not key on §4's projected words. Recapture activates existing groups
and allocates no rows (intrusion:386–420). Merge appends both bound sides,
transports actual fibers, redirects copy to parent, takes minimum levels,
canonicalizes captured keys and replays merged lowers (intrusion:632–710;
context:4649–4673). It may alter the canonical receiver key but never erases
historical raw structural Term handles. No equality quotient is applied here.
R71 raw/canonical fiber coverage remains separate from the endpoint count.

If Luna later supplies a uniform fiber multiplicity m for the entry-finite
projected descriptor carrier K0 above, then the actual application is:

```text
C_t <= m*|K0| = Cbar
B_t <= P0*(3^Cbar - 1)                     (R251)
M_t <= max(0,R0+P0*(3^Cbar-1)-1)           (R250/R251)
```

Equality generation advances once per genuine merge. No extra generation
factor is needed to pay for a fixed exact pair. That application is presently
conditional because m has not been supplied by the source construction.
The unconditional finite-prefix combination currently justified is only

```text
C_t <= 2*(P0+B_t)*U(P0+B_t),
B_t <= P0*(3^C_t-1),
M_t <= max(0,R0+P0*(3^C_t-1)-1).
```

These inequalities cannot be rearranged into a uniform upper bound: their
right sides grow with the quantity to be bounded. Hence no global generation
bound, eventual Diagnostics entry or terminal return follows. R250's finite
settlement/Diagnostics suffix lemmas retain their actual phase-entry premises.
Even a future pair/birth bound would leave relation/context/fiber closure and
valid diagnostic references/reports to their own proofs.

Before/after: R251 left a bare finite-pair credit construction. R252 constructs
finite template support and an injective raw descriptor bound, then identifies
the exact same-level receiver constructors where its entry-finite projection
still needs bounded multiplicity. Parent closure remains OPEN. This is a
source-construction reduction, not a renamed conditional termination theorem.

## 7. Mutual TODOs and authority boundary

`R252-RECEIVER-ANCESTRY-1`, owner Luna's source/proof lane: establish a uniform
entry bound on the combined receiver ancestry generated by (a) actual
source-link fiber exposure at bound replay and (b) Function/other structural
port selection after rewritten-bound replay. Required input: this fixed
source SCC, R251 raw birth labels/exact-pair retention, actual ordered replay
dependencies/heads and exact template witnesses. Proposed output: a finite
receiver/selector/replay descriptor with bounded raw-pair fibers, or one
particular accepted finite source prefix refuting its claimed multiplicity.
First missing source equation: preserve a bound when §4 exposes a newly
retained receiver link or §5 enters `(c_L,S)` and later selected-bound replay
returns to an entry template root. Owners: `candidate_extrude` source-link /
Work::Bound, `candidate_replay_bound`, `candidate_context_begin_replay`,
`dispatch_live_item` Function Result and actual port-admission consumers;
merge/canonicalization is an additional transition, not a free identity.
Falsifier: a fully admitted prefix exceeds that proposed multiplicity through
one of these guarded arrows, with exact input fibers, receiver, processing
relation, rewrite state and before/after representatives retained. A synthetic
cyclic graph, finite label collision without a source prefix, or resource
exhaustion is insufficient.

`R252-REVIEW-1`, owner Luna: fresh independent review of finite-template
coverage, raw interner tags/counting, same-level receiver equations and their
guards. The producer cannot independently certify this result.

Implementation **NO_SAFE_CODE_SLICE**: inspected dispatch/rewrite, extrusion
physical constructors and replay/merge owners expose a proof boundary, not a
concrete accepted-source violation of an approved clause. No production edit
or instrumentation is requested. A later evidenced violation needs its exact
first owner, falsifier and Luna's admitted code slice.

R70 W, R71, evidence authenticity/association, diagnostics, F1/FK1, foreign
continuations, full soundness, hygiene, qualifying intrusion and generalization
remain separate. No provider/residual/witness lineage or independent quantifier
is collapsed. Reused R70 only within W/successful local operation; reused R250
finite-phase/merge accounting and R251 depth/persistent-pair bound within their
actual premises. Rejected immutable bound snapshots, global sharing, semantic
identity quotient, source labels as spent credits, and a generation multiplier.

## 8. Checks, runtime and freeze

Three substantive stages: (1) gate/source-constructor/template audit;
(2) raw versus projected/receiver ancestry and exact owner equations;
(3) R251/R250 application and frozen obstruction. Bounded static reads/searches,
read-only HEAD/ref resolution and SHA-256 only; no build/test/probe/Lean/Cargo,
Git command, nested CLI, external contact, production/config/shared-state,
quarantined/runtime or expectation edits. Initial `python` was unavailable;
the read-only hash gate succeeded with `python3`. No scratch/cache output.
Only the two leased artifact/inbox paths are new/written.

Worker `/root/sol_r252_source_pair_credit`, inherited session
`01a1873a-a93b-7dc3-a8ce-028a7b543a80`; active-work/hash receipt sent to Luna
at 2026-11-02 05:06:16 UTC. Requested `gpt-6.1-sol/high`; observed effective
model/effort UNKNOWN because no runtime metadata surfaced. Hard 2400-second
grant fully charged, no expansion/refund/carryover. Exact pre-clock/provider
active time and CPU/RSS UNKNOWN; final observed elapsed is in the handoff.
No descendants. Freeze hashes and STOPPED/WRITES_STOPPED receipt accompany
the inbox; fresh review/adjudication/integration remain pending.

## Direct dependency pins

The exact 20 pins below belong to R252's contract. R70 note authors are
`/root/r70_ordinary_extrusion_proof` and complementary trace contributor
`/root/r70_extrusion_countertrace`; its conditional result stays conditional.
R250 author `/root/sol_r250_drain_progress`; R251 author
`/root/sol_r251_birth_charge`. Reviewed R251 disposition is supplied by its
history record, SHA-256
`b9515b73f640679134e5f0b43c73764156d346fd75eadbd99d209839f71a8ef7`.
Historical source pins/claims are not substituted for current source bytes.

```text
429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be  crates/yu-solver/src/lib.rs
a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905  crates/yu-solver/src/candidate_context.rs
475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97  crates/yu-solver/src/candidate_intrusion.rs
6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e  crates/yu-solver/src/candidate_scheme.rs
bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49  crates/yu-solver/src/candidate_source.rs
80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61  crates/yu-solver/src/candidate_extrusion.rs
4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15  crates/yu-solver/src/candidate_effect.rs
d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1  crates/yu-solver/src/term.rs
4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03  crates/yu-solver/src/candidate_scope.rs
aaaa88a374083f898188cd390b8cf0244855d8c09c8939b9e68ee2831bc692cf  crates/yu-solver/src/candidate_value_graph.rs
648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7  notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md
4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf  tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md
25f6a370ae1aa2d7a623a8aa0eaede979248d85b8c03c894fbf8f7850775e8db  tasks/agent-loop/inbox/20261019-r70-proof.md
ff2c149bd71c783f874c150404bf199084858df631c21899d3abf53a258655bb  tasks/agent-loop/inbox/20261019-r70-closeout.md
a93b2e5d38c03511c768dd704e57f3b616a1dafc591fe62a4155d64a06bbf4d8  notes/progress/2026-10-19-r70-closeout.md
87e9af00bfc206fb22a29b776c634acc94e75e0283257f8bba9d513d23a90574  notes/theory/2026-11-02-ordinary-drain-progress-r250.md
8b52e40891096ca6086db636165b276a3f57630091e090e3e181f390cd178c65  tasks/agent-loop/inbox/ordinary-drain-progress-r250.md
1bc35d4749290a6a583ce079e80a95ed96c60a9ff81db06e2dfac25e74ad2af5  notes/theory/2026-11-02-ordinary-birth-charge-r251.md
8aaa7b025dd89e2f4edc0fb12ae69a9e1934ac7709c6bf719fae9a1e6c234429  tasks/agent-loop/inbox/ordinary-birth-charge-r251.md
30aea41a739866e73b6220754e05a8eb96388720046f87482714d530623cda23  tasks/agent-loop/sprints/ordinary-birth-charge-r251.md
```
