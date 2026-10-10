# Local recursive extrusion: source topology and reference closure

Status: research-only characterization and conditional closure derivation;
accepted scheduling repair independently delta-reviewed; no remaining blocking
or major finding within the stated source/scheduling scope.
Frozen compiler baseline: `acc9a9d1d4c290a3ff17cf45fd1093bcab957167`.
Scope: ordinary source-directed lower-copy topology, followed by an explicitly
defined complete weighted reference saturation. The full contravariant effect
handling task remains **UNSOLVED**.

## 1. Exact source and observed boundary

The negative fixture is:

```yulang
act io
my outer sink = {
  my witness (cb:int -> [io, 't] ()) = {
    my checked: int -> [io, 'u] () = cb;
    my ignored = sink witness;
    checked
  };
  witness
}
```

The symbolic-formal control changes only the formal callback row:

```yulang
act io
my outer sink = {
  my witness (cb:int -> ['t] ()) = {
    my checked: int -> [io, 'u] () = cb;
    my ignored = sink witness;
    checked
  };
  witness
}
```

Exact inputs: scratch `source_context_witness/local_recursive_extrusion_negative.yu`
and `source_context_witness/local_recursive_extrusion_control.yu`.
Primary execution evidence: `source_context_witness/inventory-local-recursive-extrusion-output.txt`,
using the latest compiled libraries at the frozen baseline. Both parse with
zero recoveries and produce LocalSource with 10 expressions and 3 bindings.
Negative: `CANDIDATE unavailable=Unsupported`. Control: `solved=true`,
`conflicts=[]`, `source_calls=1`. HIR placeholder diagnostics and ordinary
solver results are separate evidence, not successful negative candidate execution.
The control also reports unresolved candidate obligations; its success is not
complete Call, soundness, principality, or public-cutover certification.

The source preflight deliberately rejects this negative concrete formal row
(`candidate_source.rs:56–90`); the formal constructor also lacks that branch
(`candidate_effect.rs:998–1014`). This note does not enable it.

## 2. Implemented source derivation

All code locators below are relative to `crates/yu-solver/src/` at the pinned
baseline. Subscripts denote levels, not runtime row IDs.

`candidate_source.rs:207–258` starts the outer source at level 1, keeps a
lambda's parameter/body at its level, and visits block initializers one level
deeper. Consequently sink is at 1, witness and cb/formal `t` at 2, and checked's
annotation plus scoped `u` at 3. Checked's initializer still denotes the
monomorphic cb Parameter at 2. The annotation is checked before ignored's
application; witness's Lambda publication follows its body actions
(`:229–239,270–280,373–387,485–509`).

The active initializer map survives the whole witness initializer. The recursive
name uses `Action::Link`, rather than published-local scheme instantiation
(`candidate_source.rs:253–262,331–340,490–493`). With witness's initializer
Value `w2` and recursive reference expression Value `x3`, this supplies
`w2 <= x3`. Level-directed owner selection stores `w2` lower at `x3`
(`candidate_extrusion.rs:684–699`). There is no presumed level-0 export.

`shadow_apply.rs:1327–1358` makes the demand for `sink witness` a negative
Function with positive argument `x3`. Comparing it with sink at 1 negatively
extrudes the demand to 1 (`lib.rs:11866–11885`). Function argument traversal
flips polarity, so it visits `x3`, then its selected lower `w2`, Positive at 1
(`candidate_extrusion.rs:95–162,224–248`). Positive extrusion allocates copies
`x1,w1` and installs the source link `w2 <= w1` upper at `w2` before witness's
Function lower is published. Rows are memoized before selected bounds are visited.

The later Lambda publication admits a Function lower at `w2`; ordinary apply
insertion replays against the retained upper `w1`
(`lib.rs:11117–11130,11190–11210`; `candidate_extrusion.rs:698–699`). Its Function
argument is the retained formal domain `B-`, not an invented use-time scheme.
Positive extrusion of this Function flips `B-` to Negative. The callback's result
Effect preserves that polarity, so the control's original `t2` is copied to `c1`.
The actual negative-copy constructor installs:

```text
C0: c1 <= t2 @ I                      // lower at t2; level(c1)=1 < 2
```

Here `@ I` describes the ordinary identity skeleton, not an existing Rust context
field. This lower is installed directly by `Work::Visit` at
`candidate_extrusion.rs:121–123`. Section 4 records the essential scheduling limit.

Checked's negative annotation demand is extruded from 3 to cb's level 2;
its local facade `q3` and scoped tail `u3` become `q2/u2`. Its original formal
Function positive side at cb2 does not need copying. Current signature construction
places an Allowance upper behind this facade
(`candidate_effect.rs:1061–1100,1325–1449`; `candidate_extrusion.rs:258–291`).
The checked annotation is covariant. It supplies no subtraction attachment ID.

## 3. Explicit reference extension and short closure proof

This section defines a conditional reference object, not an executed candidate.
Suppose authentic negative Stack/Filter/POP construction and its extrusion
transport produce the following stored relations on the source-directed skeleton:

```text
S: t2 <= t2 @ P_i[H]                  // upper at t2
T: t2 <= q2 @ P_i[H]                  // upper at t2
A: q2 <= Allowance(H,u2) @ I          // upper at q2
H = {resolved io};                    // one attachment occurrence i
```

`P_i[H]` denotes the selected one-ID left PUSH with the actual family/filter data;
`I` is identity. The same authentic `i` must survive extrusion. In particular,
the future Filter wrapper must transport its referenced `t2` through the Negative
traversal just derived. No current wrapper implementation is claimed here.

Define **complete reference saturation** as the least relation closure containing
`C0,S,T,A` in which every retained lower/upper pair at an owner is replayed in its
recorded order, including pairs introduced by direct extrusion insertion. Use
directed mix at each such node, exact contextual identity, and the existing
level-selected storage orientation. Nonidentity self `S` is retained with its
checks/consequences. This definition requires pair activation; it is stronger
than merely putting a context field on the current worklist or storing `S`.

For this selected derivation there is no right debt, no Function swap/both after
the seed, and no shared-child operation. Fixed replay bracketing gives
`mix(P_i^k[H],P_i[H])=P_i^(k+1)[H]`; replay with `I` preserves that value.
The actual `H` passes these local family/filter checks.

Induction now yields, for every natural `k`:

```text
Ck: c1 <= t2 @ P_i^k[H]              // lower at t2
Dk: c1 <= q2 @ P_i^(k+1)[H]          // lower at q2
Ek: c1 <= Allowance(H,u2) @ P_i^(k+1)[H]
```

Base: `C0` is the identity seed. Step: Cartesian replay of `Ck` with `S`
produces `C(k+1)`. Since `level(c1)=1 < level(t2)=2`, owner selection keeps it
lower at `t2`. Replaying `Ck` with `T` produces `Dk`; the same strict comparison
keeps it lower at `q2`. Replaying `Dk` with `A` produces `Ek`. Thus the complete
reference closure has infinitely many distinct incoming Var-to-Allowance histories,
distinguished by active count. An exact finite enumeration of those histories
cannot represent that closure. Upper-only storage of `S` does not exclude this
lower-copy topology. Neither conclusion proves divergence of the current worklist.

The P-only ray is already represented by the existing exact acceleration
`p=0,n>=0`: see [recursive PUSH results, §§4–5](2026-10-10-recursive-push-results.md)
and [approved admission design, §5](../design/2026-10-10-contextual-attachment-admission-design.md).
This note adds no universal mixed-component theorem. It does not establish that
the current compiler recognizes this complete component as a certified circuit.

## 4. Accepted scheduling repair: storage does not activate the pair

The initial `c1` lower arrives after checked's facade obligations (and, in the
reference extension, `S/T`). The source constructor creating that lower calls
`candidate_insert_bound` directly (`candidate_extrusion.rs:123`). Copy initialization
`Work::Bound` likewise calls it directly (`:307–321`, insertion at `:313`).
Neither site calls `candidate_replay_bound`.

`candidate_insert_bound_impl` (`:400–529`) journals and stores the selected side,
records origins/capture information, and marks intrusion dirty. It does not
enqueue the opposite Cartesian pairs. Actual replay is explicit at
`candidate_replay_bound` (`:635–673`), ordinary apply (`:698–699,730–731`), and
intrusion after a real merge (`candidate_intrusion.rs:590–595`). Dirty marking
alone is not such a merge or an unconditional replay sweep.

No established later event activates `C0 × S/T` on this source route. This is
a missing enqueue event, **not worklist unfairness**. Adding weighted fields and
retaining `S` alone does not supply it. Therefore this artifact withdraws any
implication of current-worklist nontermination or an executed negative source
counterexample. Only the complete reference closure in §3 is infinite.

The immediate dependency orientation also supplies no qualifying `t2/c1` SCC:
the lower copy contributes `t2 -> c1`; `Dk` contributes `q2 -> c1`; the consumer
incidence can contribute `c1 -> u2`. Original `t2` reaches `q2`, and copies reach
their own lower-level descendants. This selected route provides no reverse path
to original `t2`. The callback has no nested payload returning to that Effect.
Both bound sides contribute owner-to-bound dependencies
(`candidate_intrusion.rs:382–429`); equality requires an actual recorded pair
in one SCC (`:471–484`). Recording the parent pair alone cannot erase `C0`.
Future weighted/residual edges still require their own SCC check.

## 5. Consumer bottleneck, authority, and frozen checks

Distinct reference `Ek` do **not** imply distinct allocated gamma recipes. Current
`candidate_apply_effect` treats a Var lower and Allowance upper as an upper bound
at that Var (`candidate_extrusion.rs:718–731`); it does not dispatch that task to
the atomic member checker or a weighted residual constructor. To establish actual
residual lineage, the owning consumer must retain each required contextual history
and its constructor identity/correlation, either separately or through an exact
symbolic indexed family. Wrapper transport and initial pair activation must first
be supplied. This is the minimum bridge missing from the reference obligations
to full source-generated handling; no new solver, cap, or semantics is selected.

The admission design is **Authoritative** for its private carrier and two-circuit
gate. That approval is preserved; it does not certify current recognition,
arbitrary concrete-formal admission, general mixed closure, or complete handling.

Checks: read-only inspection of source actions, Apply/Lambda construction, extrusion,
insertion/replay, facade construction and SCC owners; reused the primary's frozen
parser/control inventory. No new build, probe, execution, Git mutation, production
edit, or shared-record edit. Only this leased note was written. Input scratch
`source_push_owner_closure.md` §7 was used; its withdrawn §§1–6 are not evidence.

Primary integration: the source/topology review and scheduling delta review were
read-only. The latter closed the accepted major distinction between complete
reference saturation and the missing actual seed enqueue. No code changed after
the 66-test covariant checkpoint at `acc9a9d1`. This record adds no test pass,
negative execution, general termination theorem, or CLOSED promotion.
