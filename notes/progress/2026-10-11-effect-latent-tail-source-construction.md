# Effect latent tail: conditional source construction of a parent/copy SCC

Status: frozen, independently reviewed research checkpoint; conditional static
source construction. The original semantic theorem and production gates remain OPEN.
Baseline: `330d5432aff4b1f9655d501e17a9eefb7e75e098`
Branch assigned by primary: `research/simple-sub-intrusion`
Exclusive lease: this note only
Method: source ownership, construction order, polarity and replay audit

## Objective and authority

Find one source construction in which the **same resolved annotation tail at
its original lexical scope** occurs in a latent Function port and in a low-row
Allowance ascent, with an actual later admission activating both directions.
Do not identify distinct AnnotationScopes by spelling. This extends the prior
Effect SCC audit's missing tail-to-parent route; it does not repeat its rank
discriminator or alter the selected graph.

Frozen governing sections:

- `2026-10-10-parent-copy-scc-intrusion.md`: Direct decision, Selected operation
  and compiler responsibility, Retained boundary.
- `2026-10-11-yulang-inference-top-level-principles.md`: §§1–5, Authority and
  integration.
- `2026-10-10-annotation-effect-hygiene-integration.md`: §1 selected polarity
  policy and variable distinction; §4 preservation of annotation ownership.
- `2026-10-08-source-generalize-definition.md`: §§2–4, full scoped relation,
  original scopes, and separate local-law/production obligations.

The operation retains genuine extrusion parents and equates a distinct pair
when the actual stored dependency graph places them in one SCC. Neither
annotation hygiene nor source Generalize supplies missing complete Call laws.
No new semantic decision or implementation authority is claimed.

## Conditional construction and exact premises

```yulang
act E
my outer sink = {
  my x (g:(int -> ['t] int) -> int) (h:int -> ['t] int) =
    ({ my ignored = sink g; h 1 } as [E,'t] int);
  x
}
```

This is a compact source-shaped witness; no global minimality is claimed.
The retained extrusion parent here is the original **formal tail t**, rather
than the invocation row r from the previous Int-only discriminator.

**Claim class:** conditional source construction, not a parsed execution,
successful complete typing derivation, established semantic theorem, or
independently reviewed result. Hypotheses are:

1. The displayed syntax lowers without recovery to the inspected LocalSource
   shape, with one resolved nullary E, outer's sink parameter, local x with g/h
   parameters, sequential ignored initialization, and the ascription around
   the whole inner block. No parser or Oracle was run.
2. Native candidate effect/source mode runs the finite ordinary actions and
   drains successfully, without availability failure or externally injected
   state. The relevant original coordinates have not previously been equated;
   an earlier qualifying merge would already satisfy operational reachability.
3. The inspected source constructors, scalar replay, and SCC graph are the
   frozen baseline implementations below. Complete Call adequacy is not an
   assumed consequence of their four native ports.

The source owners establish the scope sharing, levels, parent provenance and
later replay **under those hypotheses**. They do not independently establish
source-semantic lawfulness or accepted/public typing. Thus this is a candidate
operational witness to submit to the constructive/review lane, with execution
and semantic bridges still OPEN.

## Scope and construction owners

HIR `module/local_source.rs:332–360,757–791` assigns x's parameters to its
initializer/parameter scope spine. `candidate_source.rs:180–186` maps **both**
g and h to `AnnotationScope::Local(x.id)`. Their formal actions are emitted
before their bodies (`:270–284`). Both singleton symbolic result ports call
`candidate_formal_effect_variable(scope,"'t",level)`, whose key is exactly
`(AnnotationScope,name)` (`candidate_effect.rs:979–999,1034–1071`). Consequently
they resolve to one original row t at level 2; this is stronger evidence than
equal spelling in HIR, which retains symbolic names rather than resolved rows.

The ascription is outside the inner Block. OperatorChain lowering preserves
its incoming `Parameter(h)` scope (`local_source.rs:505–523`), which candidate
construction maps to the same Local(x) key (`candidate_source.rs:413–434`). Its
row `[E,'t]` therefore uses that existing t, despite a distinct row-position
SourceNodeKey. Views remain position-owned; equal tail does not equate views.

This placement is decisive. Writing `h 1 as [E,'t] int` **inside** the block's
final expression instead would receive `LocalSourceScope::Expression(block)`
at `local_source.rs:821–824`; its candidate AnnotationScope would differ.
That tempting first variant is invalid evidence for shared-tail reachability.

All relevant static preflight forms pass their explicit shape predicates:
formal roots have no computation row; formal effect rows are singleton
symbolic rows, with no negative concrete atom; ascription has one positive
root row (`candidate_source.rs:83–132`). Parser acceptance remains unexecuted.

The scheduler starts outer at 1, enters x at 2, installs g/h formals at 2,
then enters ignored's initializer at 3 before the final `h 1` at 2
(`candidate_source.rs:251–326`). x's actual Lambda publication follows the
body; this route needs only already installed formal Functions. Parameter
Names resolve directly to Parameter endpoints (`:210–217`). Ascription aliases
its actual child endpoints, peeling groups (`:220–234`), so its computation
check uses the inner block's effect b at 2.

## Source-to-edge trace and actual activation

Let t2 be the shared formal tail; let c1 be its genuine **negative extrusion
copy**; let r2 be `h 1`'s fresh invocation Effect; let a2 be that Apply's
computation Effect; let b2 be the inner block Effect; and q2 the negative
annotation facade with exact `Allowance(v)`, allowed={resolved E}, tail=t2.

1. **Create the authentic parent/copy pair.** `sink g` constructs its negative
   Function demand (`shadow_apply.rs:1327–1383`). sink is a Value row at 1, so
   structural admission negatively extrudes the demand to 1
   (`lib.rs:12428–12442`). Its argument g is traversed positively. g's formal
   positive Function has a negative nested argument Function; that nested
   Function's result Effect is t at negative polarity. Thus the path is
   `demand(-) / argument g(+) / g.argument Function(-) / resultEffect t(-)`.
   Extrusion follows g's already installed positive Function lower, creates
   c1 for t2, retains `(c1,t2,Negative,1)`, and installs c1 as a lower of t2
   (`candidate_extrusion.rs:83–155,228–255,309–320`). Physical edge: `t2 -> c1`.
   This installation alone does not replay prior opposite bounds.

2. **Activate that lower by a later latent port.** h's positive formal Function
   uses the *same* t2 directly as its result Effect. The later `h 1` demand
   has r2 as its negative result Effect. Function comparison emits `t2 <= r2`
   (`lib.rs:12506–12512`). Both are at 2; the actual scalar branch stores r2
   as an upper on t2 and explicitly replays its opposite c1 lower
   (`candidate_extrusion.rs:840–863,763–805`). It therefore emits `c1 <= r2`,
   storing c1 lower on r2. This is the decisive activation absent from a
   creation-only trace.

3. **Carry the copy to the actual computation.** After Value-demand discharge,
   Apply slot 2 admits the original r2 below a2
   (`shadow_apply.rs:1423–1465`). Equal levels place a2 upper on r2 and replay
   c1 below a2. The block's Group relation then emits `a2 <= b2`
   (`candidate_source.rs:461–472`; `shadow_apply.rs:1410–1421`), whose replay
   places c1 lower on b2. Each later action is after the earlier synchronous
   drain; `lib.rs:12094–12124` enforces the drained worklist before return.

4. **Construct and admit the original-scope Allowance.** The surrounding
   ascription's computation owner constructs q2 with `Allowance(v)` and
   the existing scoped t2 (`candidate_effect.rs:1194–1273,1315–1353,1510–1579`).
   Its actual slot 47 admits `b2 <= q2`. Replay first emits `c1 <= q2`, then
   pairs q2's new c1 lower with its installed Allowance upper, emitting
   `c1 <= Allowance(v)`. Ordinary Effect admission stores the original view
   directly on c1, without tail extrusion (`candidate_extrusion.rs:840–863`).
   v is open, so it does not substitute a closed-row filter for this dispatch
   (`candidate_effect.rs:755–766`). The original t2 remains its tail.

The physical cycle at this final admission is:

```text
t2 -> c1 -> Allowance(v) -> t2
```

The first edge is actual extrusion creation provenance plus its stored lower;
the second is the explicitly activated non-row upper; the third is the SCC
consumer's view-tail edge (`candidate_intrusion.rs:415–442`). Same-SCC parent
qualification uses the retained actual pair (`:476–491`). Neither interpreting
Allowance as scalar t equality nor reversing subtype edges is required.
Memo suppression cannot erase a first physical bound: if a pair is already
completed, its physical effect has already occurred. This statement does not
assert complete global saturation.

## Capture, restoration and Generalize boundary

The cycle is constructed before x's Lambda completion/publication. ignored's
intervening local installation captures only its actual result Value root;
immutable graph capture does not mutate or remap the live g/h tail
(`candidate_scheme.rs:691–744,893–925`). No use of ignored follows. The route
does not need recursive x use, scheme restoration, independent incoming use,
or a fresh captured tail to stand in for t2.

Incoming Allowance capture (`candidate_scheme.rs:619–626`) and later scheme
freshening (`:1008–1021,1052–1073`) may remap local tails and views. Those
later events are outside this formation trace and cannot justify its original
coordinate identity. Source Generalize's scoped closure is a separate selected
definition: neither this native local graph capture nor the cycle establishes
its complete typed fixed/retain relation or lawful-use theorem.

## Evidence, resource use and omissions

Static commands: bounded `rg`, `sed -n`, `cat`; read-only exact dependency
`git diff 330d5432aff4b1f9655d501e17a9eefb7e75e098 -- <named source paths>`
was empty; `sha256sum` captured the following frozen inputs. No tests, builds,
Oracle, executable probes, seeds/ranges, mutations, benchmark samples, children,
Git mutations, or shared-record writes. One lightweight shell process at a time;
30-minute static budget respected. CPU/RAM peak and precise wall usage unknown.

There is no executable oracle. Producer, replay and consumer locations supply
distinct source-owner evidence but share the same compiler implementation;
they are not independent semantic validation. The scope-error variant above
was rejected by the actual HIR construction owner rather than another toy
model. No further search was performed after this corrected route was found.

Unverified: zero-recovery parsing of this exact text; candidate execution and
observed merge; complete Call/source-semantic lawfulness; every possible earlier
canonicalization/context event; all-source Effect reachability; arbitrary later
clients/restoration; hygiene, soundness, principality, public schemes and cutover.
The semantic theorem remains OPEN, and independent review is pending.

Recommended next action: assign fresh source/semantic review of this frozen
conditional trace, especially g's nested negative extrusion port, whole-block
scope and the h admission that replays c; then authorize one focused runtime
validation only if the primary accepts that source route.

## Independent review and exact scope

An independent `compiler_referee` found no blocking or major issue in the
bounded operational constructor trace. It confirmed the shared
`AnnotationScope::Local(x)` tail, the whole-block ascription scope, negative
extrusion of that tail to the retained copy, later `h 1` replay, and the
Allowance-tail edge that closes the cycle. Under the note's explicit
construction hypotheses, this is a conditional **Effect dependency SCC**
route.

The current user clarification fixes the selected semantic graph for Value
variables by references in Value contents. It does not turn this separate
Allowance/Support Effect adjacency into a Value edge. This note supplies no
Value parent/copy SCC, no proof that the source parses or is accepted, and no
complete Call, hygiene, soundness, principality, or production result.

The reviewer reported one minor checkpoint correction: the parent-copy design
was inspected at its historical baseline hash
`8ae4348a93dce6df1852a34b2294ebc5e4e256d8b018c1f6eaad42c502470a8e`, while its
current hash is
`2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0` because
the later Value-reference clarification was added. The historical dependency
hash remains unchanged in the snapshot below; the current authority delta is
recorded here to prevent using this Effect construction as evidence for the
Value graph.

## Frozen dependencies

```text
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb  crates/yu-hir/src/module/source_annotation.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df  crates/yu-solver/src/candidate_effect.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6  crates/yu-solver/src/shadow_apply.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
8ae4348a93dce6df1852a34b2294ebc5e4e256d8b018c1f6eaad42c502470a8e  notes/design/2026-10-10-parent-copy-scc-intrusion.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38  notes/design/2026-10-08-source-generalize-definition.md
```

## Commit packet

- Exact leased/changed path:
  `notes/progress/2026-10-11-effect-latent-tail-source-construction.md`.
- Baseline SHA: `330d5432aff4b1f9655d501e17a9eefb7e75e098`.
- Changed dependency hashes: none observed; local_source and shadow_apply hashes
  added to the frozen dependency set above.
- Claim/review status: conditional static Effect construction; bounded
  compiler-referee review found no blocking/major issue; original semantic
  theorem, Value-parent/copy scope, correctness and production parents remain OPEN.
- Checks already run: exact source dependency diff (empty), SHA-256 snapshot,
  static scope/polarity/activation/capture inspection. No executable checks.
- Proposed checkpoint commit message:
  `research: construct conditional scoped latent-tail Effect SCC route`.
- Shared-record delta integrated by primary: record the candidate same-Local(x)
  tail route, rejected inner-block ascription variant, bounded review, and the
  Value-versus-Effect graph boundary; preserve semantic theorem as OPEN pending
  accepted-source execution and source-semantic correspondence.
- Producer stops writing before submission; primary owns review and integration.
