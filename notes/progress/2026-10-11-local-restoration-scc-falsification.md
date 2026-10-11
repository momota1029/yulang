# Local-restoration SCC falsification boundary

Status: frozen, unreviewed research-only static source characterization.
No authentic counterexample or universal exclusion theorem is established.

## Objective, baseline and authority

Attack the original deterministic-rejection frontier over authentic supported
source/operation histories: a captured Local zero-opposite-count Value
restoration leaves a distinct retained Value extrusion parent/copy SCC
unsettled; a later Effect-root drain merges it and completes a Value mismatch
without reporting it; later Value drains and final Local linking also fail to
report the mismatch, allowing a conflicting result to remain exportable.

Baseline: `a077a4e3e75ba5144504f7e2182f45ee29ddef44`. Permanent ordinary
reference: `/home/momota1029/rust/simple-sub-reference`,
`9bae772624c23b52a93c1b226157e16898b4d9db`, confirmed by read-only rev-parse.
Governing sections: top-level inference principles §§1–4; design-authority
“Authority order” and “Natural compiler behavior and proof-obligation economy”;
research-lab “Evidence quality and stopping unproductive loops”; git-concurrency
“Disjoint-file mode”. The supplied deterministic-rejection proof §5 and
Effect-drain reachability note “Missing authentic predecessor” fix this gate.
Appropriate rejection and safe publication remain required. Exact diagnostic
identity, complete restoration and optional extra characterization are not
substitutes for this obligation. No selected language meaning was changed.

Method: reverse-path/owner-origin static inspection, separate from the assigned
prover's constructive invariant. No proof-worker artifact or review verdict was
used to derive the source findings below. The primary later notified this lane
that independent review had passed its separate invariant; that notification
is not independent review of this note.

## Source-derived restriction on the smallest proposed witness

The previous note's two-row table uses a positive parent `P` with an upper
copy `C`, then restores the positive lower `P` into `C` with zero uppers at `C`.
That table alone does not construct its restoring owner.

Actual Local Name use routes through `candidate_source.rs:680`,
`candidate_scheme.rs:1354–1400`, and `step_candidate_local_use:1500–1518`.
Capture precedes preparation; the complete prepared graph precedes restoration.
`Capture::row` (`scheme.rs:304–327`) marks a row local precisely when its
canonical level exceeds the capture boundary and it is not non-generic.
`expand_row` (`:570–573`) immediately returns for every nonlocal row.
Each emitted Value bound is physically owned by the expanded local row
(`:578–627`): lower rows/leaves use Positive, upper rows/leaves use Negative.
`prepare_candidate_fresh_use` (`:1005–1023`) remaps these local generic rows
to new rows at the common occurrence use level. Structural Function nodes are
reconstructed before preparation returns (`:1120–1159`).

`begin_candidate_fresh_bound` (`:1221–1277`) takes endpoints exclusively from
that prepared `fresh.terms` / `fresh.effect_operands` graph and preserves the
captured side. It supplies `FreshUse` evidence with the imported antecedent,
fresh use origin, original source bound and mapped relation. The original
Local occurrence supplies `ConstraintOccurrenceId(occurrence,0)` and its cause
(`:1502–1514`). This route is not a generic permission to select any live row
as a restoring owner.

In particular, an extrusion copy newly allocated by an earlier restoration
child (`extrusion.rs:110–124`) was not present at preparation. Simply naming
that copy `C` as a later captured restoring owner breaks the actual constructor
history. Older/non-generic rows are shared endpoints, but their mutable bounds
are not captured by `expand_row`; choosing one as the expanded owner also
breaks that constructor. These are local constructor facts, not a proof that
all source histories exclude a new SCC.

**Exact first failed construction step:** no authentic captured Value bound
was supplied whose prepared owner is the `C` of the smallest two-row table,
while `P/C` remain distinct and retain the required original parent record.
Representative redirection cannot be asserted to fix this: it needs a real
merge history, with canonical owner, levels and bound evidence traced through
that history. No such history was constructed in this packet.

## Minimized unresolved edge beyond that table

The missing object is an authentic captured Value bound `b` owned by a generic
local row `Q`, with its actual FreshUse evidence and occurrence. Immediately
before restoring `b`, its canonical prepared owner must have zero opposite
bounds, and inserting the prepared endpoint must close a dependency path
between some distinct retained Value parent/copy pair. Then the next replaying
captured Effect bound must actually start an Effect-root drain.

This is not necessarily a two-row configuration. Shared endpoint rows and
Function ports can be intermediates in the dependency graph. The two-row
failure does not exclude a path through them. In particular, non-generic rows
are shared even when their level exceeds the boundary; a proposed global
level argument must justify their mutable outgoing paths rather than assume
that every shared row is old/low. Fresh preparation and restoration do not,
by themselves, supply that justification. Parents existing before capture and
parents created by earlier child drains must both be covered. No smallest
source expression or actual relation/fiber assignment realizing these edges
was found. This packet stops at that missing source construction instead of
inventing a larger synthetic table.

For a genuine trace, the relevant preserved data are: original/copy creation
polarity and target (`intrusion.rs:171`), canonical representatives and levels,
original captured physical side, imported evidence and mapped relation, actual
Function ports, and original occurrence/cause. A row-name reachability sketch
that omits these data remains synthetic.

## Later Value consumer: delay versus permanent loss

The downstream consumer cannot be omitted from a counterexample.
After every bound has retired, Local completion always calls
`admit_candidate_value_link` on the prepared root and the actual occurrence's
Value component (`scheme.rs:1516–1518`). That owner records the source
constraint/provenance, then invokes `constrain_live_value` (`:1337–1344`).
Consequently the hypothesized Effect drain is not the final consumer in a
successful Local use.

At Value-root empty-queue settlement, `lib.rs:12225–12229` passes `Some(root)`
to intrusion. Any newly selected Value merge reopens that root and attaches
replay children through `candidate_replay_bound` (`intrusion.rs:595–604`,
`extrusion.rs:763–802`). Diagnostics then calls `replay_witness(root)`
(`lib.rs:12295–12304`). A mismatch first discovered there is ordinary later
discovery, not the requested permanent-loss witness.

If the hypothetical Effect drain already merged the pair, its persistent memo
witness is retained. Subsequent intrusion may have no new merge to reconnect
that mismatch to the final Value root. Whether final linking nonetheless
traverses/replays it requires the actual root, bound path and current relation
history. A dependency-graph path alone is not a diagnostic-child path.
`complete_diagnostic_delta` consumes direct witnesses and completed child
witnesses (`lib.rs:13300–13370`); it does not derive children merely from arbitrary
SCC reachability. This inspection establishes neither necessary rescue nor
permanent loss in the unconstructed predecessor.

Private result finishing runs `finish_observations` (`lib.rs:10368–10373`).
The actual graph export guard tests retained errors (`shadow_apply.rs:123–130`),
not every completed memo witness. Therefore a complete attack must show no
later reporting consumer adds the error before export. No exportable
conflicting source result is claimed here.

## Checks, dependencies, limitations and resources

Commands: bounded `cat`, `sed`, `rg`; read-only `git rev-parse`,
`git diff --name-only <baseline> -- <direct source paths>`; `sha256sum`;
lease-scoped `git diff --no-index --check /dev/null <note>`.
Direct source paths were unchanged against the pinned baseline at inspection.
Concurrent files, including the constructive producer's note, were untouched
and were not source inputs. The reference revision was confirmed; its ordinary
implementation was not rerun or treated as an oracle for Yulang's mixed drain.

Frozen SHA-256 dependencies:

```text
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
12afc28af43c125960e072e2eac58df5fada65c3ce33b74aa61e1b66e2d8c1c9  notes/theory/2026-10-11-deterministic-rejection-proof.md
7c484507f96595ecd5388412e64d2016d0a8267dbb063447ebbc810e9c1bb925  notes/progress/2026-10-11-effect-drain-value-witness-reachability.md
```

Claim class: bounded source characterization and minimized unresolved edge,
not theorem closure. Shared assumptions are the pinned compiler transitions;
there is no independent semantic oracle, executable checker, seed/range,
mutation test or enumeration coverage. Zero Cargo/build/test/bench/Oracle
processes. Static reads only; no Git mutations or further delegation.
The packet specified this process bound and stop condition but no numerical
CPU/RAM/wall limit. Exact elapsed wall time and peak CPU/RAM were not measured.
Requested runtime settings were not included in this packet; observed
model/effort metadata are unknown. No model-policy change is claimed.

Unverified: all shared/intermediate endpoint histories, complete representative
and prior-parent cases, actual source witness construction, necessary later
rescue, final publication adequacy, full rejection/soundness/principality.
Recommended next action: have the primary apply the separately reviewed
constructive invariant to these exact owner-origin and final-link premises;
only reopen this attack with a concrete uncovered source constructor.

## Commit packet

- Exact lease/changed path: `notes/progress/2026-10-11-local-restoration-scc-falsification.md`.
- Baseline: `a077a4e3e75ba5144504f7e2182f45ee29ddef44`.
- Changed dependency hashes: none observed; direct snapshot above.
- Review status: unreviewed research characterization; writes stopped at freeze.
  No independent review of this producer's output is claimed.
- Checks already run: static constructor/consumer inspection, pinned-source
  equality, reference revision and hashes; lease-scoped whitespace check.
- Proposed commit: `research: narrow Local restoration SCC falsification boundary`.
- Shared-record deltas left to primary/curator: record failure of the synthetic
  copy-owner construction separately from source exclusion; retain final Local
  linking as a required counterexample consumer; adjudicate the separate
  constructive invariant before changing the original parent gate status.
  No task/index/authority/question-board file was edited.
