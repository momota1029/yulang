# LEAN-COMPLETE-CALL-20261025 — Proposition B handoff

- Assignment-ID: `LEAN-COMPLETE-CALL-20261025/PROPOSITION-B`.
- Handoff revision: **1**, frozen read-only preparation; no proof submission.
- Sprint contract: `tasks/agent-loop/sprints/lean-complete-call-20261025-r7.md`,
  SHA-256 `5d0409f5918748fc175e926111710977bb4d0bda6b8a00b4a185b475110e3250`.
- Baseline: `7262f16cf58f0236a1a140e044d8fbbeb6cf61c6` (supplied by Luna;
  this worker performed no Git operation).
- Parent: `bounded_call_finite_prefix_safety`, Proposition B of r7. Full Yulang
  semantics/type inference, original inference A/B, source/native
  correspondence, principality and termination remain OPEN.
- Author/worker: `/root/complete_call_prover`, sole contributor, no descendants.
  Current primary session: `LEAN-COMPLETE-CALL-20261025/root-turn-2`.
  Actual runtime receipt: the received assignment and this worker's live reply;
  separate runtime/session identifier UNKNOWN.
- Requested route: constructive prover B, configured Sol/high. Observed model
  and effort: **UNKNOWN**; no inference from configuration or prose.
- Exact leases: `notes/theory/lean/YulangClosure/CompleteCall.lean` and this
  inbox path. Only this inbox path was written. No scratch paths were created.
- Outcome class: **candidate preparation**, not a conditional theorem, checked
  proof, source/native theorem, or production authority.

## Parent application and exact boundary

Luna explicitly confirmed in the live assignment that B quantifies the actual
finite **Call-internal** segment through its first explicit typed handoff or
represented terminal case. The arbitrary independently typed old Control suffix
must remain literal at each internal state and at that boundary. Every state in
that delimited segment must be not `Bad`. B asserts no safety of subsequent
foreign-suffix execution. This interprets the contract's internal-prefix domain;
it does not replace arbitrary suffixes with the empty suffix.

The distinction matters at actual owners `Control.ControlStep.bindCode` and
`Control.Step.body`: a typed foreign `.bind (.code c)` may enter `.run c ...`,
and an arbitrary registered body relation may then emit `.bad`. Suffix typing
alone supplies no preservation law for that foreign body. No `BodyLaws` premise
will be added to establish internal lambda or adapter safety.

No proposition has yet been proved for the new Call syntax. The exact missing
prerequisites are:

1. Luna-confirmed implementation handoff revision/hash, frozen representation
   and direct/transitive dependency hashes, source-successor coverage, and an
   explicit grant of that seam. Implementation remains its owner's responsibility.
2. Proposition A's exact frozen declaration of
   `call_context_plug_preservation`, its actual one-step/inversion helpers and
   module/dependency hashes, followed by Luna's grant to start B edits.
3. Those actual declarations must classify every represented internal successor
   into typed context preservation or the explicit typed handoff/terminal cases,
   using real substitution and retaining the represented world and old suffix.
   A missing case cannot be replaced with a same-body safety premise.

`CompleteCall.lean` has not been created or edited by this worker. A missing
frozen declaration is an unavailable prerequisite, not a refutation of B.

## Source evidence and intended application

The governing operational source is
`docs/yulang-operational-type-safety-ja.tex`, with contract-selected sections
read directly. Its Call rules at 362–393 require one fresh owner/Scope,
outer-to-inner wrap peeling, delayed argument adaptation, source receipt before
first force, Value force versus Computation substitution, and normal Scope exit
without erasing returned views/latent code. Complete interface Views at 585–593
and 1245–1247 cover entry through result consumer and adapters. The local
preservation argument at 1029–1044 uses actual let/force/delay typing and
substitution, rather than a supplied Call-preservation law.

Source distinctions retained as falsifiers:

- Request result typing is the saved continuation's normal result type, not its
  response type (342–359).
- Crossing Scope captures the owner and restores Scope inside the saved
  continuation (468–470); suspension is distinct from normal return.
- Request exposure metadata is distinct from return result-path metadata
  (484–490).
- Event creation observes all executing View frames, including across handlers;
  outward bubbling alone does not establish that source observation rule
  (585–593 and the following source explanation).
- Fail must retain its reason and the source's propagation/cleanup relation.

These observations are source-rule inspection, not evidence that the frontend,
native compiler or a newly written constructor produces an adequate decorated
plan. No compiler source or native path was edited or claimed verified. The r7
source-plan authenticity, complete decorated-plan adequacy, effect hygiene,
observation and source/native premises remain OPEN.

Once both seams are granted, the in-envelope proof method is finite-prefix
induction over the actual relation, keeping the initial representation equality
outside the induction hypothesis as in r6. Apply A to each actual successor.
The internal case preserves the typed context/result and represented world and
increments the exact internal prefix count. The exit case freezes the typed
handoff/terminal witness and its literal suffix at the first exit index. Any
whole-trace classification retains separate internal, exit and foreign-tail
counts (`n = k + 1 + l`); the foreign tail receives no internal safety claim.
Apply the endpoint result to every internal subprefix to establish all-state
`Bad` exclusion. This is a method plan, not an assumed lemma or Lean declaration.
Only constructors actually present in the frozen implementation may be claimed
represented; missing Req/Fail support must be stated in the theorem and outcome.

## Prior work reused and rejected

The reviewed r6 bridge supplies the genuine induction pattern in
`CoreControlBridge.finite_coverage_from` and `finite_coverage`, with exact
`n = k + 1 + l` arithmetic and an arbitrary literal old suffix. Its
`successor_coverage` inverts actual source steps or the explicit boundary exit.
`Original.substitute_top` and `Original.step_preservation` establish real
substitution and source-step preservation only for their represented syntax.
These results may be reused only after their r7 dependencies are frozen and
rechecked by Luna.

Rejected as insufficient for B: r6 `finite_closed_safety` has an empty suffix;
specializing to it would lose B's independent suffix quantifier. Generic
`Control.internal_preservation` assumes `BodyLaws` and cannot establish internal
Call body safety. The candidate V1–V7 outline supplies no established premise.
No same-body safety assumption, ordinary beta-only replacement, narrowed source
domain, or changed inference behavior was introduced.

## Hash observations

These input bytes were SHA-256 checked during preparation; they match r7.
They are not a freeze of the concurrently owned implementation component.

| Input | SHA-256 |
| --- | --- |
| r7 contract | `5d0409f5918748fc175e926111710977bb4d0bda6b8a00b4a185b475110e3250` |
| operational source | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `YulangClosure/CoreComposition.lean` | `1527cd3c5961b413ec2b97495744b218aba6247956881318485364d15065294c` |
| `YulangClosure/CoreControlBridge.lean` | `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a` |
| r6 accepted outcome | `b6def9a2c248ccbd7a8bda1cba9489b6dab84abd8a9131f0b24ce573e0eefd4a` |

New proof artifact hash: **NONE**. Proposition A declaration/hash: **NOT YET
FROZEN/RECEIVED**. Implementation handoff hash: **NOT YET FROZEN/RECEIVED**.
This handoff's byte hash is supplied separately after writing to avoid
self-reference.

## Checks, resources and mutual TODOs

Checks performed: direct source/declaration reading and the six input hash
comparisons above. No Lean/Lake/Cargo/native/test invocation, Git command,
external contact, nested CLI, or descendant ran. Kernel checking and independent
review are NOT RUN and remain Luna's assignments. First clock observation was
2026-10-24 22:54:06 UTC; preparation freeze requested at 22:56:56 UTC. Exact
launch-to-freeze elapsed time is UNKNOWN; the existing 1,200-second grant remains
reserved/charged under Luna's accounting, with no reset or extension requested.

- `B-IMPL-SEAM-1`: Luna/implementation owner supplies immutable grammar,
  typing, substitution, actual successor relation, metadata/world and typed
  handoff interface plus full hashes. Falsifier: an actual internal successor
  loses the owner, receipt/View, latent code, request data, result type, world
  transition or old suffix, or escapes the claimed classification.
- `B-A-SEAM-1`: Luna/Proposition A owner supplies the exact frozen A declaration,
  helper signatures, module and dependency hashes, and authoring grant.
  Falsifier: deriving internal preservation/progress requires `BodyLaws`, a
  candidate V1–V7 claim, an assumed substitution law, or an omitted successor.
- `B-PREFIX-1`: after those prerequisites, this worker constructs B in its
  leased module, preserving independent suffix quantification and exact prefix/
  exit arithmetic. No additional output path, dependency, semantics or budget
  is requested.

Worker state: **WAITING**, with all writes stopped at this revision's freeze.
No descendants or unresolved descendant leases exist. The two exact leases
remain assigned; this receipt does not release them. Continue only on Luna's
acknowledgement/granted frozen seams within the original remaining grant. This
preparation is not a commit-ready proof milestone and does not close the parent.
