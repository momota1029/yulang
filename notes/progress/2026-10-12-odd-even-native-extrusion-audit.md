# Cross-level odd/even: native extrusion event audit

Status: frozen bounded static operational derivation; unreviewed research
Baseline supplied by primary: `research/simple-sub-intrusion`, `264bf0158`
Lease: this file only; no Git commands, execution, builds, tests or delegation
Parent Value-owner/transport and qualified equality gates: OPEN

## Objective, authority and claim class

Trace the first genuine extrusion parent in a cross-level recursive source
family, separating its endpoints from the accepted source-owner cycle. This
is source inspection and finite hand evaluation of the actual candidate
transitions, complementary to the prover's mathematical derivation. It proves
no soundness, principality or general source-reference law.

Governing sections: parent-copy SCC decision, “Selected operation and compiler
responsibility”, “Value-reference SCC clarification”, “Retained boundary”;
top-level inference principles §§1–5; local self-recursive binding, “Selected
source behavior” and “Proposed source-to-solver seam”; source Generalize §2.
The accepted edges may cross lexical levels. Comparisons and parent metadata
are not source-reference edges. No candidate scanner is approved as the full
Value-reference graph. Published local uses freshen descriptions while retaining
actual binding objects; active recursive roots remain monomorphic.

Exact user text, reproduced in `tasks/current.md`:

```yulang
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

The current source boundary remains: conditional syntax requires `:`, ordinary
HIR does not admit this indented body, and LocalSource has no conditional form.
No native history of this exact text is claimed. The primary additionally
assigned this Call-bearing analogue:

```yulang
my odd n = { my even n = odd(n); even(n) }
```

It removes conditional/infix arithmetic while retaining both Calls and the
cross-level lexical cycle. The earlier spelling `odd n; even n` is not safely
classified as Name-only: parser `operator_chain.rs:758–812` admits a same-line
identifier as `MlArgument` when ML mode is enabled; LocalSource `:533–541`
accepts both MlArgument and CallTail as Apply. The explicit parenthesized
analogue avoids dependence on the applicable ML mode. Adjacent `(` dispatches
to `call_tail_normalized` (`operator_chain.rs:633–634`), and LocalSource
`:533–574` constructs Apply with its actual callee/argument. This is static
formation evidence, not an executed parse or admission result.

## Actual identities and schedule

Use symbolic names for actual allocation roles, never prescribed row ordinals.

| Endpoint | Owner/role | Initial live level |
| --- | --- | --- |
| O | module definition root of odd | 1 |
| L | outer Lambda expression root | 1 |
| X | outer formal n | 1 |
| B | outer block result row | 1 |
| E | local even initializer Lambda row and installed local root | 2 |
| Q | local even formal n; inner argument Name aliases this endpoint | 2 |
| N | module Name odd inside even | 2 |
| A | inner Apply result row | 2 |
| U | published-local Name even in final expression | 1 |
| Z | final Apply result row | 1 |

All collected roots initially receive level 1 (`lib.rs:10048–10105`). Source
traversal starts at 1, preserves level through Lambda, and increments only
block initializer traversal (`candidate_source.rs:254–305`). Thus E/Q/N/A
receive 2; final expression and X remain 1. Parameter Names use Parameter
endpoints, not their separately allocated occurrence rows (`:211–217`).
Lexical lookup makes the inner n Q and final n X
(`yu-hir/src/module/local_source.rs:636–656`).

The ordered relevant actions are: inner Name Module, inner argument Name
effect facts, inner Apply Candidate, inner Lambda, initializer effect link,
Install(E,boundary=1), final local Name Local(use-level=1), final argument
Name effect facts, final Apply Candidate, block Group, outer Lambda, final
Link(L,O). Name/Lambda purity and effect facts interleave as emitted by
`candidate_source.rs:369–476`. The temporary active initializer is even;
there is no Name of even inside its initializer in this analogue, so no
recursive-local Link is emitted there. odd is a ModuleDef lookup.

The retained module use has enclosing definition odd as parent and target,
although the lexical source reference belongs to even's initializer. It is
therefore internal in odd's definition SCC. `execute_candidate_graph_plan`
activates roots/uses before the schedule (`candidate_scheme.rs:842–882`),
and Action::Module dispatches through `route_candidate_open_use` to
`route_internal_inner` (`candidate_source.rs:672–676`,
`candidate_scheme.rs:938–945`, `lib.rs:15765–15782`). Capture boundary zero
after the module schedule does not change O's live level to zero.

## Decisive native prefix: two Value parents really are retained

Hypotheses: the explicit analogue has formed the stated LocalSource; the
private candidate graph/effects route is selected; allocations and these
normal admissions succeed; no external intervention changes identities. No
Value-owner content map or scanner-correctness premise is assumed.

1. Module Name admission requests O1 <: N2. Candidate row admission selects
   N as positive owner because `level(N) > level(O)`
   (`candidate_extrusion.rs:816–823`). It stores `N.lower += O`; neither
   lowering nor parent retention occurs for this row/row admission.
2. Inner Apply constructs `D2 = Function−(Q2, argument-effect2,
   invocation-effect2, A2)` and admits N2 <: D2
   (`shadow_apply.rs:1331–1390`). Q is the actual shadowing formal, not X.
   This stores `N.upper += D2`; replay of N's existing lower O requests
   **O1 <: D2** (`candidate_replay_bound`, `:763–804`).
3. The structured upper endpoint is extruded negatively to O's live level 1
   (`lib.rs:12427–12440`). Function traversal flips polarity for input and
   argument effects, preserves it for result/effects, and visits argument
   first (`candidate_extrusion.rs:225–262`). Q2 is above target 1, so its
   first Value event is exactly
   `Parent(cQ1, Q2, Positive, target=1)`.
4. `candidate_extrude :90–125` allocates cQ, calls
   `retain_extrusion_parent`, and inserts `Q.upper += cQ` before copying
   Q's prior positive/lower side. Q has no Value lower bound in this prefix.
   Argument-effect and invocation-effect copies are distinct Effect events;
   they are not Value graph vertices by the selected source contract.
5. Visiting the result port similarly retains
   `Parent(cA1, A2, Negative, target=1)` and inserts `A.lower += cA`.
   A has no prior Value upper bound in this prefix. The rebuilt demand is
   `D1 = Function−(cQ1, copied effects1, cA1)`; it is admitted as O's upper
   bound by the rewritten task.

Thus the Call-bearing analogue reaches actual Value extrusion. These parents
are an inner formal and an Apply result, **not** O or E. The endpoint rows
are identified by their owning construction, not inferred from matching
levels, source spellings or parent IDs. No independent use freshening is
misclassified as an extrusion event.

Later level-sensitive operations are also distinguishable without assuming
source graph semantics. Inner Lambda admission uses Q/A and entry/return
effects at level 2 against E2 (`lib.rs:11233–11370`). Installation retains
E and boundary 1 (`candidate_scheme.rs:1316–1335`). Final Local capture
classifies rows above boundary 1 as local; `prepare_candidate_fresh_use`
allocates their description rows at use-level 1 (`:307–321,1010–1020`),
preserving older anchors such as O/cQ/cA and stopping capture expansion there
(`:567–574`). It does not call `retain_extrusion_parent` for these fresh rows.
Fresh-bound restoration precedes the final root-to-U link (`:1500–1520`).
Final Apply uses X1/Z1, block forwarding uses Z/B, and outer Lambda uses X/B
against L1 before Link(L,O). This schedule describes consumers; a complete
post-prefix graph/lifecycle trace was not certified here.

## What the event does and does not establish about SCCs

At the decisive prefix the scanner's Value payload incidences include
`N → O`, `N → D2 → Q,A`, `Q → cQ`, `A → cA`, and
`O → D1 → cQ,cA`, with all four Function ports also traversed.
The fresh cQ/cA have no Value-side outgoing references yet in that prefix.
Consequently neither pair has a scanner return path in this prefix. Parent
metadata adds no edge (`candidate_intrusion.rs:375–485`); source references
are not being inferred from these storage directions.

The accepted source-owner cycle is `even → odd → even`. It says nothing
by itself about `cQ → Q` or `cA → A`: Q is a formal port, A is an Apply
result, and neither is the even owner E. The two source edges therefore do
not prove that either retained parent/copy pair is in one source-Value SCC.
Even the candidate's actual one-sided Q/A links require a Value-content
correspondence before they can be promoted to source-reference edges.

The first missing source premise is now concrete: the native content and
resolved reference targets owned by the extruded formal/result rows, and
their preservation under the polarity-specific copy and later local use.
For A, this includes the already open Apply result-to-row-content law.
For cQ it includes the formal/description target identity law. No approved
reverse source-reference path from either copy to its parent is provided
by the inspected constructors. This is missing evidence, not proof that
the required path is impossible, that later scanner SCCs cannot arise, or
that intrusion is unnecessary.

The current analogue can discriminate **whether the implementation emits
actual parent records**. It cannot currently certify the desired qualifying
source-Value SCC or equality theorem. `CandidateInference::solve`
(`shadow_apply.rs:79–113`) is the receiver; it admits the private graph route
subject to preflight/session success. The separate CandidateValueObservation
receiver rejects internal module uses (`:541–552`), so it is not an alternative
receiver for this trace. Neither receiver establishes complete Call, exact
source admission, runtime Return or public inference correspondence.

## Evidence, limits and next action

Read-only commands: bounded `cat`, `rg`, `sed`, `sha256sum`; one leased note
write. No executable checker/oracle, parser, compiler, test, build, benchmark,
random seeds, enumeration ranges or mutations ran. The operational derivation
shares the inspected implementation rules; it independently locates their
constructors but does not prove those rules sound. Some combined reads
truncated; decisive transition windows were reread narrowly. Two guessed
source module paths were absent and were replaced by actual rg locators.

One leaf, zero children, zero heavyweight processes. Budget: 30 minutes;
not exhausted. Exact reasoning wall time, CPU and RSS are unmeasured.
No original conditional/arithmetic trace, full final scanner enumeration,
source-reference reverse path, abnormal/retry behavior, general effect graph,
soundness, principality or cutover verification is claimed. Independent
review remains pending. Writes stop at this frozen handoff.

Recommended next action: supply the constructor-owned source content/target
transport for `(cQ,Q)` and `(cA,A)`, then evaluate their actual two-way source
reachability; use the explicit Call-bearing analogue for the bounded native
event check when execution is separately authorized.

## Dependency snapshot and commit packet

Direct source SHA-256 values at artifact freeze:

```text
parent-copy decision 2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0
top-level principles edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389
local recursive binding 38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895
source Generalize 46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38
HIR local_source.rs 906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed
syntax operator_chain.rs cd7b6ccd9e0bf92d90de5a0e9e5cfdede5f38990bacb12d60fff8e9fdf8edc2d
candidate_source.rs 13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49
candidate_call.rs 79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35
candidate_extrusion.rs fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0
candidate_scheme.rs 9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1
candidate_intrusion.rs aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0
shadow_apply.rs 230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6
solver lib.rs c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94
candidate_effect.rs ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df
```

- Exact leased/changed path: `notes/progress/2026-10-12-odd-even-native-extrusion-audit.md`.
- Baseline SHA: `264bf0158`, supplied by primary; Git/live-baseline validation
  remains primary-owned. No dependency was changed by this leaf.
- Claim/review: bounded static operational derivation and exact missing bridge;
  unreviewed research checkpoint; no theorem or implementation authority.
- Checks already run: constructor/consumer window reads and direct dependency
  hashes; no execution/tests/builds. No independent self-review claim.
- Proposed message: `research: trace odd-even Call extrusion to actual port parents`.
- Shared-record deltas left to primary/curator: record the inner replay
  O1 <: D2 and actual Q/A Value parents; distinguish them from O/E source
  owners; preserve qualifying source SCC, owner/transport, equality, complete
  Call and production gates OPEN. No shared record was edited.
