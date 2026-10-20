# R185 — source-history frontier audit

Revision 1; author `/root/r185_source_history_proof`.
Outcome: **candidate local constructor evidence; exact required-owner STOP**.
`R183-FRONTIER-COVERAGE-1`, original parent, A/B, source/native,
implementation and production gates remain **OPEN**. No source-qualified
counterexample, reviewed theorem or production authority is claimed.

## 1. Parent and unchanged application target

The original parent is
`notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1,6–7,
SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`.
For EACH actual compared provider use i, with its authentic endpoint map mu_i
and actual mapped admissions, its native implication requires

```text
e_A <= mu_i(e_t) <= mu_i(e_n) <= mu_i(e_R) <= e_C <= e_out.
```

The fixed domain retains the shared xi, original declarations/formals/providers,
open incoming E, arbitrary finite chains and prefixes, repeated/simultaneous
entries, alternatives, independent protections, pending matching/guards/value
computations and raw typed resumptions. The positive explicit-root source
fragment does not restrict the full accepted source domain. F1 and FK1,
including foreign continuations, remain independent obligations. No argument
below discharges any of them through a local frame action.

R183's scoped reviewed result (author `/root/r183_source_to_capture_proof`,
SHA-256 `0fe3afdc4ddfd1d3b8979bf34497e395bef06836a199cb6735a39eb84c43a28d`)
establishes the local Capture/FreshUse conservation argument once the required
physical owners and fibers are reached. Its §6 leaves the actual source-history
frontier law open. R185 investigates that law without changing its statement.

## 2. Input boundary and what was actually inspected

Luna activated R185 revision 1 after prospective CLEAN review. Contract:
`tasks/agent-loop/sprints/source-history-and-option-b-representation-20261021-r185.md`,
SHA-256 `d1323554eaf8809e6f65c27df2592fea49ffeb3b557f4070beb050e9cef7b997`.
Baseline `1ec02864dccccffa9617705b0ddbeaa64176aff5`.

All 45 source manifest entries were read as committed blob bytes and their
SHA-256 values matched the contract. Luna explicitly authorized read-only
`git show BASELINE:path` for these exact paths; no Git mutation or repository
control action occurred. No worktree compiler source or external Yulang2 source
was used. Hashing all 45 entries is input authentication, not semantic coverage
of all 45 files. Semantic inspection concerned the eight solver files below;
other entries were hash-only.

| Inspected solver owner | SHA-256 at this baseline |
| --- | --- |
| candidate_source.rs | cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7 |
| candidate_scheme.rs | 9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225 |
| candidate_extrusion.rs | 7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332 |
| candidate_intrusion.rs | 475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97 |
| candidate_effect.rs | c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1 |
| lib.rs | 99dc39e970b35f2d06a900826bf686ee5a76795430a3e4167ac5c64184da6af6 |
| candidate_value_graph.rs | 19da9779e3e7866f5891e019e1cd343136ae0115bd1c47a02a7e7ee0cdfa80e0 |
| candidate_context.rs | ac1375954d0d310bbeaaccb09625dc4701dd1c25a050a67f1f203d91e9456b06 |

The proof facts below use these baseline bytes and their own line numbers.
R183's candidate scheme/lib/context bytes differ; its historical line numbers
and candidate-specific behavior are not silently promoted to this baseline.

## 3. Pinned source admissions and a useful rejected attack

`candidate_source.rs:966–1058` assigns a Lambda and its immediate body the
same source level; a Block initializer instead enters the next level, with
publication at the enclosing boundary (`:1126–1160`).
`initialize_candidate_source_levels:1585–1618` initializes the source component
and parameter levels and allocates a Computation entry at the parameter level.
`execute_candidate_action:1736–1739` resolves a FormalNameEffect action through
that registration's entry. `candidate_effect::candidate_formal_effect_equal:
1439–1448` admits both actual effect inequalities. `lib::admit_lambda_fact:
11322–11444` allocates the return at the parameter level and admits bodyE<=RE;
Computation omits Value's slot-3 forcing edge.

At an authenticated first distinct direct-Name admission, write t,n,R for
these actual entry, Name and return rows at level l. On the ordinary fresh
effect-dispatch branch, `candidate_apply_effect:946–971` stores equal-level
t<=n at t's upper side, n<=t at n's upper side, and n<=R at n's upper side.
The physical insertion owner is `candidate_insert_bound_with_evidence:
501–635`. Thus Capture of the reached original Function can find n through
its AE=t while all three owners remain local. This rederives the local seed
used by R183; it does not assume that every later source use has that seed.

Consider one attempted way to obtain R183's mixed frontier: start at exactly
that seed, negatively extrude t to k<l, qualify that occurrence, and finish its
normal intrusion/drain before capture, without other intervening mutations.
This attempt cannot leave t shared with n and R local at a boundary b>=k:

1. `candidate_extrude:84–188` memoizes t's fresh copy at k, records its parent,
   and visits every selected upper bound. It therefore visits n from t<=n.
2. Visiting n negatively selects n<=R and n<=t. Memoization terminates the
   cycle back to t and visits R. Each of t,n,R has level l>k and gets its own
   negative parent/copy pair in this same occurrence. `Work::Bound:329–344`
   stores the selected copied edges and transports their actual fibers.
3. `retain_extrusion_parent` (`intrusion:306–376`) reads the processing
   relation's source-event set. If that occurrence qualifies, each of these
   parent records enters the pending list. `finish_candidate_extrusion:
   378–396` records the common occurrence/group; qualification is a source-Value
   SCC condition, not a type-endpoint SCC assumption.
4. `settle_candidate_intrusion:568–597` visits the pending parent indices.
   `merge_candidate_rows:599–709` unions each pair, appends both stored sides,
   transfers fibers, and takes the minimum row level. At completion the
   canonical t,n,R each have level at most k. They all fail level>b and hence
   are all nonlocal at b>=k. In the intermediate merge prefix this conclusion
   need not hold; a successful later capture cannot be justified from an
   arbitrary private partial prefix.

The same inclusion of t,n,R occurs when the initial original positive Function
is extruded to k: `Work::Function` gives its AE negative polarity and its RE
positive polarity (`extrusion:220–267`), while AE's selected upper traversal
already reaches n and R. Again a qualifying completed occurrence lowers all
three. No claim equates separately signed copies: the result concerns the
canonical original rows after the actual qualifying group has settled.

This is a local exclusion of one concrete attempted history. Applied to the
parent, it rejects a proposed source counterexample that changes t's level by
this operation but suppresses the same operation's n/R copies or qualifying
merges. It does not establish universal frontier coverage, and supplies no
new accepted source witness. In particular, unqualified extrusion, other
polarities, later admissions/recapture, current/reuse and intervening aliases
cannot be inferred from this one completed occurrence.

`Capture::row:769–804`, `expand_row:1067–1168`,
`capture_candidate_graph_inner:1229–1305`, and
`prepare_candidate_fresh_use:1610–1640` confirm the actual shared cutoff and
one image per current canonical row. Shared storage is retained in the session;
that alone does not join a shared original to a copied local neighbor.
No appeal to the noncandidate `lib.rs::extrude` level-lowering routine is
valid here: `apply_effect_task:11820–11823` selects the candidate operation
when the candidate graph is present.

## 4. Exact obstruction: missing actual-source admission owners

The next discriminating method was to inspect an actual Apply whose rewritten
negative demand exposes the argument effect at positive polarity. This could
distinguish whole-group locality from an unsupported assumption that arbitrary
connected rows share one classification. The pinned code supplies the
downstream mechanism: `lib::dispatch_live_item:12580–12610` negatively extrudes
an upper structural value into its receiving row; Function argument/effect
polarity reverses; qualification comes from the exact processing source event.
`candidate_value_graph::Graph::retain_source:183–209` constructs an Apply's
source event from its original declaration owner and actual callee Value;
`qualifies:244–246` uses their sealed source-Value SCC. This is not a license
to choose a qualifying event from an unrelated provider.

The actual admission is outside R185's manifest:

| Required unpinned path / definition | Concrete missing evidence |
| --- | --- |
| `crates/yu-solver/src/shadow_apply.rs::admit_candidate_fact` | `candidate_source::execute_candidate_action:1751` calls this owner for Action::Candidate. Authenticate the actual source recipe, whole argument Value/effect, demand constructor, receiving callee and slot-0 admission, and their occurrence/provider/use relation at this baseline. R183 §5 identifies the historical owner but its candidate bytes are not this baseline's pinned evidence. |
| `crates/yu-solver/src/candidate_call.rs` definitions supplying `FormalNameInput`, `FormalRole` and the formal registration/native entry/carrier records | `candidate_source:927–935,1295–1304,1585–1618,1736–1739` consumes these records. Authenticate their original formal/declaration and role/entry/Name association, and the call consumer's actual same-provider/use route. The registration's existence in a consumer is not a derivation that its source supplier emitted this registration. Exact additional definition symbols must be located inside this file after its admission; no unseen function name is invented here. |

Neither file was inspected. Their hashes/modes at the fixed baseline are
**UNKNOWN in this packet**. Prior assertions are reused only within their
historical premises; they do not establish these current owner bodies.
The first row alone blocks a complete induction over actual source Apply
admissions. The second blocks its required formal/carrier authentication when
attempting to close the same-provider/use bridge. This is a dependency
obstruction, not evidence of a compiler bug or of impossibility of the theorem.

Luna's explicit stop instruction required freezing on these missing owners.
One final read of the already pinned `candidate_source.rs:1705–1768` copied
the exact action-to-consumer locators for this handoff. No additional owner,
proof stage or implementation was admitted after that instruction.

## 5. Parent application, TODO and falsifier

Actual result: the initial signed qualifying-extrusion attack above is
excluded by its whole parent/copy group. R183's abstract mixed-frontier
skeleton remains an abstract API-level falsifier, neither source-qualified
nor ruled out for every allowed history. No universal source-admission or
level-locality invariant is established. The parent's mapped-admission premise
therefore remains exactly OPEN, as do both independent Replay inputs and
the separate terminal same-use interpretation. A local row map is not a runtime
receiver, provider identity, scoped payload transformer or observation witness.

**R185-ADMISSION-OWNERS-1 — Luna dependency decision.** Sequentially revise the
manifest to pin the two exact missing paths above at the unchanged baseline
(including modes and SHA-256); obtain prospective review and activation before
further reads. Required inputs are the actual original source, formal/provider,
Apply occurrence, registration/carrier, level/boundary/non-generic decisions,
physical bound owners, source event and qualifying parent/copy group. Proposed
output is an extension of the source-history derivation on a newly assigned
exact lease, or a fully source-qualified counterexample. This request grants
no write/code/test authority and adds no external dependency.

Falsifier for a claimed locality invariant: an admitted source history produces
the mixed cutoff after all required pending work settles, the actual compared
Function and use are authenticated, and no captured or authentic shared path
joins its mapped t,n,R. A synthetic relation history, unrelated provider,
one-parent Replay association, skipped qualifying group member or worktree
source bytes do not satisfy this falsifier.

If later authorized source reads cannot decide emission, the minimal provisional
implementation TODO remains passive readback at that actual Apply admission,
`Capture::row/expand_row`, and actual restoration/Replay consumers. Record the
same original provider/use, physical key and relation, canonical decisions,
mapped endpoints and BOTH ordered Replay keys. Exact source-emitted loss is the
falsifier; tests of assumed transitions would not prove source emission. R185
authorizes neither such instrumentation nor production code changes.

Omitted coverage is explicit: arbitrary admitted Apply histories, other source
alternatives/annotations, unqualified/signed later extrusion, later qualifying
reuse, canonical aliases, recapture, successful valid rollback, repeated or
simultaneous source entries, pending match/guard/value-arm computation, raw
reentry and foreign continuations. These remain in the original domain. No
Simple-sub operation or ordinary inference rule is removed or weakened.

## 6. Provenance, checks, resources and freeze

Direct documentary dependencies, verified over actual file bytes:

```text
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  original parent
0fe3afdc4ddfd1d3b8979bf34497e395bef06836a199cb6735a39eb84c43a28d  R183 proof note
6380fedea2dad3e302fd8ed2ce99a010c61eff493b7010c17476020afa028dd8  R183 rev3 contract
d1323554eaf8809e6f65c27df2592fea49ffeb3b557f4070beb050e9cef7b997  R185 rev1 contract
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  top-level inference principles
e50f5d4f79814c87af56e7dc34ddb6ab968abb523826c72ecdc40a8920397c0a  goal-driven sprint rules
1379059577f4469ed930c0fc130e5cd169401cf9188dfcbbc482b92b43daebbf  handoff protocol
```

Luna authored allocation/activation and the exact missing-owner STOP direction;
R183's author supplied its scoped historical proof. Current compiler authors
are UNKNOWN here. This note has one author, no coauthors or descendants, and
cannot independently certify itself or a combined result.

Checks: 45/45 committed blob SHA-256 comparisons, documentary pin comparisons,
static constructor reading and a hand-derived local group argument. Source
modes are manifest/prospective-review evidence, not remeasured by this leaf.
Zero tests, builds, probes, compiler/sample execution, network, nested CLI,
descendants or production edits. One unavailable `python` command exited 127;
the read/hash operation was then completed with `python3`. No probe was run.

Grant: 1200 seconds; elapsed active wall time was not measured from launch and
is UNKNOWN. Retain/charge the full grant conservatively; no unused budget is
reclaimed or carried forward. Requested model/effort: Sol/high
(`gpt-6.1-sol`, high), fork none. Observed model/effort: UNKNOWN/UNKNOWN.
Worker `/root/r185_source_history_proof`, session
`current-conversation-2026-10-21-r183`, active launch evidenced by the parent
assignment and this tool-backed work. All new paths are exactly this note and
`tasks/agent-loop/inbox/20261021-r185-proof-result.md`; no scratch paths.

**STOPPED after writing the frozen revision-1 handoff.** No descendant leases.
Fresh independent review and Luna adjudication are required before accepting
any candidate result. No next stage runs while waiting.
