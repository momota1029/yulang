# R84 readiness: effect hygiene and first runnable role call

Sprint: `effect-hygiene-runnable-role-slice-20261019-r84`, revision 1  
Contract SHA-256:
`fd6de85efe1926696f3a45894aa1e3a8a612b31d257bb71b339cc7c79d7c2f48`  
State: **review pending; no semantic adoption or code authority**  
Original parent/A-B: **OPEN 0→0**; R50: **NOT_ADOPTED**

## Decision package

The pilot proposes `Role::member receiver args`, with `SecondInt::second 1 2`
as its first executable target and result `2`. Its exact supported declaration
envelope and one ordered three-way compatibility procedure are in the frozen
[judgment](../design/2026-10-19-r84-role-call-judgment.md), SHA-256
`f3c604dd7a131bbba606d38ff5b19f37c01ef1b26386a5f90ae39e8de60478c1`. The
[adoption offer](../design/2026-10-19-r84-role-call-adoption.md), SHA-256
`4f8abc69bc7429e0960569e8bfe2af6d385f5aa45bfe454dacb14200001b32ce`, derives
its outcomes from that judgment, including both mixed-failure cases. Outside or
unknown endpoint evidence over the complete declarations, including extra
binders, is checked before arity, type or role mismatch. This fixes R83's
package inconsistency in a new Draft; it does not adopt semantics or revise
R83.

The candidate [proof](../theory/2026-10-19-r84-role-call-preservation.md),
SHA-256 `9f2520f0e5b13ddd0bb630f2fca43813037739170296cae1e38f5280b2cc987d`,
proves finite classifier totality/disjointness and §21 role preservation for
Compatible declarations. It specializes R81 conditionally: if P1–P4 produce
and admit the ordinary receiver-first curried graph, `SecondInt::second 1 2`
returns `2`; the exact unhandled Value example stops at `observe(1)` with its
suffix suspended. P1–P4, endpoint evidence, authentic member materialization,
native correspondence, F1/FK1 and the original parent remain open. This is a
candidate proof, awaiting independent review.

## Source-to-runtime path and early execution target

The frozen [source-path handoff](../../tasks/agent-loop/inbox/20261019-r84-source-path.md),
SHA-256 `c5cb26e5e70739b7ea467c13ccd89bf0219aa538ba78a3917ea75ae1240f4165`,
reports all 103 R80 source-manifest pins matched. It maps the current route:

1. Role/impl syntax and `::` occurrences parse, but source occurrence inventory
   does not produce validated `RoleId`, `ImplId` or `MemberId` identities.
2. Unique receiver/member validation and executable body/binder/environment
   materialization are absent: **P1/P2 OPEN**.
3. Current qualified `::` paths form `Operation`; ordinary applications form
   curried `Apply`. The required selected-member ordinary graph and provenance
   are not produced: **P3 OPEN**.
4. Candidate preflight and declaration-error exemptions do not admit complete
   selected role metadata. Runtime has ordinary Apply consumers but no
   validated role target table: **P4 OPEN**.

This gives the next implementation sprint an exact vertical path: source
identity → validation → member body/root/environment and original annotations
→ ordinary receiver-first Call/Apply → complete candidate admission →
`RuntimeProgram` execution. The handoff names the pinned source owners for each
step. It is not a runnable-support claim.

Future command candidates after adoption and implementation are
`cargo run -q -p yu-playground -- --run answer path/to/second-int.yu`, followed
by a bounded `--steps 100000` invocation to distinguish exhaustion from a
result. The literal fixture path is a placeholder. Neither command was run; no
test, build, probe or compiler execution occurred in R84.

The source-path launch requested `gpt-6-sol`/high and effective model/effort
remain UNKNOWN. Its handoff's metadata sentence says the request was not
specified; Luna's launch record is the request receipt. This metadata
discrepancy does not affect the pinned source claims or evidence boundary.

## Broad effect-hygiene map

These six fronts provide broad coverage while the role-call rule receives proof
depth. They remain separate open obligations; R84 proves none of them as a
general theorem.

| Frontier | Best current evidence | Open owner and next falsifier |
|---|---|---|
| Ordered handler match/priority | Pinned runtime scans arms in source order and checks operation identity, payload and permission; R78 evidence is conditional on authentic HIR. | Source Call/HIR Catch owners: show actual source selection under overlapping handlers or a projection/order mismatch. |
| §21 Value/Computation entry | Charter §21 and pinned candidate/runtime/receiving consumers; role-call lemma is conditional on actual binder retention. | Future role-member producer/admission: emit original annotations; falsify with inherited role, skipped Value force or eager Computation force. |
| Wrong or sibling permission | Pinned Grant checks require positive ownership/boundary/family/ancestry evidence; a missing Grant is not proof of protection. | Native K,D/residual owner: preserve a protected sibling; falsify if wrong family/owner matches or sibling request disappears. |
| Shallow unmatched outward request | Pinned runtime propagates the unmatched event with its saved suffix; R78 S evidence is conditional. | Authentic source and native residual owners: preserve event and suffix; falsify on dropped/reminted event or consumed suffix. |
| Continuation capture/resumption | One pinned runtime capture/binder/resumption route and read-only `ping 7`/`k 23` fixture. | Continuation F1/FK1 owners: inspect full template transport plus a protected sibling; no universal continuation result follows from the fixture. |
| Static-to-runtime path | Existing operation path reaches candidate actions, instructions and runtime requests; the selected-role path is not built. | Native definitions and complete source projection owners: preserve joint K,D/residual identity and request provenance through selected-member admission. |

These rows do not solve effect hygiene, permission preservation, all
continuations or source/native correspondence. They also do not reopen broad
storage/fiber inventory. Each row has a specific owner/falsifier for later
work.

## Review and adoption gate

The judgment, adoption offer, proof, source handoff, this readiness note, R83
closeout, R81 proof and R80 manifest are frozen inputs for fresh independent
compiler and specification reviews. No result is adopted unless both reviews
find no unresolved major/blocking conformance issue. If reviews are clean,
Luna will present this exact package for explicit user adoption. Only after
that decision can the next separate contract implement the first runnable
vertical slice. No expected-output, test, diagnostic, source, production or
Git change is authorized by this package.

The R84 proof and source-path allocations (150s and 100s) are charged in full;
the 700-second sprint grant has no carryover. Requested and observed model
metadata, STOP receipts and all hashes remain in the compact current state and
individual handoffs. No worker has an active writer lease.
