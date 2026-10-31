# R112 immutable Rust/source correspondence — revision 1

Status: **SOURCE CHARACTERIZATION / UNREVIEWED / FROZEN / WRITES STOPPED**.
Assignment `/root/r112_source`, complementary researcher, sole author, no
descendants. Runtime identity is the primary's NEW_TASK recipient. Model and
effort observations are UNKNOWN. This is not independent review.

## Objective, baseline and governing premise

Sprint `EFFECT-PERMISSION-SOURCE-SCOPED-ADMISSION/20261101-R112`, contract
SHA-256 `dc8812a1b186f523b338a1578bff16d04170bca5cdc0df3c96dac380d6cfc7f7`.
Method: bounded immutable source inspection of the two assigned owners and
their same-file producer/readout seams. No execution experiment.

Rust baseline: `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`. Every Rust byte
inspected came from `git show <baseline>:<exact path>`, never live source.

| Exact immutable source | Complete-file SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_effect.rs` | `1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41` |
| `crates/yu-solver/src/candidate_receiver.rs` | `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2` |

These match R111's baseline column, not its reconstructed repair candidates.
No dependency was changed. Selected semantic sources are Source Generalize
construction §§3.3 and 5.2; original intrusion parent §§1, 3 and 5; immutable
Value-birth-level SCC qualification §§2–6; top-level inference principles.
Accepted meaning: ViewLogic stays in its description region before its
challenge, EventProof stays under its actual event with the full telescope,
Shared is chosen once, and all uses retain one lawful joint strategy.
Numeric levels and SCC membership do not establish dependency permission.

Direct theory inputs checked against R112/R105:

| Input | SHA-256 |
| --- | --- |
| Source Generalize construction | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| Original intrusion parent | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `OriginalFormalAdmission.lean` | `77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c` |
| `OriginalCheckingAdmission.lean` | `77a8dd74f5913814d3628f0aed189be24b4aafc4780839eaa57237676a157da7` |
| `SourceLogicalOwnerBridgeR105.lean` | `6fecc134ac2009392f043331eb4d1a3dd479668208991e60c8a5d339e69b45b4` |

## Bounded derivation from the real producer

All following Rust line numbers refer to that immutable baseline.

1. `candidate_effect.rs:1896–1975`, `candidate_formal_annotation`, receives
   annotation, parameter, HIR occurrence and annotation scope. It obtains
   `level` from the parameter's live Value row and rejects an already retained
   formal domain. Its constructor call starts at negative variance with an
   empty structural path and fresh scratch permission vector.
2. Its recursive same-file helper (`:1613–1688`) builds polar Value pairs.
   Function argument traversal reverses variance; result traversal preserves
   it. Argument, Result and tuple Element steps are pushed and then truncated,
   so each retained permission has its original structural port path.
3. `candidate_formal_effect_port` (`:1690–1748`) maps an omitted effect port
   to a fresh row and a singleton symbolic port to the scope/name row.
   At a negative concrete-only port it creates a fresh open row and records
   parameter, HIR occurrence, annotation owner/scope, structural path, source
   row position and concrete effect identities. Its own comment explicitly
   rejects reading those members as a closed callback upper bound. Covariant
   explicit rows delegate to the source-owned signature construction.
4. After successful pair construction, the named owner calls
   `admit_candidate_value_link` at local slots 43 and 44, respectively from
   the positive annotation term to the negative parameter endpoint and from
   the positive parameter endpoint to the negative annotation term. It then
   transfers the permission vector into retained `formal_permissions` and
   stores the negative term in `formal_domains[parameter]` (`:1935–1959`).
   Those are actual producer calls, not a supplied checker transition model.
   The implementation of the link admission/propagation call is outside this
   read packet; its complete downstream semantics is not established here.

Conditional local conclusion: assuming this invocation returns `Ok(())`,
exclusive session mutation, and the called helpers honor their contracts,
the producer retains the negative formal domain and its constructed local
permission records after issuing both directional Value-link admissions.
This is a source-level control/data-flow derivation, not a kernel theorem or
runtime receipt. Failure/resource paths may return an error after intermediate
mutations; no whole-session rollback property is claimed.

The retained record's declaration (`:256–268`) states its limit exactly:
`FormalPermission` describes local source permission and is not an arrival,
provider, contribution or consumer witness. It carries no explicit incoming
description-frame key, actual-event key, event/proof telescope, Shared witness
or joint strategy. Such information might exist elsewhere in the compiler;
its absence from this record is not proof that it cannot be recovered.

## Permission-consumer seam and read boundary

`candidate_receiver.rs:2363–2379` contains the assigned
`internal_formal_permission_incidence` as an experiment wrapper. It requires
exactly one definition-use record, calls the session method of the same name,
then checks target owner against `schema.relay` and receiving owner against
`schema.answer`. It neither admits a proof payload nor alters a permission.
The wrapper is feature-gated and explicitly marked provisional with no
permission consumer. Its session-method implementation is outside the two
assigned files and was not inspected; this is an unresolved read boundary,
not evidence that the session method performs only those two owner checks.

The same-file readout seams reinforce the distinction: `:2619–2637`
(`current_internal_emission`) and `:2683–2703`
(`provider_entry_certificate`) obtain that incidence, read
`incidence.permission.entry_effect`, and build provisional emission/provider
evidence. Their comments also state that no consumer is connected. The outer
entry permission declaration in `candidate_effect.rs:269–285` is separately
typed `FormalEntryPermission`; the nested `FormalPermission` above has no
`entry_effect` field. Therefore publication by `candidate_formal_annotation`
must not be described as directly supplying this receiver's entry permission.
A connecting origin/entry/arrival law is still needed. Reading selected
projection code does not authenticate an arbitrary App or Lambda execution.

## Application to scoped admission and equality lift

The exact missing source-owned law is stronger than local annotation
permission: invert the original App/Lambda judgment at its actual generated
logical occurrence; construct the admitted ViewLogic/EventProof payload in
the original description/event telescope; decode to the same selected
descriptor (Value) or interface (Computation); retain the actual whole
operand, pattern/body checking and once Shared consumer evidence; and carry
this one lawful strategy through the qualified equalities and publication/use.
All App annotation alternatives, both Lambda entry modes and arbitrary
supported operands/pattern/body remain required.

The concrete formal producer is an actionable owner for tracing its input
annotation/scope/path into a future certificate. The receiver wrapper is an
actionable owner for authenticating which experiment/use requests incidence.
Neither supplies that missing law. In particular,
`OriginalFormalAdmission.localAdmissions` at lines 122–132 selects constructed
description/ViewLogic payloads locally but leaves `.eventProof` to
`base.logical`; changing that arbitrary relation is not justified by the two
Rust owners. R105's exact routes/telescopes remain syntactic correspondence,
as its handoff explicitly records.

Disposition: **NO_SAFE_CODE_SLICE** for closing R112's semantic premise from
these two owners. This does not assert no useful compiler change exists. A
permission-consumer edit here would skip the missing actual-event/telescope
and joint-strategy evidence; adding another owner ID or row equality alone
does not discharge it. No implementation is proposed under this research lease.

This packet supplies a bounded source characterization, no supported-source
counterexample and no proof that arbitrary admissions are realizable. It does
not duplicate the constructive lane's abstract countermodel. Original A/B,
effect hygiene, soundness, principality, termination, source/native and
production parents remain OPEN.

## Commands, coverage, resource receipt and next action

Read-only commands: `cat`, `rg`, `sed`, exact-path `git show`, `sha256sum`,
plus one `git ls-tree` lookup whose literal wildcard pathspec returned no
paths; subsequent exact-path `git show` reads succeeded. Full-file hashes
match the recorded baseline. No source search outside the assigned Rust
files, dirty/quarantined source read, Git mutation, compiler, Cargo, Lean,
Lake, test, build, generated cache, installation or environment experiment.
The sole write used `apply_patch` to this exact inbox path.

Coverage is static inspection of the named functions and directly relevant
same-file helpers/readouts, not exhaustive runtime paths. Seeds/ranges and
mutations: none. Oracle: immutable source plus independently selected semantic
specification; both share the primary's accepted language baseline. Source
comments describe intended evidence limits and are corroborated here only
by inspected data/control flow, not by execution. An external consumer or
certificate could strengthen the result; it was not searched beyond the
lease. R103 kernel failures/`sorryAx` and R105 unchecked status are untouched.

Budget: source lane 180 seconds; one lightweight read command at a time except
batched independent reads, no heavyweight processes. Exact wall/CPU/RSS were
not instrumented; no claim of measured compliance or remaining seconds.
No descendants or unresolved generated outputs. Writes stop at this revision.

Recommended next action: primary adjudicates the proof lane's missing
admission/transport law against these producer/receiver boundaries, then
leases the exact original local source-rule owner needed to derive it.

## Commit packet

- Exact leased/changed path: `tasks/agent-loop/inbox/effect-permission-scoped-admission-r112-source.md`.
- Baseline SHA: `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`.
- Changed dependency hashes: none; inspected hashes recorded above.
- Claim/review: bounded source characterization; UNREVIEWED, no independent certification.
- Checks already run: immutable-byte SHA-256 comparison and bounded static source trace only.
- Proposed message: `research: locate scoped-admission gap in immutable formal permission seams`.
- Shared deltas left to primary/curator: record NO_SAFE_CODE_SLICE within the two-owner lease,
  the external session-method read boundary, and the outstanding original-scope
  admission/transport law; keep all parent gates OPEN. No shared record edited.
