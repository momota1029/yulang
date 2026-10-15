# Native Call-result profile transport: owning-construction audit

Date: 2026-10-15
Status: independently reviewed bounded source audit; first unresolved construction identified
Primary-pinned baseline: `0a9af0da5080469f930da0032aa96d7d89d358c5`
Lease: this file only; no implementation or theorem-status authority

Independent review (2026-10-16): `ordinary_carrier_semantic` accepted this audit
at SHA-256 `3168611e0fe633bc39debbbd3d286437b594888c7ee0cc396f5514c4a1c93b26`
with no findings, checking all seven native source hashes and the reviewed
source-classification dependency. This certifies the bounded inventory and
location of the unestablished premise, not a Call-preservation theorem.

## Objective and authority

Audit whether the original independently justified profile/seed and inherited
evidence remain attached to the **same** returned typed packet through
Call-result, local install, actual copies, capture, FreshUse restoration and a
second Apply. The fixed source case is

```yu
my receive (f: () -> 'a) = {
    my g = f();
    g()
}
```

The reviewed [source classification](../theory/2026-10-15-callback-result-exposure-classification.md)
§§1,3–5 supplies the source meaning: the first complete Call has one original
joint assignment `xi=(nu,K,D)` and one actual return witness `W`; result
transport combines the actual-value input and matching callee-result input,
then ordinary binding/read use identity. It creates no new outer-formal seed
at `g`. Its review at `f267a08e2` is supplied by the primary; the historical
pending-review footer is not a new review verdict.

Other governing sections are [callback context](../design/2026-10-03-callback-context-delivery.md)
§§2,2.1,4, [typed transport](../design/2026-10-02-typed-boundary-realization-draft.md)
§6, [directional introduction](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
§§2–4,6 and [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–4. Normative B still delivers the authentic original callback context
before body generation, independently synthesizes endpoints, then compares
the completed interfaces. This audit chooses no replacement semantics.

## Result: stop at the first Apply's source/native result interpretation

**Claim class: bounded source/artifact characterization, not a counterexample
or preservation theorem.** The first unresolved owner is the native result
construction for the first Apply. The inspected constructor establishes a
symbolic result endpoint and Function covariance. It does not yet establish
that the resulting relation denotes the original complete Call's same `W`
and both indexed source packets under the original `xi`.

This is a precise prerequisite, not observed destruction of an already
constructed packet. In particular, the absence of profile fields on
`LocalScheme` does not demonstrate loss: the live root, relation contexts,
bound evidence and attachment bundles provide other retention paths.

The derivation of the stop is:

1. `candidate_source.rs:978–1020` retains the authentic first Apply recipe,
   actual source callee/argument indices, shared result component, checking
   occurrence and cause. `shadow_apply.rs:1548–1625` resolves those endpoints,
   constructs the negative Function demand with that result in field 3 and a
   separate invocation-effect field 2, and admits the callee inequality.
   Neither success of that admission nor later Function shape was used as
   evidence of an original returned packet.
2. When Function decomposition is reached, `lib.rs:12590–12618` generates
   exactly the Result child `lower.result <: upper.result`, separately from
   ResultEffect. `candidate_context.rs:3020–3063` preserves the inherited
   post-check context and source references and records the FunctionPort
   dependency. Thus there is a real scalar/relational Result path; claiming
   that it is absent would be incorrect.
3. The direct source observer explicitly keeps the remaining construction
   separate. `candidate_call.rs:268–280,330–359` borrows the source expressions
   and native interface; `PendingCallConstruction::suppliers` at `376–393`
   unconditionally retains `OriginalGenCall0`, `ArgumentReifyAndWholeCarrier`
   and `ReceiverDispatchAndCompleteResultFutureInterfaces` as missing
   suppliers. This declaration alone is not the proof of a gap: steps 1–2
   identify the actual constructed object as a native constraint and its
   context derivation. The missing justification is its interpretation as
   the source-selected indexed result image, with the actual returned packet
   and callee-result packet referring to the same provider/return witness.
4. `EvidenceSnapshot` at `candidate_context.rs:493–496` retains a bound key,
   relation, admission/emission heads and coverage. Capture/import preserve
   these references. They can preserve an established source witness; their
   retention does not independently establish the source meaning of their
   originating result relation. No conclusion here says that such a witness
   cannot be encoded by those heads and their referenced dependency graph.

Consequently the first obligation is to establish the source interpretation
at these Apply/Result owners. This audit stops there rather than proving a
new theorem with that very obligation assumed.

## Preservation inventory and coverage boundary

The table records actual native mechanisms, not a claim that every row
implements the source packet semantics. Later rows inventory available
retention without treating the unresolved first row as discharged.

| Seam | Actual producer/consumer evidence | Established bounded fact / remaining boundary |
| --- | --- | --- |
| First Apply result | `candidate_source.rs:978–1020`; `shadow_apply.rs:1548–1625`; `lib.rs:12590–12618` | The shared source result component is field 3 of the demand and target of the covariant Result child. Same-`W`, indexed two-input packet interpretation remains the first prerequisite. |
| Directional demand versus returned value | `candidate_context.rs:3041–3052` | A demand is authenticated against its original Function root, consumed once at Function dispatch, and produces a scope transformer only for AE/RE. Result does not manufacture a second directional seed. Clearing this demand is not evidence that an independently inherited result profile was erased. |
| Original inherited context | `candidate_context.rs:3024–3040,3054–3063` | Result preserves the parent's post-check context and sources and records the parent/child FunctionPort edge. This is stronger evidence than inspecting only `ScopedFlow.demand`. Its source-packet interpretation remains unproved here. |
| Actual level copy | `lib.rs:12500–12550`; `candidate_extrusion.rs:93–128`; `candidate_context.rs:2977–2997` | Copy allocation retains actual parent/copy and processing evidence; a rewritten whole Function keeps a corresponding demand root. Numerical equality of the original annotation, Apply result and later Name rows is unnecessary and was not assumed. Whole-packet correspondence across arbitrary histories is not established. |
| Local install | `candidate_source.rs:794–815`; `candidate_scheme.rs:1429–1448` | Install stores the initializer's actual value root, local identity, boundary and capture region. Initializer effects separately enter the block at source slot 20 and are excluded from later value freshening. No new formal registration is constructed. |
| Name lookup | `candidate_source.rs:912–945`; `candidate_scheme.rs:1475–1494` | Published Local Names select the installed slot. Capture starts from that scheme's live root/boundary and owned capture region, rather than rebuilding the initializer or registering a formal seed. |
| Capture | `candidate_scheme.rs:557–600,604–652,766–850` | Every visited local row bound retains its source bound, relation and interned evidence snapshot. Reachable Function fields keep ordered kinds/signs; contexts, deferred demand roots and attachment bundles are retained. Older nonlocal rows intentionally stay shared anchors. This is not proof that a particular source profile is reachable from the first Call's root. |
| FreshUse | `candidate_scheme.rs:1088–1099,1189–1270,1306–1331` | One canonical row map reconstructs all four Function fields; contexts and snapshots are imported; scoped demands keep original call identity while actual local scopes/inputs and demand roots are remapped. A fresh use does not independently select source witnesses. |
| Restoration and Name publication | `candidate_scheme.rs:1333–1379,1616–1637` | Each captured bound imports its antecedent snapshot, source bound and mapped relation. The Local cursor processes every bound/restoration before admitting the fresh root into the Name component. This is a real ordering barrier; replay semantic completeness is not certified by this audit. |
| Second Apply | `candidate_source.rs:618–628,950–1020`; `shadow_apply.rs:1590–1618` | Unscoped collection constructs its own demand from the Name component. A Local Name has no parameter `formal_name`, hence this direct omitted-formal branch supplies no new seed. Independently carried evidence is not disproved. |
| Scoped collector | `candidate_source.rs:965–975` | The Local-callee guard returns availability failure before constructing the second Apply record. It is a current experiment coverage boundary, not packet loss, a source rejection theorem or authorization to remove the guard. |

## Exact next action and exclusions

Assign the first-Apply/Result owner a source-to-construction obligation:
identify the original complete Call witness and show that the actual Result
relation/dependency graph represents the tagged images of **both** its
actual-return packet and matching callee-result packet under that same
`xi`, including original profile/seed identities and dependent incidences.
Consume the established source result rule and existing evidence graph; if
an input is genuinely discarded, identify that producer before selecting a
retained-certificate repair. This is one owning prerequisite, not a request
for another supplied-packet transport lemma or a new profile table.

No scoped-guard removal, new outer-formal seed, positive marking of all result
leaves, changed callback semantics, narrowed source parent, compiler edit or
theorem-status change is proposed. The original-coordinate/capture lemma and
the exact native residual prototype that bypasses capture do not discharge
this changing local-result history. Full replay, recursion, execution,
live receiver/event incidence, soundness, principality and cutover remain
outside this bounded audit.

## Method, checks, resources and freeze

Method: static reading of actual constructors and consumers, independent of
the source theorem's derivation. Shared assumptions are the primary's pinned
production baseline and accepted source meanings; no independent operational
oracle or executable experiment ran. No generated transition model was used.
There are no seeds/ranges, mutations, timings or search counts to report.
The failure condition for a preservation claim is the absent source/native
Result interpretation above; no operational falsification is claimed.

Commands used: bounded `cat`, `sed`, `rg`, `nl` source reads and `sha256sum`
on the dependencies below. No Git commands, builds, tests, probes, network,
delegates or writes outside this lease. Up to three lightweight read-only
shell commands were batched; zero heavy processes. Budget was 25 minutes; wall/CPU/RAM were not
instrumented. Dependency hashes were recorded at freeze; direct comparison
with the baseline commit belongs to the primary because this packet forbids
Git commands. Native sources were supplied as stable by the primary.

```text
26abb65f09f2dcf7b3f798329d7f9cf867d3e6196b4cd79c03b3b558d90566e5  crates/yu-solver/src/candidate_source.rs
436687cbc8c4ea372d0066f3f8a8e46cfc28223ade163f49864cd3c5039c60e6  crates/yu-solver/src/candidate_scheme.rs
270ee70b331e4095f404fafafdf0731b57dd451c130cdf251aea2b5944d7cc6c  crates/yu-solver/src/shadow_apply.rs
4689e2ee34c69c9492ecc1a58af15d7c802f44dca82d69f76e3e1520d8d5f3dd  crates/yu-solver/src/candidate_call.rs
9f71c8c40d6850bffccb27d7393bf6219f0ceca5cf1fe1e738073ea943706083  crates/yu-solver/src/candidate_context.rs
2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b  crates/yu-solver/src/candidate_extrusion.rs
a37c0c605802fc482c20a59199eea7a09b56ab966454db2b11dfe2d62b1dead7  crates/yu-solver/src/lib.rs
6f2bc05137e451c38391655bb2d45e9224f12eebf7d58c7f5a78c8abd69c93f4  notes/theory/2026-10-15-callback-result-exposure-classification.md
df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5  notes/design/2026-10-03-callback-context-delivery.md
db9c2728cd1fce99d450bb16df2ff0671b4ebca7561f63d31f57d0c6200a34f7  notes/progress/2026-10-15-callback-context-delivery.md
f11c6594e43c29fbfdbca1638b5c548cecc12a5beb192cac743e60f022c1cc73  notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md
1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb  notes/design/2026-10-02-typed-boundary-realization-draft.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
```

## Commit packet

- Exact leased path: `notes/progress/2026-10-15-native-call-result-profile-transport-audit.md`.
- Baseline: `0a9af0da5080469f930da0032aa96d7d89d358c5`; changed dependency
  hashes relative to that SHA are not independently checked by this no-Git
  leaf. Freeze hashes above let the primary perform that check.
- Review: bounded characterization independently reviewed as recorded above.
- Checks: static owning-source reads, dependency hashes and a clean trailing-
  whitespace scan; no executable
  validation. Artifact is frozen on handoff; further edits require the
  primary to return the lease.
- Proposed checkpoint message: `research: audit native Call-result profile transport owners`.
- Shared deltas intentionally left to primary/curator: retain the original
  parent OPEN; record this first Apply/Result interpretation prerequisite and
  the positive retention inventory; keep scoped Local-callee coverage separate.
