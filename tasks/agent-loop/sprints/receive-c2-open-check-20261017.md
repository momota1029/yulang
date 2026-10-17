# Sprint `receive-c2-open-check-20261017` — derive the actual open second Call

Status: CANDIDATE until the primary freezes the hashes and grants the exact proof lease.  
Branch / baseline: `research/simple-sub-intrusion` / `a65ce9d07`.  
Parent: user goal `型推論と実行器が証明込みで実装できるまで続ける`; original theorem and production gates remain OPEN.  
Authority: user-authorized process change permits drafting candidate bridges for independent review. It does not adopt new semantics, narrow the original domain, authorize compiler code or close a parent.  
Contract revision: 1.

## Original outcome and success evidence

The original obligation is `FORWARD-FIRST-CALL`, especially its independent
context hypothesis at every original `A1,E1,xi=(nu,K,D)`, provider, scope,
current world, pending requests, responses, raw continuation and future-use
developments. Preserve the all-compatible-context domain and the full original
quantifiers. The selected source fragment remains
`receive(f : Unit -> alpha+) = let g = f(Unit) in g(Unit)` with
`alpha+ = ([ctrl]Unit) -> [ctrl]Int`.

The reviewed structural result already shows how a checked open suffix would
plug into the existing source graph. This sprint asks whether the actual
source-selected second Call `c2 = g(Unit)` supplies that derivation at the
original `A1,xi`, or where the first exact descriptor/checking law is absent.
Do not substitute `alpha+` for `A1`; do not use an actual `c1` return,
acceptance, receipt, installed `g`, selected provider trace or native success.

Success is either a source-rule derivation of all five original c2 obligations
at their unchanged dependent coordinates, or the first exact missing law,
owner and falsifier. Apply any derivation to the frozen structural plug and
name the enclosing Bind bound, unchanged residual, world/import/profile join
that still remains. An obligation inventory alone is insufficient.

No semantic bridge is assumed necessary. If the existing selected rules truly
cannot express a required source step, draft only the smallest candidate rule
with premises, conclusion, preservation law and falsifier; leave it unselected
for fresh independent review and the existing adoption gate.

## Two continuing lanes

### Proof lane

One bounded Astra constructive proof assignment may proceed through these
related stages under the same exact lease:

1. Fix the original `A1,E1,xi`, source Function `F2`, c2, and Unit argument
   positions. Derive `WF_Dec(F2;xi)` from the original selected source
   constructor or identify its exact missing descriptor premise.
2. Derive the full `VIncl(A1,F2;xi,e_f2)` from the unchanged original incident
   constraints. Prove it for all original decorated values in `A1`; never
   replace it with a convenient single inhabitant or a narrowed carrier.
3. Construct the original `WholeArgCompatible` for `Result(I_a2)` and the
   actual `CarrierContract(F2)`, together with the original `ReceiveSchema`.
4. Construct complete `CIncl` for the original invocation image, retaining
   pending observations, responses, raw continuation and future developments.
5. Reuse the reviewed structural plug proof at the exact same overlapping
   coordinates; identify the remaining enclosing Bind/residual/world/profile
   obligations without claiming that c2 alone proves them.

Allowed outcomes: constructive source derivation; source-qualified
counterexample; or the first exact unavailable premise/law and owner. A
counterexample refutes only its stated source instance and never grants
production. No actual c1 execution evidence may form the challenge.

### Implementation lane

Luna/high owns a read-only readiness audit of the already approved source and
runtime owners. Inspected owners for this sprint:

- `tools/inference-playground/src/lib.rs` — `prepare` returns
  `(HirModule, CandidateInference)`; `execute` currently discards the
  candidate and constructs runtime from HIR.
- `tools/inference-playground/src/runtime/program.rs` — `RuntimeProgram::from_hir`
  builds execution structure from HIR and carries no independently checked
  source `T` importer.
- `crates/yu-solver/src/shadow_apply.rs` — `CandidateInference` is a candidate
  constraint/graph result, not the original source derivation.

Observed hashes are recorded in `current.json`. This establishes
`NO_SAFE_CODE_SLICE` for this sprint: the proof does not yet supply source `T`,
the existing producer/importer contracts are reviewed but unapplied, and an
implementation would have to invent or trust the absent certificate. No code
lease, test/build/probe/execution allocation, semantic adoption or cutover is
granted. Reassess after the proof changes the source evidence; do not repeat the
producer/importer mapping.

## Frozen inputs and exact authority

Recompute these SHA-256 values before use. Any mismatch stops only the affected
inference pending a primary-authorized delta.

| Input | SHA-256 | Bounded use |
|---|---|---|
| `notes/progress/2026-10-06-initial-context-source-construction.md` | `10e86ed3bac72d91f03c83acf50ed8e8336ab3c3d0df4a90a03cbe4efdc7ef75` | Original source Call/Bind rules, c2's five generated obligations, conditional inversion. |
| `notes/theory/2026-10-17-receive-resultbind-context-plug.md` | `90a0844f10ea433bb21c0d98e67a278e288930752987c233c86290354067bf87` | Reviewed same-tuple structural plug and exact outstanding premises. |
| `tasks/agent-loop/inbox/20261017-receive-resultbind-context-plug.md` | `cc883103ed36f538be299215061b23b0f4e12c18d9e85e8fd439fab993e48482` | Frozen prior handoff and review boundary. |
| `notes/theory/2026-10-16-first-call-joint-forward-preservation.md` | `f71cc442bcccb23f7e6f1aa6221b089abb8c24d1c4ce01fecef37995541c16b6` | Original parent assumptions and unaltered quantifiers. |
| `notes/theory/2026-10-16-written-unit-arrow-inlet-construction.md` | `ce0846a783af6029c346a6bc82664bd920b6a46429601a4030dd656a3fb07099` | Selected Unit carrier/inlet construction; independent premises remain. |
| `notes/design/2026-10-16-source-application-checked-result.md` | `c9207625887d78aaccef988324e8505f6dd08fdfe076e0f564f8b7dca3c54076` | Original Apply-owned A1/E1 coordinates and complete source result view. |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` | Full Function membership domain; no narrowing to one convenient provider. |
| `notes/design/2026-10-17-receive-context-plan-producer-contract.md` | `f491aa97bb2828111c7f46eb4f65cca9b7d3e00886c83cfa3ff21a7f43856f05` | Confirms current source T producer gap; reuse without redoing the mapping. |

Implementation audit pins, for read-only evidence only:

| Owner | SHA-256 |
|---|---|
| `tools/inference-playground/src/lib.rs` | `b65cfd7200e459c9448438ec979ffeb9eddb35c282600349cebe7ddf3b759bbb` |
| `tools/inference-playground/src/runtime/program.rs` | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` |
| `crates/yu-solver/src/shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` |

## Leases, review, resources and stop conditions

Exact proof artifact lease:

- `notes/theory/2026-10-17-receive-c2-open-check.md`
- `tasks/agent-loop/inbox/20261017-receive-c2-open-check.md`

One Astra proof author, maximum 720 seconds, one author at a time, no
descendants. No implementation file lease. Luna's above read-only inspection
does not transfer ownership of those code files. After freeze, assign a fresh
`compiler_referee` review (120 seconds), then a fresh `spec_auditor` review
(120 seconds), sequentially. Coordination 60 seconds, reserve 180 seconds,
total cap 1200 seconds. Retain the three inherited UNKNOWN reservations and
quarantined leases. Unused budget is retired at the sprint boundary.

Review must check every original c2 conjunct, same-`A1,xi` witness identity,
all-value inclusion, whole-carrier and full invocation-image coverage,
dependent scopes, no actual-return circularity, and honest residual obligations.
No author/coauthor reviews their own work. Material findings stop for Luna
adjudication; repairs require a new bounded allocation.

Stop on a frozen derivation/counterexample/first unavailable exact law, any
dependency or scope mismatch, the budget boundary, or user/session STOP. No
compiler change, semantic adoption, tests, builds, probes, execution, native
MODEL establishment, source admission, parent closure or production cutover.
Only Luna integrates, stages the explicit reviewed files, checks the full
outbound range and pushes non-forced.
