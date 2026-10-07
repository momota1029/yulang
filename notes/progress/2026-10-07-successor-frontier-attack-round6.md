# Successor frontier attack, round 6

Date: 2026-10-07
Starting remote baseline: `d8ddbb0a3a3ab80b7cca67de09a8310617ba1170`
Claim class: bounded source-rule and historical-mechanism attacks
Semantic, implementation and production authority: none

## Starting ledger

At the latest remote baseline, the canonical DAG contained 90 nodes and 196
edges: 7 CLOSED, 20 CONDITIONAL-CLOSED, 43 OPEN-PROOF,
19 OPEN-SEMANTIC, 1 IMPLEMENTATION-ONLY and 0 BLOCKED. This pass attacked
selected OPEN leaves in dependency order; it did not rebuild the inventory.

## Priority A: original Call output map and historical mechanism

Three distinct read-only analyses specialized Theorem C, performed last-rule
inversion, and audited the owning Function-signature/Call-elimination route
for the fixed captured `f x` Call. They agree on the result:

1. Theorem C and source-indexed realization preserve typed views and static
   maps supplied in the decorated source schema. Theorem C §2.6 requires those
   maps as inputs; it does not introduce the original-sort output map.
2. Typed-core §6 produces a body/result skeleton
   `Fun(P, Result(I_body))`. Typed-core §9 leaves the complete invocation
   interface `J_call` as an inference obligation. These rules do not derive
   an independently interpreted original complete signature for the captured
   formal, much less its original output correspondence.
3. Gen-Call-0 conditionally identifies an immediate decorated port and its
   `p_out(c)` address under a well-formed elaborated Function. Typed-boundary
   transport operates on supplied correspondences. Neither supplies the
   original commuting map.

The precise remaining two-stage cut is:

```text
L : resolved Call and Name incidences, with distinct source occurrences
G : formal registration, source root, upper-use demand and Gen-Call-0 schema
S : linked selected seed/exposure evidence at its original scopes
K : independent original complete Function-signature interpretation,
    including original capture/root dependencies
------------------------------------------------------- [missing]
b : original beta/root/position formation
kappa : TypedOutputCorrespondence_orig(
          U_c, outEff(U_c), p0; X,xi,original scopes)
commuting justification for the complete-invocation/signature/output incidence
```

`K` must not contain `kappa`; otherwise this assumes O0. `WF_Dec(F_c)` alone
does not supply the original interpretation. Keep `sigma_apply` and
`sigma_step`, the lexical Name occurrence and the Call checking occurrence,
and the immediate signature port and `p_out(c)` distinct. This is the first
missing static introduction on this route. O1 (`Slots_orig`/`Own_orig`), C0,
C1 and J0 remain separate downstream obligations.

The Frozen Oracle lineage supplies a **historical mechanism**, not current
semantic authority. Before provenance introduction, commit
`302e8be52ab93b5ddd54f923b2b25dc7c0c5aca8` already constructs an ordinary
`Neg::Fun` demand, links effects and emits `Expr::App` in
`crates/infer/src/lowering/expr/tail.rs`. Commit
`f0922ba32b63e767221c52b93c0bb9df3c2325b5` wraps that constructor with
`make_source_app` and retains arena-local application identity, source origin,
module and application/callee spans. Later commits add an
`ApplicationArgument` boundary before construction and argument-span
records. At frozen pin `a58eefc31e22141574b6f20c6a5748151c6d79f1`, this path
remains a historical Function-demand plus source-provenance mechanism.
Separate guarded frame/formal subtraction records a selected frame and formal
`DefId`.

This history does not interpret a current original Function signature, prove
the map `J_call -> kappa`, introduce `Slots_orig`/`Own_orig`, or assemble a
complete source contribution. Mapping those endpoints would assume the
missing source rule. The old implementation's behavior therefore remains
archaeological evidence only; no Oracle code was executed and no Oracle
semantics was adopted.

The result is a bounded route limitation, not a proof that no other source
producer exists, a source counterexample, or a pair of competing complete
semantics. No user decision is indicated.

## Priority B: open-world imports and recursive descriptor route

### INIT_WORLD

The open-world last-rule audit separates (i) the source/import binding map,
which may retain distinct aliases to a shared provider, from (ii) the
independently supplied semantic contract dependency map. A source-owned Name
can copy already supplied references and inert Lambda/Delay construction can
retain them; neither installs an independent semantic root at an importer
incidence.

The first missing introduction has this interface:

```text
independent external base at original (B_orig,xi,C0)
fixed semantic import clause Delta_i and its independent open premises
resolved importer-incidence/provider map
licensed rigid/hole dependency map for Delta_i
overlap agreement on provider, reference, state, operation,
  continuation, role/profile and live-owner evidence
------------------------------------------------------------ [missing]
Delta_i holds at importer incidence i; the extended tuple preserves
all old incidences by restriction; H_f and H_a remain hypothetical
```

Its action must commute with both old-tuple restriction and the retained
alias/dependency maps under each independently legal hole substitution, while
preserving the fixed interpretation of `Delta_i`. Source Renaming gives a
relation image, not this fixed-import introduction/action certificate.
Assuming completed extended-world validity would be circular, and closed
program reachability does not establish admission in every compatible open
world. This sharpens the W0 leaf; it does not prove its independent premises.

### REC_DESC

The direct two-closure construction for the cyclic `f/g` pair builds the
actual closure knot and operational Return/Request prefix while preserving
the actual provider, receipt, raw continuation and pending suffix. It still
cannot establish `DescMem(R_g,v_g;xi,w)`: ordinary cyclic Return acceptance
for the latent obligations and the exhaustive ordinary constructor clauses
are not available. The finite-history route retains the required failure
shape
`exists h. forall e. not LocalCheck(h,e)`; one failed evidence extension does
not refute `forall h. exists e. LocalCheck(h,e)`. Neither route closes
REC_DESC or introduces world validity.

## Priority A follow-up: CALL_TYPE

For the inert Name-callee subcase, if the original joint operand witness and
Name/Return typing are already granted, the unchanged state transports the
argument typing across that one prefix. The first missing independent
predicate is still sound realization of the whole-argument checking evidence
against the actual returned provider's carrier contract at the same original
incidence, jointly yielding `ArgCompatible`. The Authoritative Function-view
design leaves the detailed generation/realization open, and typed-core emits
the obligation without proving its compatibility. This matches the existing
CALL_TYPE leaf; the bounded attack does not establish the original inputs or
the SEM_JOINT law and changes no status.

## Before / after and next attack

| Gate | Before | After | Result |
|---|---|---|---|
| CALL_TYPE | CONDITIONAL-CLOSED | CONDITIONAL-CLOSED | Whole-argument checking realization remains open. |
| ORIGINAL_ASSOC | OPEN-SEMANTIC | OPEN-SEMANTIC | Original complete signature/output-map producer remains open ahead of O1. |
| INIT_WORLD | OPEN-SEMANTIC | OPEN-SEMANTIC | Independent importer-incidence introduction/action remains open. |
| REC_DESC | OPEN-PROOF | OPEN-PROOF | Ordinary cyclic Return acceptance and exhaustive constructor clauses remain open. |
| DAG totals | 7 CLOSED, 20 CONDITIONAL-CLOSED, 43 OPEN-PROOF, 19 OPEN-SEMANTIC, 1 IMPLEMENTATION-ONLY | unchanged | No status or edge promotion. |

No new semantic clause was proved. No admitted-source counterexample or
complete alternative semantics pair was found. The next highest-leverage
attack is to expose an independently justified original Function-signature
formation/elimination clause with premises that actually discharge `K` and
produce the commuting O0 map. If no such clause exists in the source theory,
attack its minimum construction directly rather than adding transport
wrappers. In parallel, derive the W0 import introduction from the owning
semantic-import contract, and keep `CALL_TYPE` at the concrete
checking-to-`ArgCompatible` leaf.

## Scope and checks

Eight bounded, read-only producer analyses covered the above routes at the
pinned baseline; direct dependencies were checked against that baseline where
the reports provide comparisons. A separate historical lineage audit read
immutable Oracle blobs/commits and did not run Oracle code. The DAG was
regenerated and validated at 90 nodes / 196 edges with unchanged statuses.
`git diff --check` passed. No tests, builds, semantic executable checks,
performance measurements, or compiler changes were made. The existing
default-off shadow crosswalk is unchanged; its nested/grouped pending-Apply
and eight-address join was already present at the pinned baseline, so no
duplicate plumbing or test change was made. Independent compiler-referee and
spec-auditor reviews found no blocking, major or minor issue in the stated
semantic boundaries and authority labels. Those reviews did not independently
reproduce the historical blob lineage, DAG checker execution or production
conformance.
