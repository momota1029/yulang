# R — Force normal-return constructor audit, revision 1

Status: **FROZEN candidate source audit; O-RESULT remains OPEN**. The requested
`force_return_rows_source_derivation` was attempted but not established. This
is an exact-blocker submission, not a conditional theorem or a semantic choice.

## Assignment and frozen inputs

- Sprint: `FORCE-ADMIN-RESULT-DISCHARGE-20261025/r6`.
- Contract: `tasks/agent-loop/sprints/force-admin-result-discharge-20261025-r6.md`,
  SHA-256 `972a6cd97e340e1d0d0564e0f76a21021cf1877b7ba21f1df1db7aa56ba1b581`.
- Assignment/handoff ID: `R/FORCE-RETURN-ROWS-20261025`; revision **1**.
- Author: `/root/force_return_rows_prover_r6`; primary `/root`; session
  `FORCE-SOURCE-REALIZATION-20261025/root-turn-1`. Actual receipt: this leaf
  received the stage-one packet and performed the source/hash reads reported
  here. Requested model/effort: `gpt-6.1-sol` / `high`; effective observed
  model/effort: **UNKNOWN / UNKNOWN**. No coauthor or descendant.
- Baseline supplied by the primary/current snapshot:
  `9b945b0bb175e8e0919d388dc720babbdf0c2464`; no Git command was run.
- Sole output/write lease: this inbox file. The conditional
  `notes/theory/lean/YulangClosure/ForceReturnRows.lean` lease is **unissued**.

All contract/input digests below matched. These pin bytes and do not promote
candidate declarations to checked proofs.

| Input | SHA-256 |
|---|---|
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| F: `inbox/20261025-force-result-flow-derivation.md` | `a849f178fbc55eb653c2fc4295e4b4675935e7c904cbef7da5100edb0b983212` |
| P: `inbox/20261025-force-source-input-equations.md` | `d7f8853e07cf2ec73fb99d3cbe045f3ab5b2e6f5626469417648a9fbfc313f88` |
| r5: `inbox/20261025-force-source-mapop-correction-r5.md` | `203d55dc462046f0616eba027198c68224182fdf4ab03bf19ccb87548c691b8b` |
| r5: `sprints/force-source-mapop-correction-20261025-r5-outcome.md` | `04e93d203dbf09f2421be4ef988328330ccecb5997b3e01564178d8b195ed823` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `CoreSubstitution.lean` | `fc73d6d60d28f2abb54049a5715751d27df47ad93dbeb8f52966cf98a747bd2f` |
| `ControlTyping.lean` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `ControlComposition.lean` | `9a48a5f2ef15eb947478757e0fa74457579183ccdbab90f2518886590e33fc40` |
| `CoreControlBridge.lean` | `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a` |
| `CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |

`inbox/` and `sprints/` abbreviate `tasks/agent-loop/`; module names abbreviate
`notes/theory/lean/YulangClosure/`. F's author is
`/root/force_result_flow_research_r4`, P's is
`/root/force_source_input_research_r4`, and the correction's is
`/root/force_mapop_correction_r5`. Other dependency authors are not inferred
from their filenames; their identities remain UNKNOWN in this receipt.

## Parent and unchanged scope

The parent is complete Lean semantics and type inference. This packet targets
the O-RESULT source premise required before Force realization and downstream
Call step erasure/successor coverage. The intended claim ranges over **every**
retained refined typed Force/Delay derivation, its consistent type/dictionary/
metadata interpretation, and **every actual finite normal body return**, with
every component and latent path of the result retained. It is not restricted
to base results, empty profiles, direct syntactic delays, a single alias, or a
chosen body-return path. Bare execution typing is insufficient (paper
1180–1192, 1579–1581). Original Call A/B and independently supplied foreign
continuation quantifiers remain unchanged and OPEN.

Source citations below are line numbers in the pinned operational paper.

## Attempt 1: construct bottom-up from retained derivations

Let `t` be the actual interpreted forced value-view occurrence, of refined
type `U(E,A)`. Its resolved Delay carries the body derivation `D_M` and the
actual captured packets `c_i`. Let an actual execution of that body reach
`Ret z`, with returned packet `z:A`. Write `r:A` for a separately materialized
normal-result occurrence, and `o:A` for a fresh enclosing result occurrence
if the chosen expansion materializes that further interface. Distinct names
do not assert that the paper requires two separate return allocations.

Let `P_A` denote the legal finite value-interface/component/latent paths of
that retained result instance. This does not choose a new root-path encoding.
It includes the complete latent interface, not just effect endpoints. A
finite guarded typed template may denote infinitely many finite members
(611–624, 1194–1209); finite template is not finite path enumeration.

| Actual occurrence / construction | Derived result and exact extent |
|---|---|
| Captured `c_i`, stored Delay body | Delay preserves code and captured packets, stores the body graph at the force port, and creates no executing View or immediate event. It does not create a direct Flow from every capture to every future result (1244, 1256–1257, 1473–1479, 1531). |
| Actual operand `t`, including its real alias/type-instance lineage | The actual operand supplies the Force View at `force.effect`; preceding Var/type application has its own identity transport and one simultaneous packet substitution (1241, 1245). Constructor equality cannot substitute another operand occurrence (543, 556, 609–610). |
| Actual returned `z` and `Ret` result `r` | The return's input is `z`; a fresh output is required for its recorded transport (582–583). Its exact typed template is `Id_A = {(p,p) : p in P_A}`, with domain and image `P_A`; it transports every latent path and contributes immediate effect zero (1528). |
| Existing body provenance ending at `z` | It reaches `r` by composing the actual preceding routes with this Ret identity, matching both occurrence and port. This introduces no new Boundary, Admit, source receiver, or profile (596–610, 682). |
| Force execution occurrence `j` | At an actual emission inside the Force body, `Observe(q,t,force.effect,j)` is contributed by that executing View, alongside all other executing Views (560–562, 588–594, 1245). `j` is an execution occurrence, not a second input value packet. |
| Force normal leave, incoming `r` and operand-result interface associated with `t` | The paper requires a separate result transport and connection of enter/body/leave (485–492, 1245, 1532). I did not derive the concrete new Flow row batch, its exact incoming occurrences, or its typed membership equation from those rules. |

The last row is the first failed constructor application. Captured packets are
already represented by their actual executed body routes; adding direct
`c_i -> o` rows would invent provenance. Administrative aliases/wrappers
likewise need their actual existing transport and consistent interpretation;
they are not interchangeable additional incoming sources. A Flow from `t`
cannot be replaced by a Flow from its underlying Delay node without that
lineage. Force introduces no Call receiver (557–559, 1256–1257).

For clarity, the frequently suggested two-row completion would be:

```text
Flow(r, o, Id_A)
Flow(t, o, StripFR_A)
StripFR_A = {(force.result · p, p) : p in P_A}
dom(StripFR_A) = force.result · P_A; image(StripFR_A) = P_A.
```

This is **the unproved target equation**, not this packet's constructed rows.
The exact occurrence granularity is also unproved: fusing the Ret interface
with the Force output needs an explicit composition equivalence, not renaming
`r` to `o`. Permission for prefix-substitution templates (611–613) does not
establish that this particular constructor emits `StripFR_A`.

Every latent row would have to follow uniformly from its membership equation.
For example, when `A = U(E',B)`, the candidate would carry
`t:force.result.force.effect -> o:force.effect` and
`t:force.result.force.result.p -> o:force.result.p`, plus the corresponding
identity rows from `r`. The remaining `p` is unchanged. It cannot be replaced
by `force.effect`, an immediate event, or a path-color equality. Tuple,
nominal, recursive and instantiated abstract descendants require the same
all-path law, using their actual retained typed templates. The nested-delay
example at 1994–1998 confirms that latent execution is later; it supplies no
missing Force-leave membership equation.

Thus Ret identity is applied back to the parent: it removes any need to
reprove body-return propagation, while leaving precisely the enclosing Force
result construction. It does not discharge that construction.

## Attempt 2: inspect the actual Lean producer/consumer interface

I changed method from the preceding source-rule inversion to an audit of the
actual pinned representation owners. This cannot replace source evidence, but
it identifies why a proof over the existing carriers cannot recover it.

- `CoreSyntax.lean:208`, `TypedCall.PortKind`, has `carrier`, `callEffect`,
  `result`. It has no distinguished Force-effect/result constructor. Numeric
  component labels could encode them, but no checked source interpretation of
  such an encoding is supplied by this declaration.
- `TypedCall.ValueTyped.delay`, `.view`, `CompTyped.force`, and `.expose`
  (`CoreSyntax.lean:269–284`) retain execution types, and permit arbitrary View
  occurrences. They retain no refined Force/Delay template or source-licensed
  Force-return row evidence. The paper expressly limits unrestricted View
  typing to the execution-type projection (1579–1581).
- `TypedCall.PathRule.adapterMap` (`CoreSyntax.lean:228`) accepts arbitrary
  endpoints. Building a correspondence with it would assume source licensing.
- `Control.Metadata.viewReturn` (`ControlSyntax.lean:96`) has type
  `World -> Nat -> World`. It receives neither the actual returned packet nor
  a typed path template; it can consult an independently established World
  representation, but the signature itself establishes no such invariant.
- `Control.CallControlStep.returnExpose` (`ControlSyntax.lean:353`) wraps the
  returned value in `resultView` and calls `viewReturn` on its identity. It
  records no explicit Flow batch. Its existence does not prove that an
  actual source Force constructs this result view/template or that World
  interprets it with the required two incoming lineages.
- `Original.Principal.forceDelay` and `principal_preservation`
  (`CoreExecution.lean:10,16`) establish bare Force beta/type preservation in
  their fragment. They do not retain or prove metadata transport.

These are inspected candidate/native-carrier facts, not checked r9 theorem
premises. No production compiler/native correspondence is established. The
paper's finite-cell construction also cannot repair the omission: 1346–1349
and 1404–1421 generate a relation from an **already specified** primitive
correspondence. Approximation by all candidates is an abstract representation
step, not a license to choose concrete Flow rows.

## Exact blocker and next owner

The smallest missing evidence is the **normal Force View-result construction
equation at the source decorator**, including the designated result-prefix
correspondence and concrete input occurrence allocation. Its owner is paper
`d`, the Force row at 1245 together with Delay storage/Force reconnection at
1531–1532, and the normal expose return described at 485–492. Its downstream
consumer is a future source-licensed replacement/refinement of
`CallControlStep.returnExpose` / `Metadata.viewReturn`.

The required input is the retained refined derivation and actual normal
body-result packet, not endpoint typing alone. The required owner output is
an independently defined decorated normal-return transition exposing its new
rows. One must then prove the row/domain/image equation from that transition.
Defining the transition to mean the desired row equation, or adding an opaque
`forceRowsCorrect` field, would leave exactly the same premise assumed.

There is presently no honest theorem signature for the requested full claim
using only the actual pinned Lean declarations: they lack this source-indexed
transition and refined template interpretation. I therefore use the contract's
**precise-blocker** acceptance branch, rather than introduce prospective names
and present them as existing imports. A future proof module would at least
import `YulangClosure.CoreSyntax` and the separately approved source-decoration
owner; the latter is absent and is a dependency/authority boundary for Luna.
No Lean file should be activated on the assumption that an arbitrary
`PathCorrespondence` fills that boundary.

No new semantic ambiguity is claimed. I did not construct two fully
source-admitted systems with different Path/Eligible. In particular, dropping
the strip row in one invented graph would not establish source admission.
The result agrees with F's bounded missing-derivation characterization; it
does not refute the claim that the accepted source fixes Force behavior.

**Mutual TODO `R6-R-FORCE-LEAVE-OWNER-1` (owner: Luna/source-decoration lane):**
consume this audit against O-RESULT; obtain or derive the single source-owned
normal-return transition above, preserving actual body-result and operand
lineages and every latent suffix. Inputs are the pinned paper, retained
refined Force/Delay evidence, actual normal return, and current interpretation.
Proposed output is that exact constructor equation with a noncircular source
derivation and occurrence allocation. Falsifier: a claimed row batch either
loses an actual body-result route, loses an operand `force.result` route,
adds a route from an unrelated capture/alias, or changes any retained latent
suffix; observe its consequence only at a later genuinely executed View.
If the two-row completion is selected, the incidence consequence for a fresh
output must be derived for every source Boundary/receiver/path from the actual
rows; it cannot be supplied as an invariant premise of the constructor.

This is now an owner/input obstruction after source inversion and carrier
audit. Another proof packet with the same erased carriers and an assumed
`ForceReturnRows` witness would repeat it. No production code slice is
authorized or proposed here; the immediate next step is Luna's source
adjudication, with the R Lean lease left unissued. N may progress independently.

## Reuse, checks, resources and STOP

Reused F's exact Ret consequence and separate observation/result distinction;
reused P's occurrence/context distinctions only as candidates. Consumed P's
mapop claims through the independently CLEAN r5 correction and outcome; no
unconditional continuation-input-type invariant was used. Rejected the Draft,
Ret-only inference, arbitrary `adapterMap`, endpoint type equality, bare Force
beta, and later preservation summaries (1777–1790, 1880–1896) as substitutes
for the missing constructor evidence. No inference generation, propagation,
levels, extrusion, intrusion or generalization rule was changed.

Checks were source/declaration reads and SHA-256 comparisons only. One initial
hash command tried nonexistent `lakefile.lean`; locating `lakefile.toml` and
hashing it matched the contract config pin. This was a locator correction,
not a changed dependency. No Lean/Lake invocation, executable checker, code,
test, build, compiler/native probe, Git operation, nested CLI, scratch file,
external contact or delegation occurred. Only this report was written.

Resource cap: one R author, 1,200 seconds total across both stages, one CPU,
1,024 MiB; no stage-two work. First clock observation during work was
`2026-10-25 00:32:25 UTC`; another pre-freeze observation was
`2026-10-25 00:35:00 UTC`. Exact dispatch/start elapsed time, CPU and peak RSS
are UNKNOWN; conservatively charge the full 1,200-second individual grant
under the contract. No unused time or stage-two budget is claimed here.

**STOP receipt:** revision 1 is final. After this write, only read-only final
pin/report hashing and the handoff remain. No descendants, scratch/generated
outputs or unresolved descendant leases exist. All authored writes stop;
this worker does not continue while awaiting review. Artifact digest is sent
externally with the frozen ID/revision, avoiding a self-hash. Fresh independent
review and Luna adjudication remain required; this author cannot certify it.

Commit-ready status: **pending source review; parent OPEN**. No commit/push or
shared-state edit is part of this packet.
