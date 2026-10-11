# Value incidence: local identity and the retained fresh-use bridge

Status: frozen bounded source characterization; unreviewed research checkpoint
Parent all-source/all-history/actual-retained-pair gate: OPEN
Baseline: `d8c097e1f810fb26a8cf1936aa97059f6948bf32`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file; leaf, no delegation

## Objective, authority and method

Attack the proposed incidence method using one nested local initializer and
its published use. An incidence names the source owner, exact occurrence and
resolved binder, actual native rows, and construction-specific transport
coordinates. The question is whether existing records lose those coordinates,
or whether the unresolved premise is the interpretation of their construction.
This is static source conformance, complementary to the constructive prover.

Authority is **Selected operation and compiler responsibility**, **Value-reference
SCC clarification**, and **Retained boundary** of
`notes/design/2026-10-10-parent-copy-scc-intrusion.md`, and §§1–5 and **Evaluation**
of `notes/design/2026-10-11-yulang-inference-top-level-principles.md`.
`rules/compiler-engineering.md`'s **Natural compiler behavior and proof-obligation
economy** and **Deterministic Simple-sub inference** govern the method.
Actual Value variables are vertices; actual references in their owned values
are edges. Comparisons, storage sides, lexical containment and parent records
alone establish no edge. Effects stay separate. Type-only rows need no invented
source value or outgoing edge merely because they are allocated.

Read dependencies include the current task's mathematical construction and
independent falsification notes, the value-owner introduction and mutual-Name
native bridge notes, and the seven compiler files listed below. The previous
uniform-renaming attack and recursive-root calculation are accepted background,
not repeated experiments. No semantic decision or representation is adopted.

## Small discriminator and explicit hypotheses

```yulang
my host z = {
  my id x = x;
  id
}
```

This is a constructor discriminator, not an executed source counterexample.
Hypotheses: successful lowering/collection of these forms; the same retained
HIR artifact and candidate session; successful finite source admissions,
installation, capture and completed local routing; and no intervening
canonical equality that changes the original identities in the displayed
calculation. The ordinary unannotated formal path is used. No authentic arrival
at a later extrusion, complete Call, principal scheme or public acceptance is
assumed or claimed.

Let `b` be the `HirLocalId` for `id`, `o` the body Name `x`, and `u` the final
Name `id`. Let `I` be the actual live Value row of the initializer Lambda's
component, and `A` the actual live formal row from its parameter recipe.
They are distinct original rows. Retained HIR gives the exact initializer,
Lambda body and parameter identity; name resolution gives `o -> parameter x`
and `u -> b`. The separate initializer boundary supplies the source owner of
`o`: the local binding `id`, not `host` merely because of containment
(`yu-hir/src/module/local_source.rs:636–657,795–830`).

The native coordinates are recoverable jointly:

1. `candidate_source.rs:187–217` assigns the Lambda/formal recipes and makes
   the body endpoint the parameter recipe, bypassing its occurrence component.
   `:441–455` retains the initializer Lambda component and body endpoint.
2. `lib.rs:11233–11260,11342–11362` consumes the same recipe and forms the
   positive Function with argument `A-` and result `A+`, then admits it to `I`.
   The two Effect ports are retained without becoming Value edges.
3. Block scheduling visits the initializer at level 2 and installs it at
   boundary 1 (`candidate_source.rs:253–326`). Formal levels are initialized
   from the same schedule (`:532–558`). `LocalScheme` stores `(b,I,1)`
   (`candidate_scheme.rs:116–120,1316–1335`).

Thus the source-reference candidate is jointly indexed as
`(owner I, Lambda initializer of b, occurrence o, resolved parameter x, target A)`.
This recovers actual Value coordinates for the original source construction.
It does not claim that `A` owns `Ref(A)`, that the bypassed Name component owns
anything, or that the Lambda's argument port creates a second source Name edge.

## Positive result: local freshening retains a joint map

At `u`, `Action::Local` retains `(slot(b),u,use component,level)`
(`candidate_source.rs:381–390`). Routing reads the installed local identity,
root and boundary together, captures that root, and prepares one fresh map
(`candidate_scheme.rs:1354–1378`).

Write `G` for that captured graph and `jI,jA` for its row indices for `I,A`.
Capture interns canonical rows once (`:300–328`) and expands the initializer
root's retained Function bound (`:570–614`). The Function capture retains
ordered children and their polarities (`:458–514`), so `A` occurs as both
the negative argument child and the positive result child of that Function.
This establishes why the target row is present in this particular capture;
it does not infer a semantic reference from a bound side.

The actual local map is

```text
M_u(G.rows[j].key) = FreshUse.rows[j]
owner candidate   = M_u(I)
body target       = M_u(A)
```

`prepare_candidate_fresh_use` canonicalizes source rows and memoizes one
destination for each canonical source (`:983–1023`). Eligible local rows get
fresh identities; older/non-generic rows are shared. In the successful
unmerged unannotated prefix above, `I,A` are level 2 with the ordinary initial
non-generic state, so both are eligible above boundary 1. The map keeps the
two polar occurrences of `A` on the same fresh row during scheme
instantiation. This is the actual local-freshening rule, not a proposed
unpolarized rule for extrusion.

Native terms are reconstructed from `G` using that same row map and each
node's retained polarity (`:1110–1161`). The final local admission uses the
fresh root and the actual use component (`:1500–1522`). On completion,
`commit_local_use` retains `LocalFreshRoute { local:b, occurrence:u, graph:G,
rows:M_u }` (`:228–236`). Although temporary reconstructed terms are released,
the Function children and row map remain. Their Value coordinates are
reconstructible; releasing `FreshUse.terms` is not a demonstrated incidence
loss for this case.

Consequently, **given a justified original owner/reference incidence and its
fresh-use preservation law**, the body occurrence `o` has exactly one joint
fresh owner/target candidate `(M_u(I),M_u(A))`, indexed by this local use `u`.
Two uses have separate retained route records. In a shared-capture variant,
the map itself records the unchanged older target. No allocation of a fake
source value to every captured row is needed. This is a positive operational
source-construction bridge; the conditional clause concerns semantic
preservation, not an absent row map.

## Exact remaining seam and record sufficiency

The discriminator does **not** refute incidence-directed construction. Its
first unresolved semantic application is the justification that the native
Lambda admission at `lib.rs:11342–11362` represents the owned initializer's
body reference to the formal, and that the particular restored instance
preserves it. HIR provides the source reference and the native constructors
provide matching coordinates. The inspected code builds typing Functions,
captures typing evidence and remaps rows; it does not itself prove that the
owned-value interpretation commutes with those operations.

The Authoritative graph clarification specifies edge meaning and directs
source constructors to determine adjacency. It supplies no specific native
Lambda-result/fresh-use preservation theorem. The registry adoption's
discussion of `ParameterOrigin` likewise states an outstanding complete
original formal introduction (`2026-10-10-original-registry-constructor-adoption-proposal.md`,
§2). Repository search found no compiler `ParameterOrigin` definition;
`FormalRegistrationInput` and `FormalNameInput` are explicitly source inputs,
not those original certificates (`candidate_call.rs:1–29`). That separate
formal/Call gap is not proof that this incidence route is impossible or that
its graph construction requires the whole original registry presentation.

| Record | What this audit can use | What it cannot establish alone |
| --- | --- | --- |
| `LambdaRecipe`, formal registration/name inputs, HIR | Exact local initializer, body Name, binder and native `I,A` | Owned-value preservation under native Lambda admission |
| `LocalScheme`, `LocalFreshRoute`, `FreshUse` | Installed root, boundary, use occurrence and joint fresh/shared Value map | Source-incidence preservation merely from typing-graph restoration |
| `DefinitionUse`, `RoutedUseProvenance` | The established module-Name route certificate from the frozen predecessor notes | Every local initializer's owner solely from its containing module definition |
| Apply source/native input | Joint source operands, checking occurrence and native four-port demand | That a demanded port is a reference owned by the Apply result or provider |
| Extrusion `Parent` | Exact created copy, parent, polarity and target level | Reference adjacency or a source-occurrence-to-port law |

For later extrusion, a supplied occurrence-to-port incidence can use the
actual operation's `(endpoint,polarity,target)` key and returned Function's
ordered children (`candidate_extrusion.rs:5,73–123,325–358`). Parent records
alone are not an operation-wide source-reference map, but retained structural
terms may still disambiguate the chosen port. This audit establishes no
information-loss counterexample to the combined records and no authentic
extrusion history for the displayed source. It does not repeat the previous
single-renaming falsifier.

## Checks, limits and next action

Static commands: bounded `cat`, `sed`, `rg`, `sha256sum`; read-only
`git rev-parse HEAD`, `git branch --show-current`, `git status --short`, and
`git diff d8c097e1f -- <exact inspected source/authority paths>`. The dependency
diff was empty. Early combined captures truncated; the decisive local routing,
capture, publication and Lambda rules were reread in bounded captures.
`git diff --no-index --check /dev/null <leased note>` found no whitespace issues.
The absent `spec/` search was reported by `rg`; no specification coverage is
inferred from that failed path lookup.

No executable oracle, checker, seeds/ranges, mutations, instrumentation,
builds or tests ran. HIR and solver evidence share the same pinned source and
successful-construction hypotheses; this is not independent semantic oracle
validation. Failure conditions include failed collection/admission, changed
canonical identities, a different formal annotation domain, or a source
reference whose target is not covered by this capture. Arbitrary Apply,
recursive local/module transport, later extrusion, replay/equality, scanner
agreement, complete Call, type equality, principality, effects and cutover
remain unverified. This producer does not certify its own artifact.

Only lightweight static read processes were used, with at most four reads
batched; no heavy/probe process or measurement sample. CPU, RSS and reasoning
wall time were not measured; the packet supplied no numeric budget. Requested
role was independent falsification/source conformance; actual model/effort
metadata is unknown. No child spawn, Git mutation or shared-record write.

Recommended next action: have the constructive lane apply one explicit
Lambda/source-incidence preservation law to this retained local route and
decide whether its fresh-use preservation follows from the native map.
Do not commission another metadata carrier before testing that existing
joint map. Keep the original parent theorem OPEN.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-11-value-incidence-independent-falsification.md`.
- Baseline SHA: `d8c097e1f810fb26a8cf1936aa97059f6948bf32`.
- Changed dependency hashes: none; inspected source/authority dependencies match the pinned baseline.
- Claim/review status: unreviewed bounded positive source-construction characterization with an explicit semantic preservation premise; no impossibility or parent closure; writes stopped before submission.
- Checks already run: static reads, baseline/branch/status, exact dependency diff, SHA-256 snapshot and note whitespace check. No tests/builds/Oracle.
- Proposed checkpoint message: `research: trace retained local Value incidence and fresh-use coordinates`.
- Shared-record deltas left for primary/curator: record existing local-use map sufficiency for the displayed joint coordinates; distinguish the unresolved Lambda/fresh-use semantic preservation law from metadata loss; preserve all parent gates OPEN.
