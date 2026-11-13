# Source syntax extraction and finite capture refinement

Status: partial proof progress. The two unrestricted syntax extraction goals
are closed. Finite simultaneous capture reconciliation is closed under its
explicit representation premises. Unconditional unknown-root Class P
accessibility and the universal source simulation remain open.

This continues the [source producer handoff](2026-11-14-source-producer-handoff.md)
at worktree HEAD `f196a37fdf2f4f7d69aabc1dc07b8dd277796630`. No transition,
diagnostic, language rule, or centered-boundary definition is changed.

## 1. Exact source extraction

[GeneralNominalRequestTemplates.lean](../../lean/Yulang/GeneralNominalRequestTemplates.lean)
proves the exact handoff proposition:

```lean
request_templates (context : GeneralNominalCandidates.Context)
    (requests : List Request) : RequestTemplates context requests
```

Each emitted constructor test is traced to a source subpattern. Records use
the actual retained empty-record primitive key and the retained field keys;
the template has one distinct variable at each constructor position. Neither
covered request syntax nor covered associated RHS syntax is assumed.

[GeneralNominalRequestCanonical.lean](../../lean/Yulang/GeneralNominalRequestCanonical.lean)
proves the other exact handoff proposition:

```lean
request_canonical (context : GeneralNominalCandidates.Context)
    (requests : List Request) : RequestCanonical context requests
```

The auxiliary `Tidy` predicate permits joins and partially supported syntax.
Normalization establishes enough record-field uniqueness for every test
that translation actually emits. It does not assert that every normalized
source pattern is covered or has a successful recipe.

[GeneralNominalRegistrySourceTemplates.lean](../../lean/Yulang/GeneralNominalRegistrySourceTemplates.lean)
uses `SchemaVocabulary.generated_vocabulary`, `packet_vocabulary`, and
`SchemaBudget.request_menu` to obtain finite registry source keys, constructor
templates, and canonical packet schema tests. These theorems impose no new
restriction on a Checked registry.

## 2. Coarse trusted models and actual trace metadata

[GeneralNominalCommonTrustedLedger.lean](../../lean/Yulang/GeneralNominalCommonTrustedLedger.lean)
proves `trusted_append`: two trusted derivations can be replayed into one
trusted ledger. Output certificates retain their exact substitutions and
literal earlier-binder membership. Every model of the larger ledger is a
model of either earlier coarse ledger.

`common_ledger` constructs a finite trusted ledger containing every fact that
occurs in any trusted ledger at the current state. It covers facts, not every
possible alternative readback tree. It does not establish `TrustedInputs`.
`inputs_append` and `inputs_replace` preserve existing `TrustedInputs`; the
replacement must hold under the same coarse model predicate. A replacement
valid only in actual current models cannot be passed to this theorem.

[GeneralNominalReachableSchemas.lean](../../lean/Yulang/GeneralNominalReachableSchemas.lean)
proves that actual reachable models satisfy all recorded facts, and therefore
every trusted ledger. A reachable actual model also witnesses inhabitation
of every such coarse trusted model predicate. Reachable output facts retain
their registry membership and the initial constructor interpretation.

Consequently, `trusted_schemas` derives the schema premise of the existing
labelled output producer from the real trace and trusted derivation.
`reachable_promoted_output` now has just the exact handoff `TrustedInputs`
premise for its remaining source-coverage input. It does not derive that
premise from packet settlement.

## 3. Simultaneous capture reconciliation

[GeneralNominalCaptureComparison.lean](../../lean/Yulang/GeneralNominalCaptureComparison.lean)
proves a uniform comparison for canonical, vocabulary-bounded finite trees
over the surviving holes. The trees must denote equivalent values under one
fixed inhabited model predicate. The conclusion is either:

- a common canonical tree `Below` both presentations, with the same meaning;
- a surviving hole equal to a canonical tree that omits that hole.

The node/node case uses canonical head inversion, compares all child
positions, and combines their common trees with `Below.node`. Here `Below`
includes componentwise constructor comparison; it is not merely literal
subtree membership. If a leaf occurs in the other tree, that leaf is already
a suitable common lower presentation. This branch does not turn an opaque
recursive value into a finite closed type. If the leaf is absent, the
comparison yields a genuine global replacement.

[GeneralNominalCaptureRefinement.lean](../../lean/Yulang/GeneralNominalCaptureRefinement.lean)
reifies each replacement with the source templates and repeats comparison
by induction on the surviving-hole count. `reconcile` handles a finite list
of equivalent captures. It produces a `Refinement`, not a mass-minimal choice
made before refinement.

A refinement records the source pattern, its labelled readback, vocabulary,
and finite syntax-code depth. Positive bookkeeping increments, one larger
than the extracted code-depth bound, permit all operations to use one
`HoleElimination.Trace` growth function. This also handles aliases, whose
minimal replacement depth can be zero. `Refinement.count` proves:

```lean
operations.length + after.holes.length = before.holes.length
```

Every operation is applied globally, in the same order, to the journal and
all represented-origin readbacks.

[GeneralNominalCaptureFamilies.lean](../../lean/Yulang/GeneralNominalCaptureFamilies.lean)
extends this construction to any finite family of capture groups.
`reconcile_groups` preserves earlier common presentations while reconciling
later groups. `reconcile_journal` returns the refinement, a valid inventory,
the total elimination bound, a Trace, and a journal with exactly the globally
substituted labels. `trusted_inputs` transports the exact handoff predicate
through the whole refinement when its model predicate is the coarse trusted
one. These generic theorems do not inspect a Step or require interval endpoints
to coincide. Their capture representations and uniform semantic agreements
still have to be extracted from actual reports.

## 4. Concrete child-label extension

[GeneralNominalPacketChildLabels.lean](../../lean/Yulang/GeneralNominalPacketChildLabels.lean)
proves that equal allocated child occurrences within one packet come from
the same clause. The proof uses allocator injectivity and the declaration's
checked clause-ID uniqueness.

`extend` constructs the new label function directly from the capture
substitution and clause arguments. It preserves the root, the new packet's
input, and every input/child occurrence used by an older nonterminal packet.
The one remaining source-syntax compatibility premise is explicitly named
`HistoricalChildLabels`: if a new child already has one of those historical
uses, its old label must equal the new substituted clause label.

`new_packet` proves the exact handoff `NewPacket` conclusion from labelled
captures, simultaneous head matching, and `HistoricalChildLabels`. No new
label function or packet presentation is supplied as a premise. Terminal
packets satisfy `NewPacket` without matching premises (`terminal_packet`).
The general reachable `HistoricalChildLabels` premise is still open.
Semantic equivalence, allocator uniqueness, and choosing a canonical source
key do not by themselves imply equality with a historical source label.

## 5. Initialization and inconsistent states

[GeneralNominalSourceInitialization.lean](../../lean/Yulang/GeneralNominalSourceInitialization.lean)
constructs a valid initial inventory and journal with exactly the original
frontier hole range. Each root label is the indexed source leaf for its lower
endpoint; this is the point input under Class P's PointSource premise. No
closed-term premise is used.

`initial_trusted_inputs` is the empty-ledger case only. It is vacuous and is
not a proof of a reachable source invariant.

`inconsistent_accessible` proves accessibility for any actual SourceFormed
state whose current model predicate is empty. Installability requires a
current-model witness, so installation is impossible; every remaining step
belongs to the existing well-founded passive relation. Step model restriction
preserves emptiness. `reachable_inconsistent_accessible` supplies SourceFormed
from an actual source trace. The inhabited comparison theorems are never
applied to an empty predicate.

## 6. Remaining source-production obligation

The first unresolved link in handoff order is the reachable source invariant
and its coarse `TrustedInputs` projection. The new results isolate that exact
named premise in the promoted-output producer. The invariant must still
retain source meanings and historical labels for newly relevant origins,
including absent-origin recovery and newly exposed constructor children.

In particular, this work does not prove any of the following from
Checked + InitialSource + PointSource:

1. `TrustedInputs` at every relevant reachable inventory and trusted ledger.
2. `ConstructorExpansion` at every relevant full-report exposure, together
   with old-leaf readback and the actual K2 graph backing/safety.
3. Simultaneous head matching and `HistoricalChildLabels` for every new
   nonterminal packet after refinement.
4. The universal `JournalSimulation.Simulation.next` field.

Thus `JournalSimulation.accessible` cannot yet be instantiated for all
unknown-root Class P sources. No infinite trace, contradictory owner rule,
or genuine semantic gap was found. Missing representation evidence is never
used to derive pending, rejection, or a new transition guard.

The source-syntax, ledger, capture, and label-extension results are generic
enough to reuse with explicit centers. The actual reachability and inconsistent
state theorems use the existing actual-inspection Step. No unrestricted
centered-Step transfer is claimed; the concurrent centered-boundary task was
left untouched.

## 7. Verification and scope

The configured prover role and its referenced launch files were unavailable.
The primary constructed these bounded derivations directly; no prover agent
ran. A separate read-only reviewer checked the source extraction, coarse
ledger, capture comparison/refinement, initial inconsistent branch, trace
schema proofs, and the final family/label-extension modules. The review found
no blocking issue and confirmed that the note leaves the universal source
obligations open. The reviewer independently reran
`cd lean && lake env lean Audit/SourceSyntaxRefinement.lean` with exit 0;
all 40 dependency reports stayed within the allowed three dependencies.

All ten modules are appended as imports in `lean/Yulang.lean`. The separate
`lean/Audit/SourceSyntaxRefinement.lean` checks the two exact handoff types and
40 dependency closures. Every reported dependency is in `propext`,
`Classical.choice`, and `Quot.sound`.

| Exact command from the repository root | Exit code | Result |
|---|---:|---|
| `cd lean && lake build Yulang.GeneralNominalPacketChildLabels` | 0 | All ten new modules in the import closure; 828 jobs |
| `cd lean && lake build Yulang` | 0 | Aggregate build; 2377 jobs |
| `cd lean && lake env lean Audit/SourceSyntaxRefinement.lean` | 0 | Two exact handoff type checks and 40 dependency results |
| `git diff --check` | 0 | No tracked whitespace errors |
| `python3 /tmp/check-source-syntax-refinement.py` | 0 | Exact file scope, byte-prefix preservation, imports, token/whitespace scan, unchanged HEAD |

Development elaboration attempts returned exit 1 before local fixes; the
commands above use the completed versions. Existing tracked-file edits are
exactly ten appended imports and one appended design-index entry. Ten proof
modules, one separate audit, and this note are the only new repository files.
No frozen file or git ref was changed.
