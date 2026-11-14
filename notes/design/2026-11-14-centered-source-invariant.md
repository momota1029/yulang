# Concrete centered source invariant and the remaining installation case

Status: the concrete invariant initializes for unknown point roots. Every
noninstall constructor and every terminal installation preserves it. A
centered `Simulation` and its `Acc` consequence are constructed conditional
on one exact constructor obligation, `NonterminalInstallPreservation`.
Unconditional Class P accessibility remains open.

This continues [the centered source handoff](2026-11-14-centered-source-continuation.md).
The starting commit is `cd86f76ab5790c28ed3ccbbe446e32a4f0499140`.
Six proof modules, one audit, and this note are new. The only changes to
existing files are appended imports and the appended design-index entry.

## Concrete coverage

`GeneralNominalCenteredSourceInvariant.Coverage` stores identity-indexed
journal labels and selected raw and centered trusted ledgers. It requires:

- A uniform labelled `Value` over the surviving original holes for every
  argument center of every registered site. The forest of source patterns
  is exactly that site's journal label, and each tree uses the finite test
  vocabulary.
- The handoff's exact `TrustedInputs` under the selected raw ledger's coarse
  model predicate, together with the selected raw ledger and readbacks.
- Labelled values for selected centered input origins: input site centers,
  head-schema origins, declared input binder centers, raw legacy input
  origins, and merge input centers.
- Labelled values for output-only binder centers actually used by the named
  schemas of selected output facts. `output_binder` also derives settlement
  of that exact packet from the trusted ledger.
- Inclusion of every selected raw fact as a centered legacy fact.

The selected centered predicate is the original source plus source sites and
the selected centered facts. `registered_site` restricts these values to
actual centered models using the reachable trusted-model theorem. It never
uses the converse implication. `trusted_inputs` exposes the exact raw field;
`promoted_output` derives raw materialized output labels using the existing
settled binder ordering and the stored raw input coverage.

The finite source menu includes **both declaration heads and materialization
requests**. A menu containing only requests would omit a constructor used
solely by a head such as `Wrap[T]`. `source_scoped`, `templates`, and
`output_test` prove the widened vocabulary directly from source syntax.
Neither source holes nor constructor keys are created from later states.

`initial_coverage` uses the existing initial journal and source-frontier
leaves. Point root arguments identify each explicit root center with its
original lower source. Both trusted ledgers start empty; registered root
coverage is nonvacuous. `initialized` supplies a valid initial inventory.

## Proved transition cases

`GeneralNominalCenteredTrustedTransport.trusted_step` preserves a selected
centered trusted ledger through every full centered step. Its coarse model
predicate is exactly unchanged. Settlement, recorded facts, and plan
membership persist; exact snapshot input readback is transported unchanged.
It does not infer such readback from readiness alone.

`GeneralNominalCenteredSourcePreservation` proves separate theorems for raw
administrative actions, centered refresh, centered merge, and installation
when the declaration has no requirements. The administrative theorem
covers enqueue, refresh, equate, and reobserve. Each case retains all labels
and uses a zero-elimination trace. Terminal installation adds no child sites.

These cases retain the selected explanations. A merge can make additional
outputs settled, and a terminal installation can record new output facts;
their selection and new source readbacks remain the responsibility of the
later nonterminal producer that uses them. The merge theorem does not claim
literal equality of different historical source patterns from semantic
aliasing alone.

## Completed pieces of nonterminal installation

`GeneralNominalCenteredChildSourceValues.recipe_readback` composes a centered
actual schema with uniform finite binder readbacks. `filled_value` keeps the
exact source template and shared substitution. `child_template` derives a
finite tree from actual candidate preparation, including request completeness.
A small additive lemma, `covered_tidy`, establishes a normal form for covered
normalized source templates, including source syntax whose normalization
removed unsupported hidden pieces.

`child_recipe` embeds the actual child argument in the centered child schema.
`child_value` and `child_site` then construct the exact emitted center values
and forest, with labels
`normalizeArgs (substArgs capture (normalizeArgs clause.arguments))`.
They require the shared binder readbacks and centered `Inputs` explicitly.
They do not require the raw optional-provenance guard, select captures from
individual models, or choose a minimum before refinement.

`GeneralNominalCenteredCoverageReplacement.replace` transports the entire
invariant, all registered forests, and historical journal through one global
replacement. It requires readback for that replacement under each field's
coarse predicate. `eliminate` constructs a one-hole trace and derives its
finite encoding budget from a supplied scoped raw-coarse replacement. Raw
readback restricts to centered readback via legacy inclusion. A replacement
known only under actual centered models is not silently used for raw inputs.

## Exact remaining constructor

The complete statement is compiled as
[`NonterminalInstallPreservation`](../../lean/Yulang/GeneralNominalCenteredSourceConstruction.lean).
For fixed `registry`, original `context`, and `root`, it quantifies over every
full centered path to `state`, every valid current inventory, every journal,
and every concrete `Coverage` for that journal. For every plan and support
with `Generated`, `Installable`, not `Committed`, actual `PacketGuard`, and
nonempty requirements, it must produce an updated inventory, finite
`HoleElimination.Trace`, installation journal, and concrete coverage afterward.
It has no compatibility-restricted transition relation or numerical bound
as an extra premise.

`next` proves the other constructor branches and invokes this obligation only
for installation with children. `simulation` constructs the existing full
centered `Simulation`, using `Nonempty Coverage` as its invariant.
`reachable` proves coverage along every full centered path under the same
single hypothesis. `accessible` applies the centered journal reduction;
`class_p_source_production` reduces the universal Class P proposition to this
one universal constructor obligation.

Still needed inside that case: select and combine the guard's trusted
explanations; produce every newly relevant finite input and output-binder
value; construct each full-report exposure over the original surviving holes
with old-leaf readback and actual K2 safety; and reconcile semantic captures
with the historical journal under the resulting global replacements.
The earlier historical-label theorem removes a separate historical
compatibility premise once this matching is available.

No semantic counterexample or undecided rejection/deferral policy was
established. This is an open source-production proof, not an owner decision.
No boundary, guard, execution rule, or fixed specification was changed.

## Verification and independent review

The `prover` role and its repository launch configuration were unavailable;
no prover agent ran. The primary constructed the bounded derivations under
the [yulang-proofs skill](../../../../.codex/skills/yulang-proofs/SKILL.md).
The independent `source_obligation_review` agent reviewed the quantified
statements and model scopes read-only and ran separate dependency audits.

Commands were run from the repository root:

| Exact command | Exit code | Result |
|---|---:|---|
| `cd lean && lake build Yulang.GeneralNominalCenteredSourceConstruction Yulang.GeneralNominalCenteredChildSourceValues Yulang.GeneralNominalCenteredCoverageReplacement` | 0 | All six new modules; 871 jobs |
| `cd lean && lake build Yulang` | 0 | Aggregate; 2393 jobs |
| `cd lean && lake env lean Audit/CenteredSourceInvariant.lean` | 0 | 57 declarations; dependencies limited to `propext`, `Classical.choice`, `Quot.sound` |
| `git diff --check` | 0 | Tracked whitespace |
| `python3 /tmp/check-centered-source-invariant.py` | 0 | Exact new files, append-only tracked changes, imports, audit coverage, unchanged HEAD, proof-token and whitespace checks |

Development elaboration attempts exited 1 before fixes to implicit arguments,
namespaces, structural recursion, and dependent list indices. Exploratory
reads of absent files exited 1 or 2. Final checks cover the final widened
source menu. No commit, push, fetch, merge, or reference update was run.
