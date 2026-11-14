# Centered source continuation and historical journal compatibility

Status: historical compatibility and the full centered termination reduction
are checked. Unconditional unknown-root Class P accessibility remains open.
This continues [source syntax and capture refinement](2026-11-14-source-syntax-refinement.md)
and the [source-producer handoff](2026-11-14-source-producer-handoff.md).

The starting commit is `975bf6eacee30c78a3a04b47f64d9b04ca5dc301`.
All ten proof modules and the separate audit are new. Existing files only gain
imports in `lean/Yulang.lean` and this note's entry in the design index.
No transition, guard, boundary, owner decision, or configuration is changed.

## Historical compatibility

`GeneralNominalIdentityJournal.IdentityLabels` makes the journal's syntax
depend on numeric invocation identity. This is stronger than depending on
the complete `Occurrence`: different endpoint demands can have the same
allocated child identity. A read-only review probe verified this distinction
using two singleton captures for a variable child argument.

The allocation proof separates repeated and fresh invocations. A repeated
parent/declaration pair reuses the historical presentation, using equality
of seeds, parent identities, and checked declarations. In the fresh case,
injectivity of the allocator and strict parent/child identity growth prove
that each new child identity is absent from all historical uses. Checked
declaration and clause identifiers resolve collisions within the same packet.
The new label function preserves identity indexing.

`new_packet_extension_preserving` preserves the root and every historical
input or clause-child use, including terminal packet uses. The centered
`GeneralNominalCenteredSiteLabels.install_journal` additionally proves that
every already registered centered site's label is unchanged. Its proof uses
actual reachable lineage, rather than equality of complete occurrences.

Consequently, `HistoricalChildLabels` is no longer a hypothesis of the new
raw or centered `NewPacket` theorem. The remaining `Matching` premise is
explicit: one canonical capture family must match the current input labels
after global replacements. It is not produced merely by numeric identity.
`IdentityLabels` initializes for unknown roots and survives every operation
in the existing capture-refinement machinery. No earlier minimum-size choice
is used.

## Full centered traces and coarse source predicates

`GeneralNominalCenteredTrace` proves source/configuration preservation,
registration of generated occurrences, packet and site lineage, exact
plan-to-packet correspondence, and interpretation of trusted facts along the
full `GeneralNominalCenteredSteps.Step` relation. `trusted_models` maps actual
centered models into the coarse centered trusted-model predicate. It does
not map coarse models back into actual models.

`GeneralNominalCenteredSourcePersistence` proves monotonicity of recorded
packets, recorded facts, finite discharge, settlement, and raw `SharedSupport.Trusted`
ledgers through every centered step. For a fixed raw ledger, its coarse model
predicate is exactly unchanged, because it depends only on the original
source and that ledger. `trusted_inputs_step` and `trusted_inputs_trace`
therefore preserve the handoff's exact `TrustedInputs`, with no replacement
by an actual-state-only predicate. Initial trusted ledgers have no facts or
readbacks, and their trusted-input assertion follows.

These are persistence and initialization results. They do not derive
coverage of newly relevant captures or assert that an arbitrary centered
ledger has a raw recipe certificate. In particular, the centered output
certificate names binders but does not itself express output-only binders
over surviving original holes. Their settled-child production remains part
of the missing source invariant.

## Constructor production over fixed surviving holes

`GeneralNominalConstructorSourceExpansion.structural` and `point_nominal`
construct the handoff's exact `ConstructorExpansion` from a current recorded
observation and represented child trees. Their `Represented` premise includes
uniform raw-model readback, canonicality, constructor vocabulary, and actual
graph backing for each child. The proofs derive the parent's readback and
actual graph edges from the observation. They never reset the hole set to
the current state's frontier. The scalar producer has no child premises.

`expansion_discharge` consumes the old leaf and actual safety to obtain a
labelled one-hole replacement and its finite `Trace`. `tested_discharge`
extracts safety from the actual tested position and explicitly separates
empty model predicates. `centered_tested_discharge` consumes the full centered
packet guard; its inhabitation field supplies a raw model and its safety
field rejects the raw backed cycle at that tested position.

The centered consumer still requires expansion and readback over the stronger
raw `Models state.erased.current` predicate. It is not a producer for arbitrary
nonpoint centered projections. Full-report source-location recovery,
represented-child production, and the general centered constructor case
remain open. Neither failure to find a tree nor absence of a certificate is
used as an execution deferral rule.

## Centered termination reduction

`GeneralNominalCenteredProgress` proves administrative accessibility without
`CompatibleStep`. Centered refresh retains raw model restriction and gains a
new known-source fact. Centered merge gains an alias fact; reachable centered
sites have raw registered occurrences with the same demands, which supplies
the finite output-source bound. Ordinary equality feedback and descriptor
reobservation use the established orders. A generic finite persistent-fact
order handles their union. Reachable states with no centered models are
accessible: the installation guard's inhabitation field rules out installs.

`GeneralNominalCenteredSnapshot` reconstructs the finite literal signature
cover from bounded historical lineage along full centered traces. The journal
supplies the bound through the existing substitution-stable syntax descent.
`GeneralNominalCenteredHolePhases` then orders the remaining holes, remaining
snapshot signatures, and administrative progress. This gives the centered
counterpart of the fixed-hole phase theorem and the accumulated elimination
bound.

`GeneralNominalCenteredJournalSimulation.Simulation` now has a universal
`next` field over the full centered Step. `accessible` and `eliminated_holes`
are proved from this structure and `Checked` plus `InitialSource`.
`class_p_accessible` exposes one named remaining assumption:

```lean
ClassPSourceProduction roles :=
  ∀ registry, Checked registry → ∀ context (root : Occurrence roles),
    InitialSource registry context root → PointSource context root →
      Nonempty (Simulation registry context root)
```

This proposition is a compiled open obligation, not a theorem. Constructing
it still requires the reachable source invariant with newly relevant-origin
coverage, its coarse trusted-input proof, full-report constructor production,
and common semantic captures yielding `Matching` after replacements. The
numerical phase reduction and historical label compatibility are now separate
checked components. Unconditional Class P Acc is not claimed.

## Verification and review

The configured `prover` role and its launch configuration were unavailable.
The primary constructed these bounded derivations directly; no prover agent
ran. The independent `source_obligation_review` agent reviewed the final
statements and model/graph scopes read-only, and reran the separate audit.
It found no hidden compatibility premise or quantifier mismatch, and confirmed
the remaining source-production premises. No semantic obstruction was found.

All commands below were run from the repository root:

| Exact command | Exit code | Result |
|---|---:|---|
| `cd lean && lake build Yulang.GeneralNominalCenteredJournalSimulation Yulang.GeneralNominalCenteredSiteLabels Yulang.GeneralNominalCenteredSourcePersistence Yulang.GeneralNominalConstructorSourceExpansion` | 0 | All ten new modules in the import closure; 866 jobs |
| `cd lean && lake build Yulang` | 0 | Aggregate; 2387 jobs |
| `cd lean && lake env lean Audit/CenteredSourceContinuation.lean` | 0 | 91 declarations; dependencies contained in `propext`, `Classical.choice`, `Quot.sound` |
| `git diff --check` | 0 | Tracked whitespace check |
| `python3 /tmp/check-centered-source-continuation.py` | 0 | Exact new-file set, byte-prefix preservation, ten imports, one index entry, unchanged HEAD, proof-token and new-file whitespace scans |

The independent reviewer ran the last command with exit 0. Development
elaboration attempts exited 1 before fixes to explicit parameters, list
membership binders, and constructor-position types; the final versions pass.
The first exploratory read of a nonexistent `GeneralNominalCenteredSources.lean`
also exited 1 and was followed by inspection of the actual modules.

The final scope check found exactly ten new proof modules, the new audit,
this note, and the two permitted append operations. All other tracked files
are unchanged. No commit, push, fetch, merge, or reference update was run.
