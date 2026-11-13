# Source producer closure and the remaining simulation

Status: local producer theorems checked; universal `Simulation.next` remains
open. This continues
[uniform centered source production](2026-11-14-uniform-centered-source-production.md).
No Step, guard, boundary, or language rule is changed.

## 1. Centered-kernel availability and scope

This work starts at HEAD `63f03ff1d`. The supplied integration commit
`303a16872` is not in this checkout's object database. `FETCH_HEAD` is
`ca75f9324`, which predates `GeneralNominalCenters.lean`.

Both read-only attempts failed with exit 128:

- `git show FETCH_HEAD:lean/Yulang/GeneralNominalCenters.lean`
- `git show 303a16872:lean/Yulang/GeneralNominalCenters.lean`

The supervisor was asked to make the object or a readable checkout available.
No fetch, merge, checkout, commit, or ref update was performed. Consequently,
the new semantic lemmas use the generic positive actual-origin interfaces;
alignment with the centered kernel's exact fields remains unverified. The
operational reduction still concerns `GeneralNominalActualInspectionSteps.Step`.

## 2. Proved center, capture, and binder producers

`LabelledOriginClosure.Value` packages one source Pattern, one finite tree,
uniform labelled readback, and the current source-key/hole scope. All choices
are outside the model quantifier. The original hole-origin map stays fixed.

`initial_value` unconditionally represents each initial argument's lower
endpoint source identity by its original frontier index. For Class P this is
the point input identity. The theorem does not identify a general nonpoint
actual argument with its lower endpoint. `frontier_value` covers every source
identity already in that initial frontier.

`followed_value` retains a source subpattern, uniform readback, and a `Below`
witness along any finite path inside an explicit readback tree. Its source
keys come from the retained parent label. `named_projection` transports that
subtree to a supplied actual center name using uniform `Same` evidence. This
works for nominal and structural projections, and needs no equality between
interval endpoints. `Below` remains valid after every later global substitution.

There is a necessary qualification to the proposed projection argument.
If a represented parent is only `.leaf h`, it has no explicit constructor
subtree. `opaque_path` proves exactly this syntactic fact about `Follows`.
A named semantic projection can still exist, but its finite representation
requires an existing alias representation or a genuine exposure/refinement.
Center names preserve identity; they do not manufacture the missing finite
subtree. This is a source-proof obligation, not a pending rule or an infinite
execution counterexample.

The output-only binder producer now follows the **actual** `Trusted` ledger.
`SettledLabelledLedger.trusted_trees` uses the literal prior-ledger membership
in `OutputCertificate.binders`. An input-variable substitution is an actual
captured-origin leaf; an output-only substitution is an earlier finite ledger
tree. Induction therefore derives canonical finite trees over one constructor
vocabulary, without a settlement-height premise. `promoted_tree` supplies the
same tree, its uniform meaning, and its leaf containment for every requested
output of a promoted packet, even if that target is not the particular entry
added by the final `Trusted.output` constructor.

`promoted_labelled` composes that tree with fixed-hole input-origin expressions,
then reifies the result using a finite family of source-key constructor
templates. The result is one `Value` over the surviving original holes. No
reserved binder target is added as a new hole. Its precise remaining premises
are `Schemas`, `NodeTemplates`, and represented/vocabulary-bounded
`inputOrigins facts`. In particular, `PacketSettled` alone is not used to
manufacture an `OutputCertificate` or prior-binder membership.

The reifier `ScopedRecipeLabels.reify` is independent of semantic models.
Each constructor uses a retained source-key template with one distinct leaf
per position; it fills that template with the recursively chosen child labels
using one substitution. `subst_uses` proves the surviving-hole scope. This
avoids a model-dependent choice of source syntax. The reifier may choose a
different supported source key from an older equivalent input presentation;
it proves validity and finite key scope, not automatic compatibility with a
historical packet's exact labels. Source extraction of `NodeTemplates` is
still open.

The ledger proof uses the certificate's `uses` evidence through
`certificate_coherent`; it does not silently identify the raw packet report
with the inherited report.

## 3. General exposure and compatible packet extension

`LabelledExposureElimination.discharge` now handles any explicit constructor
tree once its **actual** expanded readback, canonicality, constructor vocabulary,
and graph backing have been produced. From the old hole readback, an inhabited
model set, and actual-position K2 safety, it derives:

1. absence of that hole in the expanded tree;
2. a source-labelled replacement over the remaining holes;
3. the finite inventory-code depth and a one-elimination Trace;
4. exact equality of the old leaf presentation and the expanded tree after
   applying the same replacement globally.

No source label or numeric growth estimate is assumed for the expanded tree.
`alias_discharge` handles equality of two distinct surviving holes.
`Value.replace` preserves every existing representation's readback and syntax
scope under the global replacement. `capture_pair_equal` and
`capture_pair_below` provide exact, substitution-stable agreement for the
stated leaf/constructor pair. They do not solve an arbitrary finite system of
repeated-capture equations.

These are general elimination consumers, not a proof that every full-report
`Exposed` event supplies their premises. The remaining extraction includes
absent-origin recovery, exact-report validity, represented children, graph
backing, and the appropriate inhabited/safe branch. A missing proof of any
of these facts is never treated as pending.

New child occurrences also need a label-extension operation. Holding the
entire function `Occurrence → List Pattern` fixed would require labels for
future children in advance. `CompatibleJournalExtension.relabel_journal`
instead preserves the root label and every input/child label already used by
an old nonterminal packet. `install_extension` then attaches a new packet
presentation. `eliminating_extension` composes this with a genuine global
replacement and derives the Trace budget from the replacement's syntax.
The agreement premises are explicit: allocation of a numeric identity does
not by itself prove absence of collisions with historical occurrences.

`JournalSimulation` uses the already established nonterminal journal directly.
Its `phase_cover` and `accessible` theorems are closed conditional reductions.
Terminal packets create no ancestry descent edge, so this route needs no
terminal packet head-mass presentation. No equivalence or strictness theorem
between this interface and the older all-packets `HolePhaseSimulation.Simulation`
is asserted. The source `invariant` and its universal `next` construction are
still missing in both routes.

## 4. Exact handoff spec

The following open-goal types are compiled definitions in
`GeneralNominalSourceProducerHandoff.lean`, and are checked in the new audit.
They are **not proofs** and are not execution guards. Namespace abbreviations
below follow that module's `open` declarations.

First prove the pure source-syntax extraction lemmas:

```lean
request_templates (context : GeneralNominalCandidates.Context)
    (requests : List Request) : RequestTemplates context requests

request_canonical (context : GeneralNominalCandidates.Context)
    (requests : List Request) : RequestCanonical context requests
```

Their conclusions expand exactly to:

```lean
NodeTemplates context
  (GeneralNominalSourceLabelVocabulary.collectArgs
    (requests.map fun request => normalize request.pattern))
  ((generated context.state context.interpretation requests).tests.map Prod.snd)

∀ entry ∈ (generated context.state context.interpretation requests).tests,
  TestCanonical entry.2
```

`NodeTemplates` itself is:

```lean
∀ test ∈ tests, TestCanonical test → ∃ pattern,
  Label context pattern (.node test (fun position => .leaf position.val)) ∧
  Scoped keys pattern ∧ Uses (fun name => name < arity test) pattern
```

Use `SchemaVocabulary.generated_vocabulary`, `packet_vocabulary`, and
`SchemaBudget.request_menu` to connect these source templates to the finite
registry/source vocabulary. Raw associated RHS patterns need not themselves
be covered; reification must handle the supported variable branch selected
by an actual Recipe. Do not add a covered-RHS assumption to Checked registries.

Next construct the reachable source invariant over the **particular current**
inventory. Its trusted-input projection must have this exact type:

```lean
TrustedInputs (state : Tracked roles) (facts : List (Fact roles))
  (context : GeneralNominalCandidates.Context) (origins : Nat → Origin)
  (remaining keys : List Nat) (tests : List Test) : Prop :=
  ∀ root ∈ inputOrigins facts,
    ∃ value : Value (GeneralNominalSharedSupport.Models state facts)
      context origins remaining keys root,
      Vocabulary tests value.term
```

This is to be derived for the trusted facts and surviving holes supplied by
the invariant, not for arbitrary `facts` or arbitrary `remaining`. Keep the
coarse trusted model predicate here; an actual-state-only readback does not
automatically justify a settled head explanation. With this fact and `Schemas`,
`promoted_labelled` already discharges labelled output/binder production.

At each relevant full-report constructor exposure, produce the following
data after recovering its actual source identity:

```lean
ConstructorExpansion (state : State roles) (identities : Nat → Nat)
    (inventory : Inventory) (tests : List Test) (actual : Nat) : Prop :=
  ∃ test children,
    Readback (GeneralNominalSaturationState.Models state)
      (fun name => .source (identities name)) inventory.holes
      (.source actual) (.node test children) ∧
    Canonical (.node test children) ∧
    Vocabulary tests (.node test children) ∧
    GeneralNominalBackedHoleElimination.Backed state identities actual
      (.node test children)
```

The same event must provide the old leaf readback and actual K2 safety used
by `LabelledExposureElimination.discharge`; its signature in that module is
the exact consumer. Establish the actual graph edges separately from semantic
readback. Handle unsatisfiable model predicates explicitly rather than using
the inhabited-case theorem without its premise.

After all necessary replacements, solve the new-packet compatibility goal:

```lean
NewPacket (journal : Journal context root before inventory)
    (packet : Packet roles) : Prop :=
  ∃ labels : Occurrence roles → List Pattern,
    labels root = journal.labels root ∧
    (∀ prior ∈ before.current.packets,
      prior.declaration.requirements ≠ [] → Agrees journal.labels labels prior) ∧
    (packet.declaration.requirements ≠ [] →
      Nonempty (Presentation context labels packet))
```

The open mathematical part is common canonical capture agreement under
global replacements, plus consistent new child labels when an occurrence
already has historical uses. The leaf/constructor and distinct-hole branches
are now available; arbitrary node/node equations and their real report
provenance still need assembly. Do not substitute a pre-refinement
minimum-mass choice for this property. `new_packet_installs` handles the
journal construction once this goal is proved; it does not prove installability.

Finally fill this exact `JournalSimulation.Simulation.next` field, with the
source invariant above defined and initialized from Checked + InitialSource +
PointSource:

```lean
∀ state, B4Target.Steps (Step registry root) (initial context root) state →
  ∀ inventory, Valid (GeneralNominalSourceLabelVocabulary.tests keys) inventory →
  ∀ journal : Journal context root state inventory,
    invariant state inventory journal →
  ∀ after, Step registry root state after →
    ∃ updated growth count,
      Trace (GeneralNominalSourceLabelVocabulary.tests keys)
        growth inventory updated count ∧
      ∃ journal : Journal context root after updated,
        invariant after updated journal
```

The transition proof must cover administrative steps, aliases, reobservation,
and installation, retaining newly relevant-origin coverage as well as the
journal. A local branch constructor is not a proof of this universal field.
Once it is constructed, `JournalSimulation.accessible` and
`eliminated_holes` provide Acc and the initial-hole-count bound. There is no
remaining numerical ancestry hypothesis in that reduction.

## 5. Guard dependence and verification

The center/projection, source-template, trusted-ledger, replacement, and
compatible-extension theorems use positive origin/model/graph facts. None
uses failure of a provenance certificate to infer pending. The conditional
operational reduction uses the existing actual-inspection Step. Transfer to
the unavailable centered kernel is not proved.

No new infinite trace or semantic contradiction was found. Unconditional
unknown-root Class P Acc and the universal source simulation remain open.
The configured prover role/launch configuration is unavailable, so the
primary performed this bounded derivation; no prover agent ran. The separate
`settled_review` worker reviewed the modules read-only and confirmed the
explicit remaining hypotheses and the lower-endpoint scope of `initial_value`.

Final commands, dependency audit, and append-only checks are recorded below
after verification. Seven new modules and one separate audit are added; no
previous proof-module lines, frozen files, specs, plan notes, or configuration
are changed.

| Exact command from the repository root | Exit code | Result |
|---|---:|---|
| `cd lean && lake build Yulang.GeneralNominalSourceProducerHandoff` | 0 | All seven new modules in the import closure; 817 jobs |
| `cd lean && lake build Yulang` | 0 | Aggregate build; 2329 jobs |
| `cd lean && lake env lean Audit/SourceProducerClosure.lean` | 0 | 28 dependency results and five open-goal type checks |
| `git diff --check` | 0 | No tracked whitespace errors |

All audited dependencies are contained in `propext`, `Classical.choice`, and
`Quot.sound`; `opaque_has_no_constructor` has none. The independent reviewer
reran the same audit command with exit 0 and checked the final handoff scope.
Development elaboration attempts exited 1 before fixes to implicit parameter
types and dependent recursion; the final commands above use the completed
versions.

The final scope check passed: byte-prefix preservation of `Yulang.lean` and
the design index, exactly the intended new files, seven imports, clean proof
token/whitespace scans, unchanged HEAD `63f03ff1d`, and unchanged FETCH_HEAD
`ca75f9324`. The unavailable integration-object reads are recorded in §1;
they were not replaced by a forbidden fetch/merge operation.
