# Centered migration map (read-only, cycle 175)

**Version notice:** Sections 1–5 and the suggested order below describe the
`0d2ea504a4` snapshot. They are not a claim that all source producers remain
absent at the later integration head. See the f196 update at the end, which
supersedes the source-producer status while retaining the precise kernel
bridge distinctions.

Inspected checkout HEAD `0d2ea504a4` (integration merge of Astra centered production).
I-29 expressly leaves dot on I-28 until a later migration instruction. This note
is a future bridge map, not a change of kernel, boundary, or publication scope.
No centered code was changed or compiled for this review.

## 1. Exact representation and semantics

- `GeneralNominalCenters.Argument` retains `endpoints : Interval` and adds
  `center : Nat`; `Argument.Holds` means the named actual value fits those bounds.
- `GeneralNominalCenters.NominalArgument` adds `origin`; its `Holds` additionally
  requires `GeneralNominalOriginTerms.Same` with `.source center`.
- `GeneralNominalCenters.Site` pairs the same `Occurrence roles` with one center
  name per role argument. `Site.observed` gives total `.source` input origins;
  `observed_total` proves no missing input. `rootSite` chooses the endpoint for
  point bounds, a fresh source name otherwise (`point_center`,
  `nonpoint_center_fresh`). It does not turn nonpoint endpoints into point bounds.
- `GeneralNominalCenters.Plan` contains the old `Packet`, an input `Site`, and
  `input_exact`. `Plan.binder`, `Plan.emittedCenter`, `Plan.childSite` name repeated
  uses and child arguments. `repeated_emission` is literal name equality.
- `Plan.Holds = packet.Holds ∧ Plan.Equations`. `generation_guard`,
  `capture_agreement`, `input_coherence`, `no_provenance_gap` hold relative to this
  centered semantics. They are NOT the old guard over all raw packet models.
- `GeneralNominalCenteredSteps.State` contains `erased : Tracked roles` plus
  `sites`, `plans`, `sourceSites`, `sourceRecorded`.
- `GeneralNominalCenteredSteps.Models` contains raw
  `GeneralNominalSaturationState.Models state.erased.current` AND site Holds AND
  plan Equations. Forward projection to raw Models is immediate; reverse is not.
  `initialAt_models`, `initial_models`, `point_initial_models` state the exact
  initial obligations. Only the point-root case eliminates center constraints.

## 2. Actual transition correspondence is conditional, not an erasure theorem

The new `GeneralNominalCenteredSteps.At` has `administrative`, `refresh`,
`install`, `merge`; `Step` retains Generated over `state.erased.current`.
`install` erases through `GeneralNominalSharedSteps.install` and extends the center
ledger. `administrative`/`refresh` preserve that ledger; `merge` also preserves it.
`step_models` proves centered backward model preservation directly.

Existing explicit compatibility surface:
- `CompatibleStep := Step ∧ GeneralNominalActualInspectionSteps.Step` on erasures;
- `compatible_erases`, `compatible_steps_erase`;
- `administrative_compatible` (direct);
- `refresh_compatible` needs raw-model exactness beyond centered `Refresh.exact`;
- `merge_compatible` needs `rawOne`, `rawTwo`, `rawSame` beyond centered SameInputs;
- `RawPacketCompatibility` lists raw `decision`, `generation`, `input`,
  `positions`, `alternatives` obligations;
- `raw_guard`, `actual_install_lifts`, `compatible_install` consume those explicit
  obligations. They do not prove them for every centered install.

`accessible_of_erasure`, `ground_compatible_accessible`,
`compatible_terminal_of_accessible` transfer only to CompatibleStep. A terminal
state of that restricted relation is not thereby terminal for full centered
Step or full old Step. Similarly centered halted does not imply old halted:
that direction needs old enabled actions to lift, not just erasure of new ones.

## 3. Boundary and completion-consumer reuse

`GeneralNominalCenteredBoundary.vocabulary` changes State to centered State.
`fields` preserves the old survivor computation but adds center-aware root and
candidate cycles, and center DecisionGuard to InspectionPending.
`remaining.Evidence` is still
`GeneralDictionaryFeedbackEvidence.evidence roles registry state.erased.current`.
Thus target payload, recursive Evidence, occurrence, declaration and child-list
representations are reused.

Already available:
- `survivors_unchanged` (definitionally equal to I-28 empty-gap survivors);
- `local_correspondence`, `local_functional`, `local_total`, `frontierLocal`;
- `closure` (root and generated-child stability from centered halted);
- `stepModels`, `dictionaryRefl`, `initialReorders`.

Do not claim full local equivalence from no_provenance_gap alone.
`agrees_with_empty_gap` additionally requires `¬ RootCycle`, equivalence between
center `CandidateCycle` and I-28 `InspectedCycle`, `¬ I28.Blocked`, and DecisionGuard
equivalence. Those are real remaining hypotheses. Centered graph cycles add
recorded-test edges modulo semantic equality, not just an old-graph rename.

Cycle175 reusable proof structure:
`GeneralDictionaryAgreedCompletion175.dictionary_evidence` /
`dictionaries_evidence` are structural recursion over selected payloads with one
final model and all children. Their induction and `evidence_node` composition
can be ported without changing Evidence. Their current signatures are NOT
boundary-polymorphic: they consume I-28 `Classify`, stability and policy.

Required centered producer lemmas before such a port:
1. Local selected + centered stable -> a current parent Instance (either a
   recorded packet or a genuinely enabled centered Plan). Existing
   `GeneralNominalCenteredBoundary.installable_selected` is only the OTHER
   direction, Installable -> selected. The file explicitly leaves local
   selection -> guarded update as a source-compilation obligation.
2. Selected children are actual Generated children under centered stability.
   The old producer is `GeneralDictionaryAgreedEvidence174.selected_child_generated`;
   it uses I-28 `selected_available`, so cannot be applied just by renaming State.
3. A current-journal producer for the chosen centered execution fragment.

A compatibility-only route can reuse old consumers only after separately
producing old Classify/local correspondence, old halted/stability, and the old
restricted trace invariant. `compatible_steps_erase` yields full old actual
steps, NOT membership in `GeneralDictionaryAgreedFlexibleTrace175.Step`.

## 4. Finite RecordedCurrent reuse and the semantic quantifier difference

`GeneralDictionaryAgreedRefiningTrace174.RecordedCurrent` and the definitionally
identical flexible175 invariant quantify over ALL raw current-journal Models.
A centered history naturally needs only centered Models. It cannot claim that
stronger raw invariant merely because every centered model erases.

Reusable mechanisms: empty-journal `initial_recorded`, same-final-model backward
transport, ordinary install entry, and exact report transport.
`GeneralDictionaryNominalOnlyRefresh175.inspect_finished` / `instance_refinement`
are context-level and independent of either driver. They can support a centered
fixed-carrier refresh fragment directly, with Refines and nominal-only syntax;
view equality is the other available branch. `step_models` supplies the centered
backward model implication. This does not require general step erasure.

Needed: a centered current-packet invariant (or a correctly restricted raw one),
its ordinary-install producer from current centered Plan/packet semantics, and
an initial/step induction matching the chosen centered trace. Do not assume
Instance/Evidence as action guards. Existing source formation on I-28 is
`GeneralNominalActualInspectionSteps.SourceFormed`; a centered SourceFormed/plan
formation bridge is not supplied merely by `InitialSource` and compatibility.

Descriptor replacement is a separate gap: existing
`GeneralDictionaryKeyedRevision.RecordedFootprint`, `footprint_step`,
`initial_trace_current` already cover restricted UNTRACKED revision traces.
Their State is saturation State, not Tracked or centered State. Transporting that
relation and independently generating its footprint guard are still needed.

## 5. Where-DAG certificates and bounded diagnostics

Directly reusable, registry-only definitions/theorems:
- `GeneralDictionaryAgreedEdge174.RoleStratified`;
- `GeneralDictionaryAgreedComputed174.childRoles`, `computedHeight`, `check`;
- `GeneralDictionaryAgreedUniform174.roleNodes`, `certify`, `certify_iff`;
- `GeneralDictionaryAgreedTable175.heightTable`, `checkTable`, `certifyTable`,
  `heightTable_correct`, `certifyTable_eq`, `certifyTable_iff`,
  `certifyTable_reorders`.
Centers do not change declared where-role edges. Failure remains failure to
certify this restricted fragment, not rejection of the language.

The old `selected_child_role` proof extracts a Survivor, then uses
`GeneralNominalPatersonLineage.emitted_clause`. Centered survivors are unchanged,
so the same extraction proves a centered selected-child role lemma without full
boundary equivalence or step erasure. Port `child_role_decreases`,
`whereAccessible`, `boundary_whereAccessible` to centered Local after that lemma.

`GeneralDictionaryAgreedBounded174.runFuel` / `runFuel_resolves` are generic
protocol machinery; the old `certified_resolves` and cycle175
`diagnostic_resolves`, `diagnostic_exact`, `completed_iff` specialize the I-28
boundary. Their centered adapters need centered frontierLocal and the newly
ported selected-child descent. `CommonRoleOutermostResolver` tree exactness and
B4TargetV3 tree/classification conversions remain reusable. Noncomputable
frontier choice is still noncomputable; the table certificate alone does not
make candidate selection an executable evaluator.

## Suggested order after an explicit migration instruction

1. Port registry-only where-DAG diagnostics via unchanged Survivor extraction.
2. Prove a centered finite current-journal invariant for a declared fragment.
3. Prove selected-to-current-parent and selected-child-Generated producers.
4. Port recursive whole-dictionary consumer with centered Models and closure.
5. Keep compatibility/old-boundary equivalence a separately stated restricted
   theorem. Do not silently make raw compatibility a language condition.

## Integration update: f196a37fdf2f4f7d69aabc1dc07b8dd277796630

Read-only follow-up after the parent's 23:00 refetch. `f196` merges Astra
`b2a6343fd5` (source producer closure/handoff) and `b3fb016828` (comment-only fix),
as well as the completed cycle174 integration. Neither `GeneralNominalCenters`,
`GeneralNominalCenteredSteps`, `GeneralNominalCenteredBoundary`, nor the
`GeneralNominalActualAgreed*` modules changed between 0d2 and f196. Consequently
the exact centered/erased type and compatibility distinctions above remain
applicable. The source-production inventory HAS materially advanced:

### Now implemented local producers and closed conditional reductions

1. `GeneralNominalLabelledOriginClosure.Value` packages a uniform source Pattern,
   a finite readback tree and surviving-hole/source-key scope. `initial_value`
   and `frontier_value` produce original frontier values. `followed_value`
   retains a source subpattern and substitution-stable Below witness;
   `named_projection` transports an EXPLICIT constructor child to an actual
   center name using uniform Same evidence. No endpoint equality is required.
   `opaque_path` / `opaque_has_no_constructor` precisely identify why an opaque
   leaf does not already contain a constructor subtree. Do not describe these
   explicit projection producers as still absent.

2. `GeneralNominalScopedRecipeLabels.reify` / `recipe_label` produce a single
   finite scoped source label from `NodeTemplates`, canonicality, vocabulary,
   and permitted leaves. `subst_uses` and `vocabulary_bind` retain scope under
   substitution. This is independent of a model-specific choice of syntax.

3. `GeneralNominalSettledLabelledLedger.certificate_tree`, `trusted_trees`,
   `promoted_tree`, `promoted_labelled` now derive output trees/labels along the
   actual Trusted ledger. Prior binder membership comes from OutputCertificate;
   no assumed settlement-height bound or fresh output hole is introduced.
   `promoted_labelled` still explicitly consumes `Schemas`, `NodeTemplates`, and
   represented vocabulary-bounded `inputOrigins facts`.

4. `GeneralNominalLabelledExposureElimination.discharge` derives a scoped
   replacement, one-elimination Trace budget, and equality after global
   replacement from actual expanded readback, canonicality, vocabulary, graph
   Backed evidence, inhabited models and K2 safety. `alias_discharge` handles
   distinct-hole aliases. `Value.replace`, `capture_pair_equal`,
   `capture_pair_below` preserve existing representations / the indicated
   leaf-constructor agreement. Those consumers and local producers now exist;
   universal extraction of their premises from every actual Exposed event does
   not follow automatically.

5. `GeneralNominalCompatibleJournalExtension.relabel_presentation`,
   `relabel_journal`, `install_extension`, `eliminating_extension` support new
   child labels while preserving all old nonterminal input/child labels.
   Root-label and historical `Agrees` premises are explicit. Numeric allocation
   alone is not asserted to imply absence of historical label collisions.

6. `GeneralNominalJournalSimulation.Simulation` now provides a nonterminal-journal
   simulation interface. `phase_cover`, `accessible`, and `eliminated_holes` are
   closed conditional reductions consuming that Simulation; terminal packets
   need no synthetic ancestry/head-mass presentation. They concern
   `GeneralNominalActualInspectionSteps.Step`, not a centered execution kernel.

7. `GeneralNominalSourceProducerHandoff` gives compiled open-goal definitions:
   `RequestTemplates`, `RequestCanonical`, `TrustedInputs`,
   `ConstructorExpansion`, `NewPacket`. `new_packet_installs` is a proved journal
   constructor AFTER `NewPacket` is supplied. These five Prop definitions are
   not proofs that every reachable source supplies them, and are not guards.

### Still open, precisely separated

- Extract source `NodeTemplates` and canonical request tests uniformly from
  real declarations/recipes (`RequestTemplates`, `RequestCanonical`).
- Define and initialize the reachable current-inventory source invariant;
  supply `TrustedInputs` for the actual ledger and fixed original-hole map.
- Produce `ConstructorExpansion` from real exposed positions, including absent
  origin recovery, exact-report validity, represented children, Backed graph
  evidence, and inhabited/safe versus inconsistent-model branches.
- Solve arbitrary repeated-capture node/node agreement and historical child
  label compatibility after global substitutions (`NewPacket`). The new
  leaf/constructor and alias branches are not yet a solution of that full
  finite system.
- Construct the UNIVERSAL `GeneralNominalJournalSimulation.Simulation.next`
  for every reachable actual action, not only a local branch. Unconditional
  unknown-root Class P Acc remains open in the new handoff's own status.
- Align the generic positive-origin producers with centered kernel exact
  fields and prove the centered transition/boundary bridges. Astra's design
  explicitly says its derivation lacked the centered checkout and did NOT
  establish that alignment. Now both sources coexist at f196, but coexistence
  is not a proved bridge. `initial_value` represents an argument's lower
  endpoint/frontier index; it must not be silently identified with the actual
  center of a general nonpoint interval.
- The Completion selected-parent/Generated-child/current-journal producer
  obligations listed in section 3 remain unclosed by these additions: none of
  the seven modules changes the centered Local/Installable direction or proves
  centered selected -> guarded update. They supply relevant construction
  machinery rather than that final semantic bridge.

### Verification provenance

`lean/Audit/SourceProducerClosure.lean` lists 28 axiom checks and the five open-goal
#checks. The merged design reports aggregate and focused build/audit success;
this reviewer read the exact source signatures and diff only and did NOT rerun
Lean. I-29 migration permission is still absent; inbox/standing orders were
reported unchanged by the parent. No source/boundary switch was made here.
