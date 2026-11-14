# Exact G EvidenceNode counterexample search

No concrete counterexample was established. The absence of a producer proof is not a proof that the field is false.

## Existing obstructions checked

- `GeneralDictionaryJournalObstruction`: an inhabited raw journal has a unique current selection, a bad model, and no installable root packet. However the stale packet has declaration ID 41 while the fixed registry contains only ID 40; the journal is manually assembled. It is not an exact-G reachable example, and full stability is expressly not proved. An actual G install requires registry membership, so this packet cannot simply be inserted into the requested execution.
- `GeneralDictionaryRecursiveObstruction`: supplies the semantic distinction between existence of one branch witness and truth in every source model. It alone supplies neither a G-ground source/centered path nor stability. Its `context false` permits varying element types in the nominal input, so the exact GroundRoots premise also needs fresh proof rather than inference from known nominal heads.
- `GeneralDictionarySelectedAliasConflict` and `GeneralDictionaryAliasInstallationObstruction`: distinct selected keys within an alias class imply no Joint/no installation. These are conditional obstruction lemmas, not a constructed centered reachable stable modeled state. No-installation is also weaker than no Evidence.
- `GeneralDictionaryCurrentRevisionObstruction` and `GeneralDictionarySupportRevisionObstruction`: actual certified paths break literal current readback of an old packet's child list. EvidenceNode uses the current selected child list; failure of the old child list is not failure of that conclusion. The tracked path also needs an actual centered G lift and exact stability, neither supplied by these files.
- `GeneralDictionaryNonterminalOldObstruction`: an unlocated child prevents old recursive Evidence. It simultaneously prevents the All2 child-Evidence premise needed to instantiate EvidenceNode; thus this does not refute the one-node rule.
- `GeneralDictionaryRecursiveConsumerObstruction`: stability blocks a fresh child-install contract because that child is already committed. This is an operational novelty obstruction with semantic success, not Evidence failure.
- The new terminal descriptor fork has no selected generated focus at either endpoint; TerminalScope177 now proves this directly. Its unregistered observer cannot instantiate the target.

## What an actual counterexample must still provide

1. One fixed checked registry, an initial source satisfying exact G GroundRoots and point-root requirements, and a real centered transition path.
2. A concrete current centered model, not only a raw-context witness. The journal and registered center equations must all hold.
3. A root-or-generated focus with current G Local selected key/children and the full target stability premises; exclude every At constructor, not just install.
4. Actual Evidence for the current selected children (or use a genuinely terminal declaration to make this premise empty).
5. Failure of the current node Instance/Evidence at that same model and current key/child list. Failure of Joint, raw installation, historical readback, or global terminal observation agreement does not suffice.

A plausible research route is a terminal output-bearing candidate whose branch can be realized in a raw context model but conflicts with an already reachable centered journal. This is only a hypothesis: one must construct the centered path and show that the same conflict does not cause Local rejection/pending or violate GroundRoots, and must eliminate administrative/refresh/merge actions to establish stability. No such witness was found in the inspected sources. The new terminal scalar-interval fragment cannot supply this route because same-model packet truth is now proved there.

## Additional route: initial scalar input with a varying named output

Inspected the actual guard chain for a terminal declaration with a point scalar input and named output constrained to int, while the initial source admits both int and string at that existing output target.

- `RequestReady` is `RootDefined` plus `generated.unknown = false`; it is not a requirement that the named output equation already hold in every source model. Thus this premise alone need not reject the proposed fixture.
- There is no `HeldNamedOutputs` premise in the current G guard definitions inspected. `GeneralNominalValueSupport.PacketGuard` is `SupportChoices.PacketGuard` plus support groundedness. `SupportChoices.PacketGuard` comprises the ordinary `Guard` and `DecisionGuard`, which justify input roots and inspection reads. For initially observed scalar inputs, source support with the empty list is the relevant construction; `empty_supported` closes groundedness automatically. An uncommitted named output does not by itself invalidate this guard.
- The bad string model can show that the proposed packet is not committed. It does not block installation: installation asks for one common centered model of the journal and plan, not truth in all current models. In the proposed initial fixture the good int model is available, and root-only merge closure is trivial. `GeneralNominalJointCandidates.initial_joint` is the relevant constructor for Joint.
- The remaining concrete construction would be the good model's `plan.Equations`: source center agreement, head schema, empty input/child schemas, and the named-output schema, with fresh allocated output names assigned consistently. If this certificate is constructed, `.install` is an actual At step and directly contradicts Stable. The simple bad-output initial example is therefore not a plausible stable obstruction merely because its output is not yet held universally.
- Whether an output refresh is possible cannot be inferred just from the source being unknown: its certificate must preserve all source models. Int/string variability prevents simply choosing an int head by model-preserving refresh. This does not rescue stability once installation is enabled.

These are definition-level conclusions and a precise missing certificate, not a newly machine-checked counterexample or a fully formalized nonstability theorem for a new fixture. To pursue a genuine obstruction, one must arrange a reachable journal that excludes every good centered branch model (or a genuine unavoidable support failure), while retaining current Local selection and all other EvidenceNode premises. That harder construction remains open.
