# Import publication construction: proof-lane attempt

Sprint: `IMPORT-PUBLICATION-CONSTRUCTION-20261027/r1`.
Contract SHA-256: `f8f8e5293bbf79490e2762d53345fc87f148192b89cedc06c6e0930083c30574`.
Assignment: `/root/import_publication_proof`, revision 1.
Baseline specified by the contract: `19d12985b`.
Outcome: exact existing-rule construction attempt stopped at unavailable
authenticated provider/environment and fixed-publication witnesses. No theorem
was constructed or certified.

The actual collaboration task path above is the available runtime identity;
session UUID is unavailable. Start acknowledgement was sent before inspection.
Requested role: registered `lean_prover`; observed model `gpt-6.1-sol`, effort
UNKNOWN. The nine-slot capacity release was acknowledged as idempotent;
UNKNOWN observations and quarantined paths remain. No descendants were started.

## Authority and frozen inputs

Applied `.agents/skills/yulang-lean-proofs/SKILL.md` and its `sources.md` and
`execution.md` references. The selected authority is Source-Generalize design
§2 and companion construction §§3–5. In particular companion §3.3 supplies
Published/Family/Mono records from their actual owning rules, and §3.4 requires
an independent provider derivation before new use. The complete fixed package
and Shared dependencies remain at their original source scopes.

The original parent remains the claim at
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md:16–44`, read with
the authoritative birth-level induced-graph correction in
`2026-10-24-birth-level-scc-intrusion.md:2–6` and the unchanged inference
principles of `2026-10-11-yulang-inference-top-level-principles.md`. It covers
all supported source forms, source typing/principal coverage, soundness,
progress/termination, complete Call and Effect hygiene with shared witnesses.
The finite provider attempt does not narrow that claim.

All **17 contract pins matched** current bytes. Receipt:
`/tmp/yulang-import-publication-construction-20261027/proof/pins.json`, SHA-256
`a2db4753503df04b363e7747fff772e4223494e9c5875872279e9446435bae55`.
Twelve additional directly consulted source/toolchain paths were hashed and
recorded in `additional-pins.json` in the same scratch root, SHA-256
`484ef0f6f84c856219fbb65f5aec5b9f2c5a52357eccfca242d43af1a533b8b4`.
Those are current-byte observations, not claims of earlier baseline identity.
No Git command authenticated the baseline string.

## Attempted provider construction

Use symbolic original coordinates for the fixed provider rather than inventing
numeric Source identities. A faithful source-owner reification would have to
establish an ordinary binding with an identity Lambda initializer, conceptually

```text
binding β providerName none
  (lambda λ (formal φ x none Value) (wild ω) (name η x)) bindingsNil
```

The exact administrative pattern and each coordinate still require the actual
provider owner equation. `OriginalIdentityRealization.Identity` is not that
equation: it takes declaration, ambient scope, Context and all occurrences as
inputs (`OriginalIdentityRealization.lean:20–39`). Its registered-formal and
Name-lookup results apply to those supplied data. The accepted nested-shadow
owner table does not authenticate this other provider declaration or its
incoming module Context.

Assuming a genuine ordinary Source binding has been supplied, the existing
`YulangClosure.OriginalSource.bindingsRulesK` gives this concrete outer route
(`OriginalSourceGeneration.lean:377–403`):

```text
initializerE β
  expressionRulesK Γ initializer
    (executionE <β, returnRebind, 0>
      (sharedE <β, shared, 0>
        (rule binding [oneShotInitializer, publicationFinalRoot]
          (publishGroup [(providerName, β)] continuation))))
```

This is a readback of the existing constructor, not an independently checked
new theorem. The non-Block identity Lambda initializer uses the ordinary
sequence case of `expressionRulesK` (lines 361–373), so its source derivation
and the publication continuation are checked at the same initializer entry.

Independent provider typing is still substantive. The Lambda rule retains
description and view witnesses, capture/closure atoms, every admitted original
invocation, its receipt, value-entry Return/rebind, Shared anchor, actual body
consumer and checking proof, then resolved formal Name/fetch atoms (lines
132–168). `Judgment.rule`, `existsE`, `forallE`, `executionOpen`/`executionFixed`
and `sharedE` require those actual Kernel/local premises (lines 732–776).
Parsing the body as `x` and proving its lexical lookup cannot supply all of
them. Setting `Kernel.atom := True` would change the missing premise rather
than prove it.

## Exact publication cut and the missing stored record

Let `E0` denote the authentic incoming provider environment and let `v` be the
actual admitted outer Return/rebind value. The existing route determines

```text
E1 = E0.enterInitializer β
E2 = E1.extend <β, returnRebind, 0> v
a  = E2.anchorValue <β, shared, 0>
E3 = E2.extend <β, shared, 0> a.
```

`a` is the original globally retained anchor; it is not a fresh convenient
payload. `E1` captures the actual entry path, names and fixed frames before
the initializer. `E3` ends in this binding's actual Return frame followed by
its Shared frame. Their paths agree by `extend`'s event rule. The existing
`publication_candidate_retains_original_scope` theorem (lines 1150–1165)
then exposes the candidate from the exact entry/frame lookups:

```text
p = <E0.origin, β, returnFrame.exitPath>
record.identity     = p
record.entryPath    = E0.eventPath
record.entryNames   = E0.names
record.entryFrames  = E0.frames.filter isFixed
record.captures     = E3.names
record.fixedFrames = (E3.prefixAtShared β).filter isFixed
record.initializers = E3.initializers.dropWhile (site != β).
```

This is the candidate shape once `E0`, `v`, the original anchor and their
semantic admission/typing have been supplied. No such actual provider tuple
was supplied by the contract artifacts or source-owner lane. In particular,
the absence of a free Name in the identity body does not justify empty entry
names/frames: the Lambda retains `captureWholeEnvironment`, and the candidate
retains `environment.names` as captures.

Even successful candidate reconstruction does not establish publication.
`Environment.publicationValid` requires the additional exact equation

```text
E3.publications p = some record
```

for the candidate computed above (`OriginalSourceGeneration.lean:607–611`).
`Judgment.publishGroup` needs both this validity proof and successful
`Environment.publish` (lines 777–780). `publish` computes name-to-identity
additions and updates **only `names`** (lines 613–618); it does not construct
the fixed `publications` graph.

The Environment declaration calls that graph fixed solution data (lines
532–545). Its relevant transitions preserve it:

| Transition | Fields changed; publication map result |
| --- | --- |
| `enterInitializer` | Adds the actual initializer snapshot; map retained (547–551). |
| `extend` | Appends a frame, advances an event path when appropriate, changes replay for certain events; map retained (566–575). |
| `publish` | Prepends source names pointing to candidate identities; map retained (613–618). |
| `restore` / `atPublication` | Restores entry scope/replay from an existing record; map retained (624–641). |
| `aliasPublication` | Adds an exposure name for an already found publication identity; map retained (643–646). |

`OriginalFormalAdmission.Prior` explicitly receives the map as an independent
input; `priorEnvironment` passes it through (`OriginalFormalAdmission.lean:
349–375`). It is not a constructor that proves the map agrees with this
provider's execution. The inspected source transition cone supplies no such
realization theorem. This does not imply that a mutable insertion API is
required: a construction of the fixed solution graph, with correspondence to
the original provider derivation/history, could supply the needed witness.

A direct definition-level discriminator makes the missing premise precise.
Replacing only `E.publications` by the everywhere-`none` map leaves
`publicationCandidate` unchanged because that function does not read the map.
But `publicationValid [(name, site)]` then implies `none = some record`, hence
is impossible. This refutes the generic implication “candidate success alone
establishes validity.” It is source inspection/algebra, not a checked Lean
theorem or a Yulang semantic counterexample.

## Existing results cannot supply that witness

`YulangClosure.OriginalEffectHygiene.source_publication_constructs_replay`
(`OriginalEffectHygiene.lean:130–152`) usefully constructs successful `publish`
and replay restoration **from `publicationValid`**. Its proof immediately
extracts the stored-map equation from that argument. Reusing it here without
the genuine validity proof would assume the missing construction.

`OriginalSourceEnvironment.alias_preserves_complete_publication` (lines
1343–1362) preserves identity, entry/completed states and captures after a
successful installed-publication alias lookup. It is applicable after actual
installation and the consumer exposure correspondence are proved. It does not
identify the surface import exposure with monomorphic SRC-J `Client.alias`,
produce the provider certificate, or supply the original imported Binding.

The similarly named native map does not resolve this gap:
`NativeContextReadback.State.publications` has type
`Nat × Key → Option (PrefixPacket t)` (lines 331–343), and
`NativeContextReadback.Step.publish` inserts a checked Context prefix packet
(471–477). It is not a map from original `PublicationId Value` to complete
`PublicationRecord Value`; its owning construction supplies no equation to
the original entry/completed-frame/capture record examined here.

## Gate disposition and next exact evidence

The conditional Lean gate is **not met**. The source-owner lane also reported
that no authenticated executed provider Source/Context/fixed-publication
realization is available on the inspected fixture path. Its frozen revision 1
handoff is `import-publication-construction-20261027-source.md`, SHA-256
`4ea9245a78c01bca1bfe93c5e2dbe420b0c48d2157057387cac4f550cc474204`;
these bytes were read and independently rehashed before this freeze. It traces
the actual import-to-provider-DefId-to-candidate-Graph/FreshUse route and states
why those graph payloads are not the original publication record. Thus Lean/Lake calls
are **0/4**, time **0/240 seconds**. No `.lean` candidate, theorem types or axiom
reports are delivered. This avoids presenting another generic preservation
lemma as the missing concrete provider construction.

The earliest missing authenticated input is the actual provider Source/root
Context/environment correspondence. The precise publication subgoal after
that input is the fixed-graph equation above, derived from the independent
provider source/history construction. That construction must retain the real
initializer entry, Return/rebind, Shared anchor, captures and complete provider
typing premises. Consumer `identity`/prelude lookups then need a justified
transport of that installed publication; complete ordered module-root
elaboration remains a separate open obligation.

This result does not establish a need to change semantics or a defect in the
selected source rules. It identifies the source/solution-graph realization
owner that the next constructive work must supply. All original parent gates
remain OPEN.

Only source reads/searches and SHA-256 calculations ran. The pinned metadata
reads `leanprover/lean4:v4.35.0`, one-thread/1 GiB per Lean configuration and no
external packages; no executable version, checker success or axiom audit is
claimed. Cargo, compiler, tests, formatter and Git calls: 0. The allocation is
900 active seconds; no independent active-time/CPU/memory receipt is available.

Writes are limited to this handoff and the two scratch pin JSON files named
above. All writes stop at submission; no live shell, verifier or descendant
remains. Fresh independent review and primary adjudication are pending.
