# Root Function extrusion: bounded bound-lineage audit

Date: 2026-10-15
Status: frozen bounded characterization and conditional source explanation;
fresh M1 compiler_referee review passed, no theorem or production conformance claim
Branch assigned by primary: `research/simple-sub-intrusion`
Pinned baseline: `402596bdbecdee9aee970e8cfdb05830960e7726`
Lease: this new note only; complementary static source/artifact method
Budget: at most 20 minutes; zero Cargo/build/probe/measurement/Git
Parent status: original H1/H2/U OPEN; H3/P disabled; omitted-formal profile
position matrix undecided

## Objective, authority and result

Determine whether the reconstructed root Function and its admission explain
the observed later `cb x` upper-bound ancestry without an Extrusion Function
TransportWitness. Governing authority is top-level inference principles
§1.1 and annotation integration §§1,3–5. Prior evidence is the exact
[pair/source census](../progress/2026-10-15-omitted-formal-copy-relation-uniqueness.md),
the bounded [Parent correspondence](2026-10-15-extrusion-parent-source-correspondence.md),
and the frozen [field observation](../progress/2026-10-15-omitted-formal-copy-field-correspondence.md).
These inputs retain their bounded claims and the original H1 quantifiers.

**The code has a root rewrite route that emits Derived evidence and no root
Extrusion Function witness.** Work::Bound and IncomingAllowance emit such
transport evidence for selected bound coordinates instead. The supplied
ancestry is consistent with that root route. It does not authenticate that
route: the first missing runtime attribution is that the Function endpoint
`term 269` captured with relation 13 is the result returned by the extrusion
of source relation 5's root demand `term 262`, rather than another bound
derived while that source task was active. This pass stops at that gap.

No runtime loss, failed inference, lost protection, or first temporal failure
at Work::Function is established. The absence of a root transport constructor
is a static fact; attributing the actual consumer to its output is a separate
unresolved fact. No language meaning, profile, production representation,
compiler change, test change, or gate promotion is proposed.

## Exact supplied runtime coordinates

The test fixture at `candidate_context_tests.rs:573–800` is unchanged:

```yulang
my root = { my outer cb = { my inner x = cb x; inner }; my identity z = z; outer identity }
```

HIR binder/parameter identities and both Apply checking occurrences are
authenticated by the frozen harness, rather than joined by spelling or row
representatives. Its all-context pair/source census joins all four retained
Parents exactly to the sole authenticated `cb x` origin, relation 5. Its
consumer selection requires an immediate Replay whose child is the actual
FunctionPort Argument parent, checks both Replay relation pairs against the
exact input BoundKeys, then traverses only Derived/Transport upper ancestry.
It reports ancestry `66 -> 13 -> 5` and zero qualifying Extrusion Function
witnesses on that ancestry. It consequently evaluated no per-copy field
candidates or exact consumer-input flags.

The primary supplied this exact saved focused-run excerpt during this audit:

```text
source Apply relation 5 pair: ValueRow(14) <: NegativeFunction(term 262)
Transport {
  child: RelationId(66), parent: RelationId(13), use_origin: 2,
  witness: Some(TransportWitness {
    from: BoundKey(Value(ValueRow(14)), Negative,
                   Value(NegativeFunction(term 269))),
    to:   BoundKey(Value(ValueRow(24)), Negative,
                   Value(NegativeFunction(term 335))),
    reason: FreshUse
  })
}
Derived { child: RelationId(13), parent: RelationId(5) }
```

Term indices abbreviate the supplied `Term { index: ... }` printout. They are
session-local identities, not expected constants or allocation-order evidence.
The excerpt does not supply relation 13's complete RelationKey, the root
extrusion return endpoint, or a rewrite queue receipt. The saved run is a
primary-supplied dependency, not a new execution by this worker. The older
consumer-frontier note's numeric row layout concerns its earlier fixture;
those numeric assignments are not imported into this receiving-call fixture.

## Constructor derivation with explicit hypotheses

Fix one successful typed drain at the pinned source bytes. Let `r` be the
active contextual relation, `V` its canonical receiving ValueRow, and `F` its
negative Function endpoint. Assume the drain reaches the inspected structural
branch with task `V <: F`, extrusion returns a changed Function `F'`, the
queued task subsequently reaches ordinary bound admission, and later capture
and fresh use operate on that admitted bound's retained relation. These are
explicit route hypotheses, not conclusions extracted from the numeric IDs.

| Stage | Exact source owner | Construction and retained coordinates |
| --- | --- | --- |
| Source Apply | `shadow_apply.rs:1463–1529` | Resolve actual callee and argument endpoints, construct a negative Function demand from argument, argument Effect, invocation Effect and result; save NativeInterface and admit the exact source checking occurrence. |
| Active task | `lib.rs:12260–12340`; `candidate_context.rs:2931–2972` | The drain sets pair processing from its current task and contextual processing from its transported relation. Context execution checks the canonical pair. Canonical requeue returns before structural extrusion (`lib.rs:12412–12420`). |
| Extrusion call | `lib.rs:12463–12516` | A ValueRow lower fails paired Function destructuring. Extrude its structural upper with Negative polarity to `value_levels[V]`. If changed, record the diagnostic edge `V <: F` to `V <: F'` with field None; enqueue the latter and return. |
| Root reconstruction | `candidate_extrusion.rs:75–255,327–364` | Root `Key(canonical(F), Negative, target)` is Visit, not Bound. Four child keys have signs Positive, Positive, Negative, Negative. Actual row copies retain Parents. Work::Function reads child outputs from local maps, constructs `F'` if changed, inserts only `(root key, F')` in the structure map; the final root lookup returns it. |
| Retained root output | `candidate_intrusion.rs:290–309` | `finish_candidate_extrusion` indexes `(processing pair, F')` in `intrusion.by_output`, pointing to a PairGroup with the invocation's occurrence and exact Parent span. It constructs no Transport dependency. This is already retained output evidence, separate from Work::Function's local per-field map. |
| Rewrite admission | `lib.rs:12884–12923`; `candidate_context.rs:2754–2776` | `enqueue_task` sets relation None. `enqueue_item` calls `candidate_context_admit` before queue insertion. It interns the queued pair with source-local context and inherited sources, and appends Derived from the retained processing relation when aligned. It constructs no TransportWitness. Call its result `q`; exact RelationKey interning can reuse an existing ID. |
| Selected root bound | `candidate_extrusion.rs:811–840,392–470`; `candidate_effect.rs:409–483`; `candidate_context.rs:3034–3079` | `candidate_apply_value` chooses owner V, Negative side, item F', then inserts and replays the bound. Origin admission uses the current processing pair. `candidate_context_bound` constructs the bound pair with inherited post-check context/sources, appends Derived to the processing parent, and attaches the complete BoundKey. This may reuse q and yield a self-Derived edge; it does not create an extrusion witness. |
| Capture | `candidate_scheme.rs:548–594,599–645` | Capture of a local row enumerates its exact negative Function uppers; `Capture::bound` follows that exact BoundKey's cursor and retains `Bound { relation, source_bound, kind, side, lower, upper, evidence }`. A missing cursor gives relation None, not an invented parent. |
| Fresh restoration | `candidate_scheme.rs:1253–1299`; `candidate_context.rs:3365–3376` | For a captured relation, reconstruct owner/item with preserved bound side and call `candidate_context_fresh_transport` with the original source_bound, mapped BoundKey and fresh.context_use. It appends Transport with reason FreshUse and attaches the new bound; restoration then admits the physical bound. |
| Consumer | `candidate_extrusion.rs:766–809`; `lib.rs:12543–12624,12701–12725`; `candidate_context.rs:2777–2835` | Replay joins exact lower/upper bound inputs. Paired Function dispatch produces Argument by Swap and records its actual comparison relation. The harness selects this Replay/FunctionPort join and follows only upper ancestry. |

Therefore, under these hypotheses, a source-root extrusion can yield

```text
r --Derived--> q --FreshUse--> u
```

when written in producer-to-child order, with no root Extrusion Function
witness. In the harness's child-to-parent order this is
`u --FreshUse--> q --Derived--> r`. This is a bounded conditional explanation
of the evidence constructors, not a theorem that `r=5, q=13, u=66` on the
observed route. Source admission and normal drain processing are shared
premises of the explanation and the existing harness.

## Why selected-bound witnesses do not repair the missing attribution

`candidate_extrusion.rs:124–177` schedules Work::Bound only while visiting a
copied row's selected pre-existing bounds; it saves the original BoundKey.
IncomingAllowance (`:178–191,293–309`) separately saves an effect allowance
bound. Work::Bound (`:310–326`) inserts the transformed bound and calls
`candidate_transfer_bound_origins(from, to, Extrusion { operation: initial,
polarity, target_level })`. The operation label records the whole invocation;
it does not certify that from/to is its returned root Function.

`candidate_effect.rs:563–609` traverses the exact from BoundKey's contextual
cursor. For each retained relation it emits a whole-bound TransportWitness
through `candidate_context_transport_witness_with_evidence`
(`candidate_context.rs:3403–3417`). Its separate origin-table loop carries an
explicit MissingOriginAssociation gap and does not manufacture an
origin-to-fiber relation. An empty contextual cursor produces zero Transport
dependencies in the first loop, even when the bound insertion has Derived
evidence. This is a source possibility, not an observed empty cursor here.

Thus neither a shared source relation nor the absence of qualifying Function
witnesses selects root reconstruction over selected-descendant admission.
The final dependency DAG records relation pairs and derivations, not a unique
activation or a reason for each Derived edge. The root rewrite, bound-origin
admission and canonical task transport all have Derived constructors in the
inspected code. A relation ID or neighboring term index does not distinguish
them. The Work::Function local child/output association remains a later
per-field correspondence question after the root output is authenticated.

## First missing transition and smallest necessary observation

The missing full activation premise is exactly:

```text
While processing source relation 5's ValueRow(14) <: NegativeFunction(262),
the root candidate_extrude invocation returned NegativeFunction(269),
dispatch enqueued ValueRow(14) <: NegativeFunction(269) with relation 13,
and its admitted BoundKey is the captured FreshUse witness.from above.
```

The smallest available retained-state discriminator comes before any new
activation observation: inspect the existing
`intrusion.by_output[(relations[5].key.pair, NegativeFunction(term 269))]`,
then its PairGroup occurrence and Parent start/end span against the four census
Parents. `finish_candidate_extrusion` creates that index from the actual final
root lookup, not a selected bound's endpoint. A matching group would establish
that this extrusion returned the exact Function endpoint in FreshUse.from.
The saved runtime evidence in this packet has not inspected that index.
The index uses a pair key, so apply the existing exact source/Parent join
rather than inferring an initiating RelationId from the index alone.

Full relation 13's key would additionally check pair/context/sources alignment;
neither its key nor the output index supplies a unique rewrite-enqueue
activation history. Claiming that exact activation would require its existing
queue/admission receipt or a separately authorized owner observation. Pair
equality, representative equality, term ordering and four Parents with source
5 cannot replace these distinctions. No observation is run and no compiler,
test or instrumentation change is proposed here.

Recommended next action: the primary should obtain the exact existing
by_output/PairGroup observation for source pair 5 and Function term 269 before
returning to per-copy Function fields.

## Dependencies, checks, omissions and commit packet

SHA-256 checked in the shared tree; production/test bytes match the pinned
inventories. The primary reported a record/test checkpoint at `c27edaa7d`
during the pass with these production/test inputs unchanged; no Git command
was used to verify or alter branch state.

```text
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5  crates/yu-solver/src/lib.rs
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461  crates/yu-solver/src/candidate_context.rs
ed3e213e943a553943784e409194723f64acb810a0bcf06607ee95b0eb4e4ed1  crates/yu-solver/src/candidate_extrusion.rs
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91  crates/yu-solver/src/candidate_effect.rs
c8ef7cc472f0dcb60d793c6f9b4f6ba1aefb76f919ff2a3ce9310f85eb647dcd  crates/yu-solver/src/candidate_scheme.rs
3db7eb04045391ceb939612226ea87e7bac6c035f3c2d4c210a8d3d4fd641831  crates/yu-solver/src/shadow_apply.rs
3a1ad7155d784c1ff0234dc7815f0d49618bff307a6564c0646cf8e510a248c4  crates/yu-solver/src/candidate_source.rs
77b145ed8a8bf2fae30a07ed74d11a29f38d18930f92e3c1c10456244fe9402e  crates/yu-solver/src/candidate_intrusion.rs
c4ffa98c7dacad210d1e0682ffec9628d2c914f78e6f4086d9062d0e912400aa  crates/yu-solver/src/candidate_context_tests.rs
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
efa7900907acd9a6c1da70fa841918e6aba3ed7977a1cece1c624259e49be8a3  notes/theory/2026-10-15-extrusion-parent-source-correspondence.md
6d932619565db4f3556c7fa29a90a3f2c8a8828d42d8758cdcca55879e884cdb  notes/progress/2026-10-15-omitted-formal-copy-relation-uniqueness.md
8dcf7aac4602baa5b29661be68df506b7a593563903cf4a7c35dedb56e923d87  notes/progress/2026-10-15-omitted-formal-copy-field-correspondence.md
```

Checks: bounded `rg`/`sed`/file reads and dependency `sha256sum`; leased-note
whitespace/locator checks only. One attempted read of nonexistent
`candidate_value.rs` failed; the actual candidate_apply_value owner was then
read in candidate_extrusion.rs. No runtime oracle, seed/range, mutation,
enumeration, new test, Cargo process, heavyweight process, measurement or Git
operation ran. The static audit and supplied harness share actual compiler
constructors; neither is an independent semantic oracle. CPU, peak RAM and
precise elapsed time were not measured; the pass stayed inside its 20-minute
allocation. No child launched and no configuration changed.

Unverified: exact root-return/rewrite activation above, per-copy field descent,
all other fixtures/entrypoints, complete lifecycle/rollback/replay coverage,
source profiles, protection/hygiene/U, dynamic Receive/Observe, full Call,
generic opening, soundness, principality and production/F5 cutover. No parent
gate closes and no source domain is narrowed. Fresh M1 compiler_referee review
found no blocking, major or minor findings. The exact `by_output`/PairGroup
observation remains unrun and primary-owned. No theorem or implementation gate
closes.

Commit packet:

- Exact leased path: `notes/theory/2026-10-15-root-function-extrusion-bound-lineage-audit.md`.
- Baseline SHA: `402596bdbecdee9aee970e8cfdb05830960e7726`.
- Changed dependency hashes: none; the runtime endpoint excerpt above was
  additionally supplied by the primary, without a separately hashed log file.
- Claim/review status: bounded static characterization and conditional route
  explanation; fresh M1 review passed; original H1/H2/U OPEN.
- Checks already run: static source/ancestry-owner tracing, dependency hashes,
  leased-note whitespace/locator checks; no executable verification.
- Proposed message: `research: audit root Function extrusion bound lineage`.
- Shared deltas left for primary/curator: link this first missing root-output
  attribution at `tasks/current.md`, `tasks/research-lab.md`,
  `tasks/effects-handler-next.md` and relevant theory/index records; preserve
  H1/H2/U OPEN, H3/P disabled and the undecided profile matrix. No shared file
  was edited.
