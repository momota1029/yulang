# NATIVE-FRESH-BOUND-ATTACHMENT/r1 proof handoff

Producer `/root/native_fresh_bound_attachment_proof_r1`; requested Sol/high,
observed model/effort UNKNOWN; session
`NATIVE-FRESH-BOUND-ATTACHMENT-20261028/r1`; unchanged grant 900 seconds.
Base contract SHA-256
`fd040b8a5a1702b54c06c44fa88a8316433dc950a62d453de48db3f73e2e6e2c`.
Amendment 01 SHA-256
`51f0867e885940a163a5f9c31bd751593911830da9edfefb54788c321f17f0d1`.
Both ACKs were sent before the corresponding resumption.

**Outcome: INCOMPLETE provisional construction, NOT_CHECKED. R1 acceptance is
ineligible. No successful reachable counterexample or universal preparation
image attachment theorem is delivered.** No kernel acceptance, printed type,
axiom audit, independent approval, source correspondence or production
authority is asserted.

## Material deviation and pause

The original contract's README hash omitted one `0` and had only 63 hex digits.
I read the README body in an early startup `cat` and later lines 350–450 after
the initial ACK but before discovering that malformed pin with `sha256sum`.
I initially told the primary I would avoid relying on README content, then
explicitly corrected the proposed receipt that it had never been read. No
construction relied on the README, and no artifact existed at that point.
I paused all further reads/construction/writes when directed. The primary's
versioned amendment corrected only the README pin, preserved the non-waivable
deviation, and made the fixed outcome ineligible for acceptance. I ACKed base
and amendment before reading the amendment and resuming provisional work.
This is failure evidence, not retroactive authorization of the earlier read.

## Original source and unchanged parent

Actual source read: `2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5,
with the actual immutable Value-birth/induced-SCC correction in design and
theory `2026-10-24-birth-level-scc-intrusion.md` §§2–6. The manuscript locates
the original paper at `/home/momota1029/rust/simple-sub-reference-paper.pdf`,
§§3.5.1–3.5.2,5.3. That PDF body is outside the admitted inputs and was not read;
no new claim is attributed to it. The source manuscripts are research proof
material, not independent semantic authority. The authoritative top-level
inference principles and selected annotation policy were read directly.

`YulangClosure.SourceProblem.InferenceSoundness` remains exactly:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

The one shared `e`, all lawful original histories, retained extrusion
occurrences, original lexical/type/event scopes, optional records, method
selection, complete Call, recursive sharing, generalization and effects are
unchanged. No SourceProblem instance is constructed. Birth SCC qualification
does not supply lawful joint publication/use transport. Contravariant concrete
annotation supplies local subtraction permission; covariant annotation allows
the concrete effect; actual inflow, variable connections, residual and handler
subtraction remain separate. `OriginalEffectHygiene.lean` was inspected only
at its constructor/consumer seam; its independent interpretation premises
remain open.

## Artifact and exact local contribution

Changed only:

- `notes/theory/lean/YulangClosure/NativeFreshBoundAttachmentR1.lean`
- this handoff.

Lean SHA-256:
`9327161449d8f286b15af23394033b35615b8530363587ca79d22f5d1a40be9f`.
No scratch, root import, cache, generated output or other write was created.
Imports are `Std` and `YulangClosure.Contracts`.

Namespace `YulangClosure.NativeFreshBoundAttachmentR1` contains eleven authored
theorem terms, all **NOT_CHECKED**:

| Name | Intended local type/contribution |
|---|---|
| `findKey_sound` | `findKey rows key = some index → rowAt rows index = some key` |
| `rowAt_append_length` | appended key is read at old length |
| `rowAt_append_old` | successful old row reads survive append |
| `intern_raw` | successful explicit reuse/append returns a row storing the entire supplied key |
| `intern_preserves` | explicit reuse/append preserves old successful row reads |
| `discharge_raw` | discharge/residual field writes preserve raw relation rows |
| `published_child_selected` | computed admission list plus same-bound registrations selects the mapped child in the local mask subrelation |
| `published_raw` | mapped child's raw row is the complete supplied RelationKey |
| `published_context_observed` | its Context occurs in the local relation-root observation predicate |
| `beginFresh_current_image` | successful effective-root/map reads derive the exact later root, image, raw row and local selection/observation |
| `prepared_observed_or_temporal_change` | successful prep/later reads yield local observation of the prep image OR a changed effective-root key |

These are authored type descriptions. **Actual printed theorem types and every
`#print axioms` result: NOT_CHECKED.** No empty axiom list is inferred from text.
Source search found no proof hole, project axiom or checker bypass; occurrences
of `admitted` are ordinary variable names. This is not a dependency axiom audit.

`rowAt` and `findKey` operate on the actual full key values and derive reuse
soundness from list search rather than assuming table lookup coherence. The
finite-list interner is an abstract successful-action projection of the native
HashMap/vector interner; native table coherence and successful-driver simulation
are still unproved. In particular this does not establish every native history
by replacing it with list histories.

Capture carries route and bound occurrence index separately from antecedent,
use origin, source bound, parent and prepared root. The occurrence index is
ghost association, not a claimed native immutable certificate. Publish records
each capture as a list entry, preserving duplicate occurrences in the model.
No set-of-root/count equality is used as per-bound ownership evidence.

## Native mapping and represented/omitted branches

Inspected frozen R5 scheme, not the concurrently edited R1 Rust output:

- Scheme `:4628–4633`: preparation captures each bound parent's effective root;
  `:4662–4693` prepares weights and calls initially empty-map renaming;
  `:4916–4962`: admission rereads effective parent root, looks up that key's
  image, constructs FreshUse transport, imports antecedent and begins restoration.
- Context `:3062–3098`: full `RelationKey = pair/context/sources/scoped` reuse
  or append. Use origin is absent from this key; it remains in Transport.
  `:4278–4294` stores mapped raw Context and attaches child to destination bound.
- Effect `:711–738`: **scoped and unscoped admission differ**. Scoped FreshUse
  reuses/authenticates the mapped relation. Unscoped admission invokes the
  ordinary bound constructor and can record another relation. Publish permits
  separate mapped/admitted IDs registered on the same bound. The native
  ordinary constructor's entire successful execution is not formalized.
- Context `:1167–1248`: completed observer's computed admission roots select
  raw `relation.key.context`; same-bound registration and Transport incidence
  enlarge the mask. `Selected` represents only admission, same-bound and
  bidirectional Transport additions. Replay and view additions are omitted;
  interpreting the actual terminating mask loop is still open. No arbitrary
  selected-root set or seed-membership assumption is supplied to the local
  selection theorem. Its admission-list seed construction is explicit.
- Context `:1090–1094`: physical contexts start at ID 1. Logical identity is
  represented separately by `Observed`'s zero alternative, never physical row 0.
- Context `:3297–3303,3799–3887`: effective roots read discharge residuals;
  discharge updates do not alter stored raw keys. The zero-residual branch
  deliberately preserves any old residual, matching the native write footprint;
  no absent-residual invariant is silently supplied.
- Context `:3992–4075` and extrusion `:965–1065`: Replay uses retained raw lower
  and upper Contexts, full-key interning and live canonical owners. Those actual
  Replay/restoration transitions, discharge effects, source completion and
  physical emissions are **not** constructed by this file.

All PrefixLeft, SuffixRightPops, Swap, BothFromRight, Replay and
WithoutLeftFilter renaming branches were read in `rename_contexts_impl`; they
are not formalized here. FreshUse's empty certificate map cannot reconstruct
BothFromRight. Child/weight closure, mutation rejection, authentic identity,
empty, pause, shared DAG and discharged-parent specimens belong to the Rust
lane; this leaf establishes none of those runtime receipts.

## Apply to parent and exact first remaining goal

The result applies only to the local source-to-native attachment seam: a
successful later lookup publishes that later image into the full raw key even
under interner reuse. If the original prepared image is missing in the local
observation, the later effective-root key differs. This removes full-key
identity confusion as a local reason for losing an **already published** raw
image, and preserves the distinction between scoped and unscoped admission.
It does not supply any original source witness or parent premise instance.

**First remaining native goal, owner Luna's native/proof integration:** for
each captured bound occurrence and every successful earlier restoration prefix,
interpret actual native Replay/full-key alias and discharge/residual writes.
When its parent effective root changes before `begin_candidate_fresh_bound`
rereads it, prove that this same occurrence's preparation-time image and its
mapped children/weights remain in the authentic completed module/local
borrowed readback, or exhibit the shortest successful reachable omitted-image
trace. That trace must include actual capture, alias key, every successful
operation, physical admission, completion and first missing image. None is
delivered here. Do not add root stability, map-image equality, seed inclusion
or all-image observation as a premise to call this goal proved.

Earlier in the correspondence chain, native HashMap/vector coherence, all
successful constructor guards, full driver interpretation, per-bound physical
emission association and loop/readback simulation also remain open. The local
`publish` constructor is not proof that an arbitrary native execution has its
shape. All inference soundness, original A/B, effect hygiene, principality,
termination, executor and production gates remain OPEN.

## Inputs, commands and resource receipt

Contract baseline `f83a5f84be91f6da6213c12193121c56b2ccafcf`; research base
`bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d` (contract identities, no Git lookup).
Actual `sha256sum` matched the admitted Rust inputs: frozen R5 scheme
`7fd3e16f2a6f856b925e2675d8a485fc25b90775a4b5a81f39d027c71874ef4a`,
context `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`,
effect `1715046b29b760fe70b3c2fb05665dad23e7f95ad05883c39d06d4da37b925ab`,
extrusion `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`,
source `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`,
term `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`,
lib `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`,
shadow apply `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`.
Workspace manifests/lock and solver manifest matched their contract pins.
Contracts, NativeFreshScopeTransport and NativeScopeTransformer matched their
contract pins. The seven authority/correction/progress pins were authenticated
and matched. README is admitted only at the corrected Amendment 01 pin.

Read pin: Lean 4.35.0, no external packages, `-j1 -M1024`. Toolchain/config
hashes match the contract. Actual Lean/Lake executable versions: NOT_RUN.
Actual commands were read-only `pwd`, `cat`, `sed`, `rg`, `sha256sum`, `wc`,
nonexistence checks, clock reads and `apply_patch` on the exact two leases.
Observed shell exits 0; one broad `rg --files` search produced excessive
truncated output, then searches were narrowed. No checker, Lean/Lake, build,
tests, Cargo, formatter, install, network, Git or descendants were run.
No checker/diagnostic attempt was consumed. The fixed outcome is ineligible,
so this handoff requests no execution checks under R1.

Grant 900 seconds; observed clocks included 07:50:36, 07:53:52 and 07:55:18 UTC
on 2026-10-28. Total active duration/CPU/RSS UNKNOWN; no renewal requested.
Primary retains the entire grant for accounting. No scratch/generated-output
lease exists for this producer. **STOP: both leased files frozen; writes
stopped; no descendants.**
