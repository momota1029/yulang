# R75 constructive relation-role proof — author handoff, revision 2

Final author status: **CHECKER ACCEPTED (flattened stdin); STOPPED / WRITES
STOPPED**. All 13 theorems passed the separately authorized amendment-01
audit with complete printed types and transitive axiom reports below. Only
`propext` and `Quot.sound` occur; no `sorryAx` remains. First-audit failures and
its pinning deviation are preserved as historical evidence. Imported project
build/integration, Rust extraction, genuine R66 `Root`, original A/B and
production are not closed. Independent review remains with the primary.

Assignment: `/root/r75_proof`, registered `lean_prover` leaf. Baseline
`6cd31c3043f142a8500eb9ea8d8095a1296f4f8d`; admission `f0217b942`.
Contract SHA-256 `bbeb3cc4bf26a8fe29b2144dc086e6e0efa6bd7c0f9d2ec5ab8aeab8401db3fb`;
initial manifest SHA-256 `6bca174a95365afbf71a4919ec82f15b6ef7f5493880d9c6772a5d52bd116a9a`.
Exact write lease: this handoff and
`notes/theory/lean/YulangClosure/DistinctSourceEmissionRootR75.lean` only.
No descendants, Git mutations, compiler changes, environments, worktrees,
builds, targets, caches, scratch files, generated files, tests or Lake commands.

## Claim, original parent and correspondence

The fixed R75 claim is the relation-role defect in its contract, not a new
language claim. Governing originals read: top-level inference principles
`notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–4;
the frozen original statement in
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §1, with the
current birth-level correction
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. The parent ranges
over every supported original source program and lawful finite history, keeps
shared source witnesses and complete Call/effect hygiene, and requires source
typing, principal coverage, soundness, progress and termination. No restriction
of that domain or replacement witness is introduced here. These source notes
are not an assertion that the parent is proved.

Actual Lean definitions read: R47 `Endpoint`, `Inputs.relationPair`, `Query`,
`Probe`, `ancestryCheck`, `RelationPath`, `RootMatches`, `Matches`, `extract`;
R45 `UseId` and owner incidence definitions; R66 `sourceProbe`, `Incidence`,
`BeforeAncestry`, `Root`, `readRoot`. Source mapping is direct:

* `candidate_context.rs:3132–3165` checks the indexed emission/admission against
  the current Effect bound, checks its relation's pair, separately selects the
  completed source-use root, then calls
  `require_relation_ancestry(emission_relation, source_root_relation)`.
* `checked_internal_use_root` selects source origin/drain evidence using the
  actual source use and Value pair. `relation_pair` is a functional indexed
  table reader. `TypedPairKey::Value` and `::Effect` are disjoint variants.
* Baseline `candidate_receiver.rs:1824` incorrectly equates the optional
  admission relation with the retained source root. R75 `OldEqualityGuard`
  represents exactly that equality. This is a static obstruction in a private
  feature observer, not an executed ordinary-inference counterexample.
* R47 already stores `Query.rootRelation` separately from `Probe.relation`.
  `ancestryCheck e root path emission` checks root-to-descendant graph edges;
  the Rust helper takes descendant then ancestor. Those argument orders express
  the same direction. No ancestry weakening is proposed or proved.

The new general lemma uses all four R47 endpoint constructors: value row and
atom versus effect row and atom, arbitrary `Id : Type`, arbitrary functional
reader and arbitrary natural relation IDs. It requires both endpoints of the
source pair to be Value endpoints and both endpoints of the emission pair to
be Effect endpoints. It derives the IDs' inequality from constructor
disjointness and function congruence. No Id equality instance is required.

`RelationRoles` retains the original `q` and `p` and checks source pair read,
emission bound pair read, optional admission relation and unchanged ancestry.
`LocalOwnership` retains every other R47 `Matches` conjunct, including indexed
readbacks, unique physical emission, current bound and `RootMatches`.
`matches_from_local_ownership_and_roles` rebuilds exactly R47 `Matches` from
these explicit local premises; it does not construct them from Rust.

The finite fixture has source relation 0 reading `(valueRow 30,valueRow 31)`,
emission relation 1 reading `(effectRow 21,effectRow 20)`, dependencies
`[(0,1)]`, and ancestry witness `[1]`. Its current Effect row, single indexed
admission/emission, historical readback and completed source/drain fields are
all supplied explicitly. Its intended discrimination is full R47 `extract`
success while the old optional-admission equality fails. It is a synthetic
finite R47 model, not a Rust extraction or R66 source/native instance.

## Frozen source bytes and execution environment

| Input | SHA-256 |
| --- | --- |
| R39 `ComputationPermissionEntryR39.lean` | `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e` |
| R45 `InternalPermissionIncidenceR45.lean` | `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f` |
| R47 `CurrentEmissionOwnershipR47.lean` | `d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c` |
| Initial audited R75 module | `8e80dc31a096b7f8290f81bd4591ca9f279c9b5cf795b3b9e19c303bd5f4fe00` |
| Repaired R75 module, authoring complete | `e868eb6bc6cba74af4f3096cc7fb2e48503c8183e064071b84022923c2bc6821` |
| Native Lean executable | `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38` |

Native executable:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`.
Its read-only `--version` returned exit 0:
`Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`.
Project pin, `lakefile.toml` and `lake-manifest.json` were read: Lean 4.35.0,
no external project packages. Existing project `.lake/build/lib/lean` was
absent; no build or installation was attempted. R39 imports the toolchain's
already installed `Std` artifacts.

The one executed check flattened R39, R45, R47 and R75 in that order in memory,
removed only lines beginning `import YulangClosure.`, retained `import Std`,
joined modules with a newline, then appended `set_option pp.universes true`
and a `#check @...` / `#print axioms ...` pair for every `theorem` in R75 source
order. Definitions and proofs from dependencies were otherwise byte-preserved.
No scratch or audit input/output file was created.

Exact command (cwd `notes/theory/lean`, environment `LEAN_NUM_THREADS=1`):

```text
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --stdin
```

Python `subprocess.run(..., input=stdin, text=True, capture_output=True,
timeout=120, env=env, cwd=root)` bounded the invocation. Input 64,215 bytes,
SHA-256 `dff3f4dd94d00e90ca2bdc6658ca423fb3d14f635d5c9c4cb762181b7d98d3a0`.
Exit **1**, elapsed **6.625 seconds**. No timeout. Complete stdout/stderr was
returned in runtime session `94719`, completion chunk `1c8e58`, including all
13 full printed theorem types and axiom reports. That retained runtime receipt
is the complete raw output; diagnostics and every axiom result are transcribed
below. CPU/RSS telemetry was not collected; `-M1024` is the Lean resource flag,
not a measured resident-memory claim.

**Protocol deviation:** R39 was measured before invocation, but was not in the
primary's frozen initial input manifest. The primary's pause message arrived
after the invocation had started. I immediately reported that ordering and the
R39 hash; this check therefore did not satisfy prior manifest pinning for R39.
No second execution has occurred. A prospective second input is frozen at
64,305 bytes, SHA-256
`8b3b30ed3a8333573aa5a78b923819491be56456f7d0e958085a4f0ec119d91c`,
using the repaired R75 bytes and the same exact transformation/footer. A
separate primary amendment is required before that input may execute.

## First audit diagnostics and theorem receipts

The first check emitted unused section-variable warnings for
`roles_preserve_ancestry` (Artifact/Id/Fact equality instances) and
`matches_from_local_ownership_and_roles` (Artifact/Fact equality instances).
The repaired source removes those unused hypotheses.

The material errors, verbatim:

```text
<stdin>:1254:18: error: failed to synthesize
  Decidable (ValuePair mixedSourcePair)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
<stdin>:1254:18: error: failed to synthesize
  Decidable (EffectPair (boundPair mixedProbe.admission.bound))

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
<stdin>:1257:2: error: failed to synthesize
  Decidable (LocalOwnership mixedInputs mixedQuery mixedProbe)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

The cause was author-written `decide` before unfolding the user predicates.
The repaired `mixed_roles` uses explicit `True` pair constructors and reflexive
read equations; `mixed_local_ownership` unfolds `LocalOwnership` before deciding
its finite equations. No premise or represented case changed. At that stage the
repaired module was **CONSTRUCTED, UNCHECKED** as a whole; the amendment-01
receipt below supersedes that execution status while preserving the failure.

Fully qualified namespace for every theorem below:
`YulangClosure.DistinctSourceEmissionRootR75`. Types below omit only qualified
R47 namespace prefixes and universe display, retaining all binders/premises.
The first six were accepted in the initial audit; their source proof terms are
unchanged except removal of unused instance binders in the last two. Their
complete transitive axiom lists were:

| Theorem | Printed type / premises | Axioms from first audit |
| --- | --- | --- |
| `value_effect_disjoint` | `∀ {Id : Type} (v e : Endpoint Id), IsValue v → IsEffect e → v ≠ e` | `[propext]` |
| `typed_relation_ids_distinct` | `∀ {Id : Type} (read : Nat → Option (Endpoint Id × Endpoint Id)) (source emission : Nat) (sourcePair emissionPair : Endpoint Id × Endpoint Id), read source = some sourcePair → read emission = some emissionPair → ValuePair sourcePair → EffectPair emissionPair → source ≠ emission` | `[propext]` |
| `roles_distinct` | `∀ {Artifact Id Fact : Type} (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact) (p : Probe Id) (sourcePair : Endpoint Id × Endpoint Id), RelationRoles e q p sourcePair → q.rootRelation ≠ p.relation` | `[propext, Quot.sound.{u}]` |
| `old_guard_rejected` | `∀ {Artifact Id Fact : Type} (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact) (p : Probe Id) (sourcePair : Endpoint Id × Endpoint Id), RelationRoles e q p sourcePair → ¬ OldEqualityGuard q p` | `[propext, Quot.sound.{u}]` |
| `roles_preserve_ancestry` | `∀ {Artifact Id Fact : Type} [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Fact] (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact) (p : Probe Id) (sourcePair : Endpoint Id × Endpoint Id), RelationRoles e q p sourcePair → RelationPath e q.rootRelation p.relation` | `[propext, Quot.sound.{u}]` |
| `matches_from_local_ownership_and_roles` | `∀ {Artifact Id Fact : Type} [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Fact] (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact) (p : Probe Id) (sourcePair : Endpoint Id × Endpoint Id), LocalOwnership e q p → RelationRoles e q p sourcePair → Matches e q p` | `[propext, Quot.sound.{u}]` |

The seven fixture declarations below were printed after Lean's error recovery.
They are **NOT accepted results**: their complete axiom lists contain
`sorryAx` introduced by recovery from the failed proof tactics, despite no
literal `sorry` or `admit` in the authored source.

| Theorem | Printed type | Complete first-audit axioms |
| --- | --- | --- |
| `mixed_roles` | `RelationRoles mixedInputs mixedQuery mixedProbe mixedSourcePair` | `[propext, sorryAx.{u}, Quot.sound.{u}]` |
| `mixed_local_ownership` | `LocalOwnership mixedInputs mixedQuery mixedProbe` | `[propext, sorryAx.{u}]` |
| `mixed_matches` | `Matches mixedInputs mixedQuery mixedProbe` | `[propext, sorryAx.{u}, Quot.sound.{u}]` |
| `mixed_ancestry` | `RelationPath mixedInputs mixedQuery.rootRelation mixedProbe.relation` | `[propext, sorryAx.{u}, Quot.sound.{u}]` |
| `mixed_old_guard_rejected` | `¬ OldEqualityGuard mixedQuery mixedProbe` | `[propext, sorryAx.{u}, Quot.sound.{u}]` |
| `mixed_accepted` | `extract mixedInputs mixedQuery mixedProbe = some ⟨mixedQuery,mixedProbe⟩` | `[propext, sorryAx.{u}, Quot.sound.{u}]` |
| `mixed_discriminates` | `extract mixedInputs mixedQuery mixedProbe = some ⟨mixedQuery,mixedProbe⟩ ∧ ¬ OldEqualityGuard mixedQuery mixedProbe` | `[propext, sorryAx.{u}, Quot.sound.{u}]` |

## Parent application and remaining premise

The relation-role theorem applies to any actual source/native extraction that
faithfully reads the Value root pair and fresh Effect admission pair from one
functional relation table. It refutes the old cross-role equality for that same
extraction; it does not assume an R66 `Root` or successful `readRoot`/policy.
The ownership composition explicitly preserves R47 obligations rather than
silently discarding physical uniqueness, readbacks or source drain identity.

First missing owner evidence for genuine R66 construction remains the
source-owned unique plan at the same occurrence (R66 `sourceProbe`), followed by
owner incidence/recipe facts and the native physical/readback/completed-root
fields. R73 decoded owner evidence alone contains neither the R55 source
inventory nor R57 native records that derive those fields. The Rust/source
owners and primary must supply that actual bridge. R75's finite fixture cannot
substitute for it. Actual extraction, genuine R66 `Root`, original A/B,
whole-language soundness/principality/termination and production remain OPEN.

Authoring completed at the repaired module hash above. The initial packet's
execution allowance was exhausted; amendment 01 subsequently authorized the
single second audit recorded below. No independent review has occurred. Module
bytes remained frozen throughout that audit. No further invocation is allowed.


## Amendment 01 second audit — complete retained receipt

Authorized at primary commit `b1f40e6f8`; preflight asserted all four source hashes, executable hash and exact stdin digest/size before invocation. Only the assigned handoff receives this receipt; no generated output file is written.

```json
{
  "command": [
    "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
    "-j1",
    "-M1024",
    "--stdin"
  ],
  "timeout_seconds": 120,
  "exit": 0,
  "elapsed_seconds": 6.718,
  "stdin_sha256": "8b3b30ed3a8333573aa5a78b923819491be56456f7d0e958085a4f0ec119d91c",
  "stdin_bytes": 64305,
  "stdout_sha256": "b1053c85ddf239c336f80964a5088533d80814db116592c7b0253b90353e029d",
  "stderr_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
  "theorem_count": 13
}
```

Complete stdout (unmodified):

```text
@YulangClosure.DistinctSourceEmissionRootR75.value_effect_disjoint : ∀ {Id : Type}
  (v e : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  YulangClosure.DistinctSourceEmissionRootR75.IsValue v →
    YulangClosure.DistinctSourceEmissionRootR75.IsEffect e → Ne.{1} v e
'YulangClosure.DistinctSourceEmissionRootR75.value_effect_disjoint' depends on axioms: [propext]
@YulangClosure.DistinctSourceEmissionRootR75.typed_relation_ids_distinct : ∀ {Id : Type}
  (read :
    Nat →
      Option.{0}
        (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)))
  (source emission : Nat)
  (sourcePair emissionPair :
    Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)),
  Eq.{1} (read source) (some.{0} sourcePair) →
    Eq.{1} (read emission) (some.{0} emissionPair) →
      YulangClosure.DistinctSourceEmissionRootR75.ValuePair sourcePair →
        YulangClosure.DistinctSourceEmissionRootR75.EffectPair emissionPair → Ne.{1} source emission
'YulangClosure.DistinctSourceEmissionRootR75.typed_relation_ids_distinct' depends on axioms: [propext]
@YulangClosure.DistinctSourceEmissionRootR75.roles_distinct : ∀ {Artifact Id Fact : Type}
  (e : YulangClosure.CurrentEmissionOwnershipR47.Inputs Artifact Id Fact)
  (q : YulangClosure.CurrentEmissionOwnershipR47.Query Artifact Id Fact)
  (p : YulangClosure.CurrentEmissionOwnershipR47.Probe Id)
  (sourcePair :
    Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)),
  YulangClosure.DistinctSourceEmissionRootR75.RelationRoles e q p sourcePair → Ne.{1} q.rootRelation p.relation
'YulangClosure.DistinctSourceEmissionRootR75.roles_distinct' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.DistinctSourceEmissionRootR75.old_guard_rejected : ∀ {Artifact Id Fact : Type}
  (e : YulangClosure.CurrentEmissionOwnershipR47.Inputs Artifact Id Fact)
  (q : YulangClosure.CurrentEmissionOwnershipR47.Query Artifact Id Fact)
  (p : YulangClosure.CurrentEmissionOwnershipR47.Probe Id)
  (sourcePair :
    Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)),
  YulangClosure.DistinctSourceEmissionRootR75.RelationRoles e q p sourcePair →
    ¬YulangClosure.DistinctSourceEmissionRootR75.OldEqualityGuard q p
'YulangClosure.DistinctSourceEmissionRootR75.old_guard_rejected' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.DistinctSourceEmissionRootR75.roles_preserve_ancestry : ∀ {Artifact Id Fact : Type}
  (e : YulangClosure.CurrentEmissionOwnershipR47.Inputs Artifact Id Fact)
  (q : YulangClosure.CurrentEmissionOwnershipR47.Query Artifact Id Fact)
  (p : YulangClosure.CurrentEmissionOwnershipR47.Probe Id)
  (sourcePair :
    Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)),
  YulangClosure.DistinctSourceEmissionRootR75.RelationRoles e q p sourcePair →
    YulangClosure.CurrentEmissionOwnershipR47.RelationPath e q.rootRelation p.relation
'YulangClosure.DistinctSourceEmissionRootR75.roles_preserve_ancestry' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.DistinctSourceEmissionRootR75.matches_from_local_ownership_and_roles : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.CurrentEmissionOwnershipR47.Inputs Artifact Id Fact)
  (q : YulangClosure.CurrentEmissionOwnershipR47.Query Artifact Id Fact)
  (p : YulangClosure.CurrentEmissionOwnershipR47.Probe Id)
  (sourcePair :
    Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)),
  YulangClosure.DistinctSourceEmissionRootR75.LocalOwnership e q p →
    YulangClosure.DistinctSourceEmissionRootR75.RelationRoles e q p sourcePair →
      YulangClosure.CurrentEmissionOwnershipR47.Matches e q p
'YulangClosure.DistinctSourceEmissionRootR75.matches_from_local_ownership_and_roles' depends on axioms: [propext,
 Quot.sound.{u}]
YulangClosure.DistinctSourceEmissionRootR75.mixed_roles : YulangClosure.DistinctSourceEmissionRootR75.RelationRoles
  YulangClosure.DistinctSourceEmissionRootR75.mixedInputs YulangClosure.DistinctSourceEmissionRootR75.mixedQuery
  YulangClosure.DistinctSourceEmissionRootR75.mixedProbe YulangClosure.DistinctSourceEmissionRootR75.mixedSourcePair
'YulangClosure.DistinctSourceEmissionRootR75.mixed_roles' depends on axioms: [propext, Quot.sound.{u}]
YulangClosure.DistinctSourceEmissionRootR75.mixed_local_ownership : YulangClosure.DistinctSourceEmissionRootR75.LocalOwnership
  YulangClosure.DistinctSourceEmissionRootR75.mixedInputs YulangClosure.DistinctSourceEmissionRootR75.mixedQuery
  YulangClosure.DistinctSourceEmissionRootR75.mixedProbe
'YulangClosure.DistinctSourceEmissionRootR75.mixed_local_ownership' depends on axioms: [propext]
YulangClosure.DistinctSourceEmissionRootR75.mixed_matches : YulangClosure.CurrentEmissionOwnershipR47.Matches
  YulangClosure.DistinctSourceEmissionRootR75.mixedInputs YulangClosure.DistinctSourceEmissionRootR75.mixedQuery
  YulangClosure.DistinctSourceEmissionRootR75.mixedProbe
'YulangClosure.DistinctSourceEmissionRootR75.mixed_matches' depends on axioms: [propext, Quot.sound.{u}]
YulangClosure.DistinctSourceEmissionRootR75.mixed_ancestry : YulangClosure.CurrentEmissionOwnershipR47.RelationPath
  YulangClosure.DistinctSourceEmissionRootR75.mixedInputs
  YulangClosure.DistinctSourceEmissionRootR75.mixedQuery.rootRelation
  YulangClosure.DistinctSourceEmissionRootR75.mixedProbe.relation
'YulangClosure.DistinctSourceEmissionRootR75.mixed_ancestry' depends on axioms: [propext, Quot.sound.{u}]
YulangClosure.DistinctSourceEmissionRootR75.mixed_old_guard_rejected : ¬YulangClosure.DistinctSourceEmissionRootR75.OldEqualityGuard
    YulangClosure.DistinctSourceEmissionRootR75.mixedQuery YulangClosure.DistinctSourceEmissionRootR75.mixedProbe
'YulangClosure.DistinctSourceEmissionRootR75.mixed_old_guard_rejected' depends on axioms: [propext, Quot.sound.{u}]
YulangClosure.DistinctSourceEmissionRootR75.mixed_accepted : Eq.{1}
  (YulangClosure.CurrentEmissionOwnershipR47.extract YulangClosure.DistinctSourceEmissionRootR75.mixedInputs
    YulangClosure.DistinctSourceEmissionRootR75.mixedQuery YulangClosure.DistinctSourceEmissionRootR75.mixedProbe)
  (some.{0}
    { query := YulangClosure.DistinctSourceEmissionRootR75.mixedQuery,
      evidence := YulangClosure.DistinctSourceEmissionRootR75.mixedProbe })
'YulangClosure.DistinctSourceEmissionRootR75.mixed_accepted' depends on axioms: [propext, Quot.sound.{u}]
YulangClosure.DistinctSourceEmissionRootR75.mixed_discriminates : Eq.{1}
    (YulangClosure.CurrentEmissionOwnershipR47.extract YulangClosure.DistinctSourceEmissionRootR75.mixedInputs
      YulangClosure.DistinctSourceEmissionRootR75.mixedQuery YulangClosure.DistinctSourceEmissionRootR75.mixedProbe)
    (some.{0}
      { query := YulangClosure.DistinctSourceEmissionRootR75.mixedQuery,
        evidence := YulangClosure.DistinctSourceEmissionRootR75.mixedProbe }) ∧
  ¬YulangClosure.DistinctSourceEmissionRootR75.OldEqualityGuard YulangClosure.DistinctSourceEmissionRootR75.mixedQuery
      YulangClosure.DistinctSourceEmissionRootR75.mixedProbe
'YulangClosure.DistinctSourceEmissionRootR75.mixed_discriminates' depends on axioms: [propext, Quot.sound.{u}]
```

Complete stderr (unmodified):

```text
```

## Final disposition and review packet

The second audit exited 0 with no warnings/errors. Its first two theorems and
`mixed_local_ownership` have exactly `[propext]`; all ten others have exactly
`[propext, Quot.sound.{u}]`. There are no other transitive kernel axioms, no
`sorryAx`, and no `Classical.choice`. The final printed type of
`roles_preserve_ancestry` has no DecidableEq binders;
`matches_from_local_ownership_and_roles` requires only `[DecidableEq Id]`.
All other general/fixture type statements retain the earlier listed types.
Complete exact final printed types and lists appear in the raw receipt above.

The single successful flattening covers exact R39/R45/R47 dependency sources
and the entire R75 module; it does not claim project import-artifact or default
target integration. The skill's usual Lake checker could not be used under the
packet's explicit no-Lake/no-generated-output boundary. Existing `Std` import
artifacts came from the pinned native distribution. No project artifacts were
built or refreshed.

Reconstruction recipe for the byte-pinned stdin (all strings below contain
ordinary newline characters at runtime):

```python
modules = ["ComputationPermissionEntryR39", "InternalPermissionIncidenceR45",
           "CurrentEmissionOwnershipR47", "DistinctSourceEmissionRootR75"]
parts = []
for name in modules:
    raw = (root / "YulangClosure" / f"{name}.lean").read_bytes()
    parts.append("".join(line for line in raw.decode().splitlines(keepends=True)
                         if not line.startswith("import YulangClosure.")))
names = re.findall(r"^theorem ([A-Za-z_][A-Za-z0-9_]*)", module_text, re.M)
footer = "\nset_option pp.universes true\n" + "".join(
    f"#check @YulangClosure.DistinctSourceEmissionRootR75.{name}\n"
    f"#print axioms YulangClosure.DistinctSourceEmissionRootR75.{name}\n"
    for name in names)
stdin = "\n".join(parts) + footer
```

Static checks: source/dependency-cone `rg` for literal `sorry`, `admit`, project
`axiom`, `skipKernelTC` and `native_decide` found no matches; each delivered
theorem's transitive axiom report is the stronger executed evidence.
`git diff --no-index --check /dev/null` on the new module returned exit 0.
No tests, compiler, formatter, Lake or build ran. Two direct stdin checks total:
first 6.625 seconds, second 6.718 seconds, total 13.343 seconds; each carried
`-j1 -M1024`, `LEAN_NUM_THREADS=1` and a 120-second timeout. There was also one
read-only native `lean --version` invocation. No process remains running.
Exact author wall time, CPU and peak RSS are not separately measured.

Changed paths are exactly the two leased outputs; no scratch/generated path.
Proposed research checkpoint: `research: distinguish Value roots from Effect
emission relations in R75`. Primary must obtain fresh independent review and
retain the actual-source/R66/parent-claim boundaries above. This author packet
does not authorize integration or promotion by itself.

Final worker state: **STOPPED / WRITES STOPPED**. Module bytes are frozen at
`e868eb6bc6cba74af4f3096cc7fb2e48503c8183e064071b84022923c2bc6821`.
