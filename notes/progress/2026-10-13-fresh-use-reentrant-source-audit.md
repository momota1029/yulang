# FreshUse capture order and reentrant compensation

Date: 2026-10-13
Status: independently reviewed source characterization and conditional constructor derivation
Baseline: `09e1219bb2c31036ea70cdee1a75537b08e8c696`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this note only
Budget: static only, at most twenty minutes, zero heavy processes

## Objective, method and authority

Trace the reviewed private restoration discriminator through real public
candidate ingress, publication, capture, preparation and ordered FreshUse
restoration. The method is a producer/consumer audit plus a conditional
capture-derived finite history; it does not rerun the private helper experiment
or read the concurrent constructive producer's unpublished artifact.

Governing sections are the Authoritative top-level inference principles §§1–4
and successful-suspension clause; private candidate suspension contract §4's
saved-count/live-index behavior; design-authority **Authority order** and
**Natural compiler behavior and proof-obligation economy**; compiler-engineering
**Natural compiler behavior and proof-obligation economy**; research-lab
**Evidence quality and stopping unproductive loops** and **Commit conveyor**;
git-concurrency **Disjoint-file mode**. The primary pins the native Simple-sub
meaning and the reviewed constructor discriminator. Pending questions supply
no permission-field authority here. No source restriction, snapshot repair,
all-pair registry or solve-at-generation rule is proposed.

Result: actual capture prevents copying the private state verbatim into a
fresh local owner. An earlier row's replay can nevertheless preload Function
uppers before a later owner's captured lower. Captured direct bounds do **not**
stabilize the physical separator: physical insertion always appends, including
duplicate row IDs. In the finite history below, a real capture-derived sequence
can still omit one direct selection, but a later captured upper necessarily
compensates. This is not an authentic source counterexample, a universal rescue
theorem, or closure of the original coverage obligation.

## Actual public producer chain

All locators refer to the pinned baseline.

| Stage | Actual owner | Established constructor fact |
| --- | --- | --- |
| Source formation | `yu-hir/src/shadow.rs:38–58`; `module.rs:1412`; `module/local_source.rs:264–394,491–812` | Parsed binding lowering constructs the immutable owner-qualified LocalSource carrier; `HirModule::local_source` checks the exact artifact root. A public facade alone is not evidence for a chosen private row table. |
| Candidate ingress | `shadow_apply.rs:78–116`; `lib.rs:904,1126–1136` | `CandidateInference::solve` preflights the carrier and collects it with candidate Values and graph Effects enabled. Collection calls `emit_candidate_source`; no arbitrary Graph argument enters this facade. |
| Source scheduling | `candidate_source.rs:170–499,644–685` | Published local Names select `Action::Local`; references to a currently forming function initializer select `Link`. Module Names select registered DefinitionUse routing. Initializer execution precedes `Install`/`LocalAnnotation` publication. |
| Local publication/use | `candidate_scheme.rs:1310–1398,1500–1518` | Installation retains a live root/boundary. A LocalUse transaction recaptures that live root, immediately prepares one FreshUse, and advances its bound cursor only after each restoration retires. Final Value linking happens after all captured bounds. |
| Definition publication/use | `candidate_scheme.rs:843–935,947–978,1270–1305`; `lib.rs:16688–16692` | All SCC member actions finish before group capture/publication. Incoming DefinitionUse recaptures the stored live root/boundary, immediately prepares/restores the graph, then routes the fresh root to the occurrence. Open SCC uses route live roots through `route_internal`; they are not FreshUse capture. |

### Sharing, representatives, evidence and order

`Capture::intern` canonicalizes endpoints and `Capture::row` deduplicates
canonical row keys (`candidate_scheme.rs:290–327`). A row is local exactly
when its canonical level exceeds the boundary and it is generic.
`expand_row` stops at nonlocal rows, preserving their live mutable bounds in
the session (`:570–573`). Consequently older/nongeneric anchors can occur as
shared endpoints, but cannot be selected arbitrarily as captured restoring
owners.

Every local Value row emits a contiguous bound block in this order:
direct lowers, direct uppers, exact lowers, exact uppers (`:577–615`). Each
physical bound can emit multiple relation records through its authentic
bound-fiber cursor; key dedup includes relation identity (`:526–566`). This is
not one universal record per scalar pair. All root-row bounds precede the
blocks of rows discovered through them (`:755–760`).

Capture holds `&InferenceSession`; it cannot settle intrusion while enumerating.
Both actual incoming routes call preparation immediately after recapture.
Preparation allocates rows, terms, remapped views/contexts/bundles and imported
evidence; it does not run typed constraints or settle intrusion (`:981–1219`).
Thus these routes supply no capture-to-prepare representative mutation.
Distinct canonical generic rows map to distinct newly allocated empty rows at
the common use level; nongeneric/older rows share their canonical source.
Fresh allocation uses `VariableBounds::default()` (`lib.rs:10156–10176`).
The defensive canonical map in preparation is not an admission of arbitrary
post-capture merges.

`begin_candidate_fresh_bound` preserves captured side and obtains both terms
from the prepared nodes. It imports the actual antecedent and supplies
`FreshUse { antecedent, use_origin, source_bound, mapped_relation }`, constructing
fresh transport and attachment mappings only from captured relation inputs
(`candidate_scheme.rs:1221–1266`). No evidence, graph field, relation or source
origin is invented by this audit.

## Conditional finite history through the capture owner

This history isolates the earlier-block seam. It uses real constraint,
capture and restoration rules, but **its source ingress/root/level realization
has not been supplied**. It is a conditional constructor history, not a
source-qualified witness or an executed experiment.

Hypotheses: canonical distinct Value rows `a,r` at level 1 and root `b` at level
2; capture boundary 0; generic metadata; no extrusion parents or merges;
identity specialization of the relevant contextual children; successful finite
drains and sufficient identities/storage. Positive `g` has negative argument
`r`, empty argument Effect, bottom result Effect and Int result. Negative `f1`
has positive argument `a`, bottom argument Effect, empty result Effect and Int
result. Negative `f2` has **UnitPositive argument**, bottom argument Effect,
empty result Effect and Unit result. The private fixture's Value Bottom
argument is unnecessary for separator growth and is not assumed here.

Start with empty rows and ordinary typed admissions in this order:

```text
a <= b
b <= f1
b <= f2
g <= a
```

Because `level(b)>level(a)`, `candidate_apply_value` stores `a` as a direct
lower of `b`. Its two upper admissions replay through that lower and store
`f1,f2` as exact uppers of `a`. The last admission replays `g` against both
Functions. The `f1` argument child `a <= r` stores a direct upper `r` on `a`;
ordinary replay queues `g <= r` behind the already queued `g <= f2`. The `f2`
argument stores Unit on `r` before that queued comparison stores `g` there,
and its result produces the Int/Unit diagnostic. These consequences follow
from `candidate_extrusion.rs:763–837` and `lib.rs:12498–12538`.

The relevant original rows therefore include:

```text
b: direct lowers [a]; exact uppers [f1,f2]
a: direct uppers [r]; exact lowers [g]; exact uppers [f1,f2]
r: exact lowers [UnitPositive,g]
```

This table is derived from the stated typed admissions; it is not a raw Graph
fixture. The original diagnostic already prevents a conflicting graph from
being exportable (`shadow_apply.rs:123–131,149–153`). No absence of inherited
diagnostics is claimed.

Real capture of `b` discovers `a`, then `r`, and emits the blocks:

```text
b block: lower a; upper f1; upper f2
a block: upper r; lower g; upper f1; upper f2
r block: lower UnitPositive; lower g
```

In the prepared use all three generic rows have the common use level; denote
them `b',a',r'`. The `b'` lower restoration installs `a'`. Its `f1'` and `f2'`
upper restorations synchronously drain `a' <= f1'` and `a' <= f2'`. Those ordinary
children preload `a'.exact_uppers=[f1',f2']` while `a'` still has no lowers.
Next the captured `a' <= r'` direct bound is installed with zero lowers.

That installation does not itself run the typed pair `a' <= r'`; it merely
emits the bound and restores its opposite products. Physical insertion has
no `contains`/dedup guard (`candidate_extrusion.rs:417–502`). If the new pair's
memo is not current, the later `g' <= f1'` argument child therefore appends a
**second** `r'`. Canonical row-map dedup does not suppress this physical append.

Restoring `g'` into `a'` saves count 3, initially direct `[r']`, exact
`[f1',f2']`. Its selections can be:

```text
index 0: r'      (stores g' as a lower of r')
index 1: f1'     (argument child appends a second direct r')
index 2: f1'     (current direct length is now 2)
```

As in the reviewed private discriminator, direct selection of `f2'` is omitted.
If contextual/memo processing instead reuses the argument pair, this conditional
shift does not occur; nothing in this note claims the opposite without that
explicit premise.

However the **same captured a-block still contains its f2-upper restoration**.
At that restoration, `a'.direct_lowers=[]` and `a'.exact_lowers=[g']`.
The preceding `f1'` comparison adds only uppers to `a'`, and its other fields
do not create lowers there. Thus the saved opposite count for `f2'` is 1 and
index 0 selects `g'`. FreshUse replay starts from the full current fiber product
and synchronously drains its children; the Int/Unit result comparison is
dispatched or its current diagnostic is reused. Later `r'` records occur after
this comparison and cannot remove the fact that it was selected.

This establishes a conditional later-compensation lemma for this finite
capture-derived envelope. It shows why preloading alone is insufficient for
the requested unrescued source failure. It also corrects a tempting but false
argument that captured `a <= r` prevents direct-prefix growth.

## Exact source-owner cut and omitted cases

For direct root capture of the private two-row shape, an authentic captured
lower `g` on local `a` is restored before that same row's captured `f1,f2`
uppers. A shared `a` supplies no captured owner block. These facts exclude the
literal direct transfer of the private helper prestate; they do not exclude
preloading from an earlier block.

The finite earlier-block history above stops before actual source qualification:
the selected public source producer must supply the root/boundary and level
history, the four original source constraints, and authentic occurrence/context
lineage. In particular, source bodies start at level 1, local initializers add
one level and local publication retains its enclosing boundary
(`candidate_source.rs:254–263,288–327`). Choosing `b` at level 2 with boundary 0
is not itself such a source history. Its already detected original Int/Unit
conflict also fails the no-inherited-rescue requirement.

A decisive remaining history must additionally explain **why f2 preloaded on
the prepared a-owner has no effective later captured-upper rescue**, or show a
real lower-prefix mutation/representative change that defeats that later
restoration as well. It must preserve the original constraints and account for
their existing diagnostics and contextual consumer. The missing premise is
at the original publication/capture-to-prepared-row correspondence, not the
private live-index helper.

Intrusion is not free representative dedup. Only retained parent/copy pairs
in one actual dependency SCC merge (`candidate_intrusion.rs:477–490`); merge
appends both sides, transfers origins, redirects, canonicalizes third-owner
bound fibers, advances the generation, and replays the parent's lowers
(`:513–604`). Such replay can supply compensation. Capture/prepare cannot be
assumed to merge keys, and a restoration-time merge cannot be asserted without
this complete source history. The finite derivation has no parents, so the
explicit empty-parent settlement branch applies (`:370–374`).

Side boundary only: the exact private f2 Value Bottom port has no direct
LocalSource annotation constructor (`SourceAnnotationValue` is
Unit/Int/Variable/Function), while Apply uses source argument rows and Lambda
uses rows/formal domains. Native fresh reconstruction creates Value Bottom
only from an already captured Bottom node; the temporary capture placeholder
is fully expanded before capture returns. Legacy closed freshening can create
Bottom but incoming graph routing bypasses that path. This does not obstruct
the analogous Unit/source-row discriminator and is not the next-action gate.

## Checks, independence and resources

Checks run: bounded `cat`, `sed`, `rg` source/authority/caller reads; read-only
`git rev-parse HEAD`, `git status --short`, and a direct dependency
`git diff --name-only <baseline> -- <listed source/authority/discriminator paths>`;
SHA-256 hashes; lease-scoped whitespace check. The inspected direct paths had
no baseline diff. Some initial combined command captures were truncated;
the owning capture/preparation/insertion/replay/merge and source-chain sections
were subsequently read narrowly. No whole-repository absence claim follows
from those initial searches.

No executable oracle or checker was used. The derivation shares the pinned
transition rules and selected authority; it does not independently prove the
source rules or review the constructive producer. There are no seeds, ranges,
enumerated counts, mutation runs, runtime probes, tests, builds or measurements.
Zero heavy processes; light static reads only. CPU/RSS were not measured.
The assigned wall cap was twenty minutes; writes stopped within that cap.
Requested/effective runtime model metadata were not supplied to this leaf.

Unverified: exact source admission of an earlier-block discriminator, all shared
and nongeneric histories, nonidentity contextual products, restoration-time
redirection, original/inherited diagnostic coverage, general later rescue,
complete Call, L4, soundness, principality and F5 replacement. All original
parent gates remain OPEN.

Recommended next action: primary assign one actual publication/capture history
whose earlier block preloads a future a-owner's f2, then require the authentic
reason its own later captured f2 restoration is absent or ineffective. Track
shared-row orientation, captured relation incidence and merge replay there;
do not repeat private shifted-vector probes or treat fixture Bottom as a
supported-source restriction.

## Frozen dependency hashes

```text
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df  crates/yu-solver/src/candidate_effect.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411  crates/yu-solver/src/shadow_apply.rs
2fd2114389a595721c0b7631b5fdf602ccfbc024df7db144649eae05f681f133  crates/yu-hir/src/module.rs
8008b84738990cb22199d386129ecb810f86c907e222da40411cddb18eb279f7  crates/yu-hir/src/module/local_source.rs
a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb  crates/yu-hir/src/module/source_annotation.rs
687b49061273974fe874a8479a8db91ba24cc77fe92e6d2b96ae46a3626cf9dc  crates/yu-hir/src/shadow.rs
734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d  notes/design/2026-10-11-private-candidate-suspension-contract.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
b98c41d86c8ef9c5b0ba0430d0f0c18d43fc9f9e9eb42fb7dd85e629ec85822f  notes/progress/2026-10-13-restoration-live-index-pair-audit.md
```

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-13-fresh-use-reentrant-source-audit.md`.
- Baseline SHA: `09e1219bb2c31036ea70cdee1a75537b08e8c696`.
- Changed dependency hashes: none observed; primary rechecks the frozen list.
- Review status: frozen producer-only, unreviewed research; one fresh referee is primary-owned.
- Checks already run: narrow static producer/consumer and authority reads, direct baseline equality, dependency hashes and lease-scoped whitespace check; no execution.
- Proposed one-line commit: `research: trace FreshUse reentrant capture order and later compensation`.
- Shared-record deltas left to primary/curator: record actual fresh-row/anchor/order restrictions; distinguish canonical row-map dedup from unconditional physical append; record conditional later f2 compensation and the remaining original-source/capture/consumer seam. Keep original coverage, complete Call, L4, soundness, principality and F5 OPEN. No shared task/index/authority/question file was edited.

## Primary review and application

One fresh independent `compiler_referee` reviewed this audit and the separate
[constructive producer derivation](../theory/2026-10-13-fresh-use-restoration-disposition-proof.md).
There were no BLOCKING or major findings. The primary corrected the only minor
source-order issue: ordinary replay queues `g <= r` after the already queued
`g <= f2`, so the original and captured r-lower order is Unit then g. That
entire block follows a's block; the later f2 compensation result is unchanged.
The earlier producer commit packet records its pre-review status.

The actual capture/prepare owners now discharge the delayed-Graph and arbitrary
shared-owner premises for the two current production entry routes. The bounded
later-upper restoration provides the missing direct comparison in these
constructor histories. It supplies no accepted source-program failure, general
incidence theorem, nonidentity transport law or F5 closure. The primary applies
these results to the original bulk-coverage seam and synchronizes task records;
remaining earlier-block/lower-prefix/merge and source-history premises retain
their original owners. Post-review checks are static artifact/dependency
integrity only, without repeated builds, tests, probes or measurements.
