# R140 independent static review

Verdict: **PASS for the bounded static research candidate.** No source/native
order divergence or mandatory repair was found in the reviewed construction.
Lean remains **CONSTRUCTED_BUT_UNCHECKED**. This verdict establishes neither
kernel acceptance nor all-source/native correspondence, parent closure or
production authority.

Reviewer: `/root/r139_review`, independent of `/root/r139_source` and
`/root/r139_proof` for R140. Active-work acknowledgement was sent to primary
before this sole output write. Packet bound: 240 seconds. No delegation.

## Frozen scope and authentication

All four frozen SHA-256 values were independently recomputed from bytes:

| Path | Bytes | SHA-256 |
| --- | ---: | --- |
| `tasks/agent-loop/sprints/effect-permission-ordered-snapshot-20261102-r140.md` | 4794 | `e81ff2ddd7cda47bfb60bc1738e0c5bc3bfce4eb9effc183dd725003b4db06d0` |
| `tasks/agent-loop/inbox/effect-permission-ordered-snapshot-r140-source.md` | 28566 | `3335922fa8b259a1f4dea95bbf72e4ee6db8a99d7dd22fce25b3909e91aa8f56` |
| `notes/theory/lean/YulangClosure/FormalPermissionOrderedSnapshotR140.lean` | 23626 | `da3baeabd61ff8fd30d078a4481f4a6c62ef5801cdb670f634e4d7c827add985` |
| `tasks/agent-loop/inbox/effect-permission-ordered-snapshot-r140-proof.md` | 21870 | `a0a8e21563435014b8da3c48bcae871ae87794e4f0ec68d842e243825364de05` |

Frozen dependency SHA-256 checks also match: R137 outcome
`82fd775010eb1b865928510bed1d34d282c0d46768f6ee93054ca0d670748231`;
R138 outcome `2cfe94f5dd822c4df4619fa194186c2537393c1c3ed8340e244f56b6e93ac480`;
R139 review `f40a05d3c791cdf4d10c98f283938e9347a5f1dbc68e6943d70a956c86d6b508`.

Baseline: `4c1d58a646a1101c080659ebfed6ae7862d8aded`. Without invoking Git,
Python `zlib` decoded the exact loose immutable objects and `hashlib` recomputed
their Git blob SHA-1 and source SHA-256:

| Immutable source | Git blob / bytes | Source SHA-256 |
| --- | --- | --- |
| `crates/yu-solver/src/candidate_effect.rs` | `18a4cafb4a1bb6466686d82aa825e28318f91a72` / 301873 | `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01` |
| `crates/yu-solver/src/candidate_source.rs` | `b43f37f4cca246a072b73329aed84e89aef4ebe1` / 212732 | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `YulangClosure/FormalPermissionConstructorR136.lean` | `2265896c38a8febf7fd41d10c9a49f9f4a1bc340` / 10356 | `3289bccd2b85dd4576adb1c4a870e635985b60e2e87c459d9174c4a0477eab4f` |

Two dependencies were packed and unavailable through the loose-object method.
Primary separately authenticated their baseline blob IDs/sizes with its own
read-only commands: `source_annotation.rs`,
`bd65e9f50e63cdbab53ee3b3c8f25958813b1ef5` / 35724;
`full_parse.rs`, `9e07c1546d36561d2a24192ced2c7ebbffd6d798` / 36778.
Those two confirmations are primary evidence, not this reviewer's independent
rehashing. Their exact immutable identity definitions were inspected in the
preceding R139 review; no packed working-tree replacement was read here.

## Source findings

1. **Same-call suffix:** baseline `candidate_effect.rs:1897–1976` agrees with
   the wrapper. The native call creates local permissions, starts the root
   value at Negative, appends the local vector at 1951–1954, samples resources
   afterward, and returns its final result. The wrapper records `before` from
   this session immediately before the one transaction/call, obtains the
   post-success suffix from the same session, and compares it before publishing
   a snapshot. It does not combine separate calls or snapshots. Later sampling
   failure is correctly included in the call's error boundary.
2. **Order/polarity/path:** `candidate_effect.rs:1661–1685` visits argument
   value with flipped polarity, result value with unchanged polarity, argument
   effect port, then result effect port. The candidate follows those equations,
   restores paths after recursive calls, and retains each Argument/Result or
   indexed Element step. R136's `inventory`/`ports`/`flatMap emit` has this order.
3. **Admission/filter:** `candidate_effect.rs:1601–1611,1691–1748` and
   `candidate_source.rs:701–715` match `valid_pair`, `emit_port` and Lean's
   `rowAllowed`/`supported`. Negative rows allow singleton symbolic/no concrete
   or nonempty concrete/no symbolic; positive rows allow at most one symbolic
   variable. Only the negative nonempty concrete/zero-symbol case emits a
   permission. Empty negative rows and mixed negative rows reject. Omitted,
   positive and singleton symbolic ports do not fabricate grants.
4. **Tuples and leaves:** baseline 1633–1659 rejects empty tuples and any
   immediate annotated tuple child, then traverses child values by index. The
   candidate and model retain those gates and all six leaf families. Lean
   retains unsupported tuple-row constructors and rejects them through its
   support predicate, rather than deleting them from the representation.
5. **Context and identities:** every compared record retains parameter,
   owner/index FormalPosition, occurrence, owner, scope, path, row and concrete
   member sequence. One complete-Eq table is threaded through expected, actual
   and root-entry images. All eight tags are represented, with FormalPosition
   distinct from Formal and scoped Symbol distinct from bare spelling. Each
   concrete member is appended, including repeats. Full Rust identity equality
   is preserved; no occurrence-injectivity or formal-index equation is inferred.
6. **Root entries:** the nested projection ignores the root annotation row,
   matching the direct root value-pair call. Root-entry records have their own
   shape/vector; the wrapper separately checks before/after equality and never
   concatenates them into the nested suffix. This is not a proof of root-entry
   construction or its source meaning.
7. **Failure/publication:** every returned constructor, encoding or comparison
   error precedes the only Snapshot return. Local partial images/table are not
   error payloads. Explicit reservation/checked-width failures are distinguished
   from infallible Clone allocation aborts. A comparison/encoding error after a
   successful native call does not promise rollback of that completed call;
   the candidate makes no such guarantee. Missing-key lookup is unused here.
8. **Fixture limitation:** baseline 3723–3765 statically contains the stated
   same-call AAR/RRR assertions, complete context comparisons and zipped source
   rows. Its explicit comment says the internal producer call bypasses source
   preflight and does not establish source acceptance. No test ran in R140.
   The frozen candidate is therefore useful internal-constructor evidence,
   not an actual new successful test receipt or whole accepted-source theorem.

No first mismatching constructor branch or retained field was found. R139's
three material corrections are retained: no SourceNodeKey occurrence-injectivity
claim, no total fallible-allocation claim, and the current R138 digest.

## Lean static proof review and limitations

Namespace: `YulangClosure.FormalPermissionOrderedSnapshotR140`. Every theorem
body was inspected, including the mutual recursion. No obvious false statement,
proof-body defect, strengthened source hypothesis, assumed native equality,
project axiom, sorry/admit or checker bypass was found. `Std` is the sole import;
the unchecked R139 module is not an imported proof dependency.

The complete 25-target surface is:
`inventory_order_filter`, `element_order_filter`, `record_fields`,
`concrete_length`, `concrete_position`, `concrete_duplicates`,
`positive_filtered`, `omitted_filtered`, `symbolic_filtered`, `empty_filtered`,
`concrete_emitted`, `mixed_negative_rejected`, `tuple_annotated_child_rejected`,
`empty_tuple_rejected`, `projection_success`, `root_row_separate`,
`fixture_order`, `exact_aar_rrr_fixture`, `exact_fixture_admitted`,
`exact_fixture_paths`, `exact_fixture_rows`, `exact_fixture_shared_effect`,
`appended_suffix`, `comparison_success`, `error_excludes_snapshot`.

All 25 have paired future `#check @...` and `#print axioms ...` commands.
For every target, actual printed type: **UNAVAILABLE**; transitive axiom list:
**UNAVAILABLE**; kernel acceptance: **UNVERIFIED**. Source-text inspection is
not a complete transitive dependency audit. No Lean execution was authorized.

The order theorem is constructive list equality over arbitrary modeled finite
values. `projection_success` additionally exposes the support gate. Records
retain all context fields and map ordered members through one table; the exact
fixture preserves AAR/RRR, both rows and the repeated shared effect. Tuple
indices and polarity are represented. The eight tags now match Rust's shapes.

Limits are accurately stated: Rust usize/u32 widths are represented with Nat;
table coverage, interning chronology, Eq/Clone correspondence, variable/hole
registration side effects, State/transaction behavior and native execution are
not proved. `idxOf` on absent keys remains a length sentinel. `appended_suffix`
is only append/drop algebra. `comparison_success` extracts an executed equality
test on supplied images; it cannot establish where those images came from.
`authenticated` projects arbitrary successful results, and its error theorem
proves error-result nonpublication, not a general authentication invariant.

## Parent application and remaining ownership

Original sources remain preservation §1 in
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md`, fixed birth-level
correction §§2–6, whole-proof closure §§1–3, and source manuscript `sec:owners`.
The latter does not promote candidate machine semantics to authority.

`YulangClosure.SourceProblem.InferenceSoundness` retains:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

The original source domain, scopes and shared witness are unchanged. The record
and proposition definitions supply no concrete instance. If checked, R140's
lemmas can justify the modeled order/filter/path projection used by this
same-call comparison. They do not construct the parent witness.

First remaining local goal: pinned elaboration and every type/axiom audit,
owned by primary Luna/verification under a separately authorized resource
decision. R139's prior exit -6 thread failures remain failure evidence; no new
version, goal, kernel or axiom output exists. Next bridge: instantiate the Rust
representation/table and relate every concrete successful suffix to this model,
owned by source/proof intake. Accepted-source key uniqueness, formal-index
correspondence, all-source/native equality, consumers/arrival/capture/copy/Catch,
A/B, effect-hygiene H and production remain OPEN with their existing owners.

## Commands, resources and stop

Actual commands used bounded `cat`, `sed`, `rg` reads and inline Python
`pathlib`/`zlib`/`hashlib` inspection; read/hash commands exited 0. The only
mutation was creation of this exact receipt through `apply_patch`. No Git
command, status/diff, dirty/quarantined source read, Lean/Lake/version/checker,
build/test/Cargo, installation, dependency change or environment probe ran.
No scratch/generated output, shared cache ownership or descendant exists.
CPU/RSS were not measured; work remained within the 240-second bound.

Exact changed path: this review receipt only. **STOPPED_WRITING** after freezing
this receipt; no outstanding writer/cache work. Primary retains adjudication,
state, integration and Git authority.
