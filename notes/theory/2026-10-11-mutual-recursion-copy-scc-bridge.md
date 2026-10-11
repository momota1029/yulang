# Mutual definition roots and the retained extrusion-pair boundary

Status: frozen unreviewed research; bounded native-constructor derivation
Parent claim: OPEN; no source parent/copy SCC witness or semantic counterexample
Read baseline: `2bcf389b086a7ae0457206f00738648c3f51865b`
Branch supplied by primary: `research/simple-sub-intrusion`
Exclusive output lease: this file

## Objective and frozen scope

Determine whether the actual mutually recursive definition roots can supply a
retained extrusion parent/copy pair, so that the independently reviewed source
reference witness can be used without another unknown-formal-value premise.
This is the primary's revised method: follow the original roots themselves,
not another local formal variant.

The reviewed exact source is fixed:

```yulang
my f x = g;
my g y = f
```

`f,g` are distinct module definitions; `x` and `y` bind only in their respective
Lambdas and neither is used. Let `F,G` be the actual allocated definition Value
rows from this one HIR/collection/session artifact, using the joint root map in
`2026-10-11-mutual-recursive-value-scc-proof.md`. Its reviewed result supplies
`F -> G` and `G -> F` in the source-value-reference graph. Occurrence rows are
separate identities. No reference graph is reconstructed from comparisons,
bounds, family metadata or a definition SCC plan.

The original required conclusion remains an existential, source-qualified
history with a retained distinct Value pair `(C,P)`, and actual source-value
reference paths `P ->* C` and `C ->* P` before the equality being justified.
Every endpoint and path must come jointly from that same history. The broader
parent gate over supported programs/histories is not narrowed by investigating
this source. This note supplies neither the witness nor a counterexample to the
approved operation.

The local native claim examined here quantifies over every completed, successful
`candidate_extrude` row visit of an actual original root `R` in `{F,G}`, with
`level(R)=1`, extrusion target `t >= 1`, and no prior identity-changing operation
on `R`: that visit maps `R` to itself and does not create a retained copy of
`R`. Separately, the authentic internal mutual Name transition does not invoke
extrusion on its root/occurrence pair. These are statements about actual
constructor control flow, not assumptions that make the SCC witness conditional
on its conclusion. The level/target guards are exposed; a whole-history theorem
that every future extrusion target is at least one is not asserted.

Successful checked allocation and arrival at the inspected native transitions
are explicit guards. Static inspection does not establish source execution,
replay completion, termination, inference acceptance or a published scheme.
No independently chosen interpretation of a formal/result or marginal witness
is used. Complete Call, effect hygiene, soundness, required principality and
ordinary native inference retain their original requirements.

## Governing sources and prior results

Authority: `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, **Selected
operation and compiler responsibility**, **Value-reference SCC clarification**,
and **Retained boundary**; and
`notes/design/2026-10-11-yulang-inference-top-level-principles.md`, §§1–5 and
**Evaluation**. The operation retains the actual parent at copy creation and
equates qualifying pairs; references in Value values determine SCC membership.

The reviewed original-root proof is reused only for its exact original source.
The nested source/operational audit
`notes/progress/2026-10-11-mutual-recursion-parent-copy-search.md` and reviewed
`notes/theory/2026-10-11-extrusion-copy-reference-proof.md` already leave formal
or Apply-result value ownership and extrusion transport unresolved. Their two
different variants are not retraced as new proof progress. In particular, their
conditional allocation of higher-level formal/result copies does not identify
those parents with `F` or `G`, and their source identities cannot be substituted
into the original-root theorem.

## Authentic mutual-use constructor route

1. Every collected Value component gets its own checked dense row and level one
   before fact admission (`crates/yu-solver/src/lib.rs:10047`–`:10089`). In
   particular `F,G` exist before any extrusion copy. Source planning begins at
   level one, preserves the level through Lambda/Name, and increases it only
   for Block initializers (`candidate_source.rs:253`–`:305`). The exact source
   has no Block; source initialization installs those planned expression and
   parameter levels (`:532`–`:541`). The module roots retain level one.

2. The component driver installs both actual roots and the internal uses before
   executing either source schedule (`candidate_scheme.rs:869`–`:889`). The
   module Name action routes its real occurrence using
   `route_candidate_open_use` (`:938`–`:945`), then `route_internal_inner`
   (`lib.rs:15770`–`:15792`). For the `g` occurrence in `f`, the actual task is
   `ValueRow(G) <: ValueRow(U_g)`, with both rows level one; the converse Name
   selects `F` and its distinct occurrence `U_f`. This identifies actual
   constructor endpoints; neither comparison is a graph edge in this note.

3. Row/row dispatch does not call `candidate_extrude`: the structural guard in
   `lib.rs:12412`–`:12441` excludes a row opposite another row. The next native
   owner `candidate_apply_value` (`candidate_extrusion.rs:809`–`:838`) chooses
   the storage/replay owner, inserts its bound and drives replay. Its body
   contains no copy allocation or parent retention. Thus the authentic mutual
   open use does not construct a retained `(C,G)` or `(C,F)` pair merely because
   its target belongs to the reviewed source SCC. Any replayed structural task
   has its own extrusion transition and cannot be credited to an unexecuted
   row/row copy.

4. Lambda constructs its argument from the actual parameter row and its result
   from the actual body occurrence component (`lib.rs:11233`–`:11260`). Fresh
   entry/return Effect rows are allocated at the parameter's level
   (`:11272`–`:11274`), with all four Function ports retained (`:11342`). On the
   LocalSource route, the Lambda expression row subsequently links to the
   definition root (`candidate_source.rs:445`–`:458`, `:492`–`:495`). This
   confirms that a source Name whose target is `G` does not itself replace a
   structural result port `U_g` by the target-root row `G`. No semantic edge out
   of `U_g` is assumed here. The reviewed direct source edge `F -> G` remains
   valid without that additional occurrence-row bridge.

The first constructor boundary on the proposed direct root route is therefore
the row/row admission at step 3: mutual Name use supplies the original target
root and a comparison with its occurrence row, but supplies no extrusion-copy
constructor on that target.

## If a later extrusion visit actually reaches an original root

The stronger local control-flow fact prevents rescuing the route just by
following an existing endpoint deeper into an extrusion operation.

At `candidate_extrude` (`candidate_extrusion.rs:21`), the initial endpoint is
canonicalized and visited with one polarity and target. At a row visit the
constructor reads that actual row's level (`:70`–`:78`). Before it snapshots
any selected bound, it tests `original_level <= target`; when true, it
memoizes the **same endpoint** and immediately continues (`:83`–`:86`). Copy
allocation, parent retention, the one-sided link and scheduling of selected
payloads occur only after that guard (`:89`–`:157`).

For an unmodified original root `R` with level one and target `t >= 1`, the
inequality `1 <= t` holds. Consequently this visit returns `R` itself, creates
no `(C,R)` Parent record and does not descend into `R`'s selected payloads.
For any polarity this follows from the same guard, before polarity selects a
snapshot. If `R` is initial, the operation's final root-map lookup returns `R`
(`:357`–`:368`); if it is a child, Function reconstruction reads that same
entry (`:325`–`:353`). Other branches in the operation may create other copies;
the statement excludes only a new copy whose original is this guarded `R`.

Actual structural-to-row dispatch takes its target from the receiving row's
current level (`lib.rs:12418`–`:12436`). The reviewed exact source's initial
receivers have level one. In the already inspected nested mutual source
prefixes, receivers are at levels one or two and the original module roots
remain at level one. Hence neither the authentic use transition nor a reached
root Visit at those targets makes an original root a retained parent.
This last application is prefix-scoped; later arbitrary history, injected
rows, failure reuse and external API calls are not proved to share these guards.

An original root also cannot be the newly allocated raw **copy** identity of
such an operation. `fresh_value_at_level` allocates at the current row-vector
length and appends a new row (`lib.rs:10156`–`:10177`); the original roots were
already allocated in its component prefix. Successful append therefore has a
different ordinal. No subsequent canonical equality is used to defeat this
distinction. `retain_extrusion_parent` records precisely the fresh output and
actual visited original (`candidate_intrusion.rs:171`–`:220`).

This is a bounded native derivation. It does not convert numerical levels,
storage or Parent provenance into source-reference edges, and does not prove
that semantic values lack references crossing a family tree.

## Generalization boundary zero is a different constructor

The component driver calls `capture_candidate_graph(root, 0)` after member
schedules (`candidate_scheme.rs:890`–`:903`). That zero is the captured graph's
generalization boundary. The call is not `candidate_extrude(root, ..., 0)`.
Capture classifies rows by level versus boundary (`:309`–`:321`); it does not
retain an extrusion Parent for the captured definition root.

Later scheme use calls `prepare_candidate_fresh_use` (`:982`), which allocates
generic local rows at the use level and shares the rest (`:1008`–`:1021`). This
is a genuine separate constructor. The inspected scheme implementation has no
`retain_extrusion_parent` call. A fresh scheme-instance root must not be
relabeled an extrusion copy of `F` or `G`. Reference transport for that fresh
instance remains another source/operation law; the original-root source SCC
does not establish it automatically.

Likewise, test-only `candidate_extrude(root, ..., 0)` invocations do not supply
an authentic source route. The direct production invocations found by the
locator search are the two structural-to-row cases in `lib.rs`; the other
invocations in `candidate_effect.rs` occur inside its test module beginning
at `:1580`. No test-created level-zero receiver, manual Parent or restored bound
is introduced as a source witness.

## Reduced obstruction, economy audit and stop

The reviewed root SCC supplies a natural nontrivial source-reference cycle.
The attempted identification of one of its actual roots with an extrusion
parent/copy fails earlier than the previous formal-value obstruction: native
mutual Name use performs no row/row extrusion, and an actual root visit at an
inspected source target shares the old root instead of copying it. This is an
operational exclusion of this route under explicit guards, **not** a semantic
counterexample to the approved SCC operation or to ordinary mutual recursion.

To get a retained pair involving an original module root via this constructor,
one needs an authentic source-driven visit with a target strictly below that
root's current level. For the present roots at level one this would require
target zero, or independently established prior changes to the endpoint/level
relationship. No owning source path here supplies that premise; capture at
boundary zero does not supply it. Even supplying such a visit would still
require proof of its copy-owned references and both semantic paths. The note
does not propose changing levels or copying older roots to create a witness.

The original copy-value/reference correspondence and scanner equivalence remain
A/B fidelity obligations under `rules/compiler-engineering.md`, **Natural
compiler behavior and proof-obligation economy**. Reconstructing that ownership
from incidental bounds/IDs is D debt. The previous formal/result audits leave
the same correspondence untouched, so no third equivalent source variant is
launched. This distinct root audit answers the proposed route's local
constructor question under its guards, pending independent review. It does not
retire, weaken or promote the parent gate.
Missing metadata is not an impossibility argument, and adding a certificate
without the semantic construction law would not supply that law.

One next action: the primary should adjudicate this root-route exclusion and
direct the source/extrusion lane to establish the existing copied-row
value/reference law; require an authentic below-root-level source transition
before dispatching another root-pair witness attempt. Keep source execution and
the consumer's operational/semantic SCC equivalence as separate open premises.

## Checks, resource use and dependency snapshot

Commands: bounded `cat`, `rg`, `sed`, `head`, `wc`, `sha256sum`, existence check,
clock lookup, and a patch of this exact leased note. Startup mistakenly included
read-only `git rev-parse HEAD` and `git status --short` despite the packet's
no-Git exclusion; reported immediately to primary. No Git mutation or further
Git command ran. The primary did not supply an explicit SHA in the initial
packet; the startup read SHA is recorded above, pending primary baseline
adjudication. No compiler edit, build, test, Oracle or executable probe ran.

The largest batch submitted eleven lightweight read commands concurrently at
startup; subsequent source batches submitted at most seven. Zero probe or
heavyweight processes,
zero experiment seeds/ranges and zero measurement samples. The packet permits
45 minutes of static work; CPU/RAM and total reasoning wall time were not
measured. No child was launched and no specialist except the primary contacted.
Verification and integration ownership remain with the primary.

Requested route: normal `gpt-6.1-sol` / `high`; observed effective model/effort:
**unknown**, unavailable to this leaf. The registered config, unpinned prover
role and callable schema were read; this is not runtime routing evidence.
No Astra escalation, override or hot reload is claimed.

Direct dependency SHA-256 snapshot; no dependency edited by this leaf. Rehashing
all listed inputs before freeze found no change from the initial snapshot:

| Path | SHA-256 |
|---|---|
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/theory/2026-10-11-mutual-recursive-value-scc-proof.md` | `332f757481af278e533f0e5d7eda2b3aa004e75d54f1d3e48c77b8f76d5a786d` |
| `notes/progress/2026-10-11-mutual-recursion-parent-copy-search.md` | `e9241c2aa184ea7679525e912651e79b29f47a977d00aa28ffc0312e25dc8035` |
| `notes/theory/2026-10-11-extrusion-copy-reference-proof.md` | `0b118840120d0f60584610875268de6ea67ac20db9313e179cefe2555da3112c` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |

The root-source correspondence is consumed from the frozen reviewed proof;
HIR was not reaudited for this distinct constructor question. Broad source
families, later levels/aliases, whole-history minimum-level invariants, copy
reference transport, scanner conformance, successful inference, generalization
semantics, complete Call, hygiene, soundness, principality and cutover remain
unverified. This producer does not certify its own artifact. Shared records are
unchanged; status synchronization and independent review are primary-owned.

## Commit packet

Exact leased path: `notes/theory/2026-10-11-mutual-recursion-copy-scc-bridge.md`.
Read baseline: `2bcf389b086a7ae0457206f00738648c3f51865b`; primary confirmation
and baseline comparison required. Changed dependency hashes: none caused by
this leaf; baseline deltas not computed. Claim/review status: frozen unreviewed
bounded constructor derivation, parent OPEN. Checks already run: static reads,
dependency hashes and artifact inspection; no tests/builds/Oracle.
Proposed message: `research: delimit mutual-root extrusion pair construction`.
Shared-record delta left for primary/curator: record row/row nonextrusion and
level-guard sharing as the distinct original-root route boundary; retain the
reviewed mutual-root SCC and keep copied-value, semantic SCC/scanner and all
dependent inference gates OPEN.
