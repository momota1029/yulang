# Qualified intrusion: publication constructor falsification

Status: frozen, unreviewed research checkpoint. Conditional candidate-code
derivation and bounded source-correspondence obstruction; no source rejection,
semantic counterexample, theorem closure or implementation authority.
Baseline: `5cb4ba6f9cc8fa65d347c3b53b6d4e6e5196d02f`.
Final HEAD recheck: `bc60eeb63ff9ddcc8a2815149a5b6486ede36af6`.
The witness review/correction was committed during this lane. Its frozen
read bytes below match that HEAD, rather than the pinned baseline; the delta
corrects First's ownership of `g 0` and records bounded review/revalidation.
The accepted final F-to-G reference and this construction remain intact.
All twelve repository source/semantic dependencies below match both revisions.
Branch: `research/simple-sub-intrusion`.
Lease: this file only; source reads, no tests/builds/probes or Git mutations.

## Objective, authority and scope

Test the publication premises of the ordinary-form
[two-use candidate](2026-10-12-intrusion-admitted-two-use-witness.md), preserving
the approved event `e=(G,F)` and its pairs `(C,B,+,2),(D,R,-,2)`.
The constructive theorem belongs to the primary's prover lane. This separate
lane checks actual constructors, equality and freshening; it does not select
an ownership interpretation or repeat an abstract model search.

Governing sections: [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5; [parent-copy operation](../design/2026-10-10-parent-copy-scc-intrusion.md),
Selected operation, Value-reference SCC clarification and Definition-root
Value ownership; [occurrence qualification](../design/2026-10-12-intrusion-value-type-association.md),
Approved extrusion-event qualification and Implementation/proof boundary;
[Source Generalize](../design/2026-10-08-source-generalize-definition.md) §§2–3
selecting its [construction](../theory/2026-10-08-source-generalize-definition-and-proof.md)
§§3–5, particularly §3.3, §5.1 rules 2–5 and §5.2's whole-frame allocation.
The rules research-lab, design-authority, git-concurrency, agent-orchestration
and orchestration-budget and the yulang-proofs skill were read.

The source under inspection remains:

```yulang
my answer = {
  my f x = {
    my g y = { my drop z = y; drop (f y) };
    my first: int = g 0;
    g ()
  };
  f
}
```

Q is answer's enclosing definition identity; F and G are the actual f/g
Value roots. First owns `g 0`; F owns the final `g ()`. The accepted source
graph has `F -> G -> F`. Neither Q nor a Function port replaces G.

## Discriminating construction: equality prevents independent B freshening

**Conditional candidate-code claim.** Assume this candidate construction has
actually created B at level 3 and C at level 2, g is installed with boundary
2, and the existing successful merge operation realizes the approved C=B
before both g uses. Assume the merged row is reachable from each captured g
interface, no intervening representative mutation undoes equality, and both
uses complete normally. Then both fresh-use maps reuse the same canonical B/C
row. They cannot allocate independent B0 and B1 for that row.

Derivation from the real owners:

1. `candidate_source.rs:270–328` keeps Lambda bodies at their current level;
   each Block initializer raises it once and installs at the Block level.
   Thus the supplied layout is f at 2, g at 3, with g publication boundary 2.
2. `candidate_extrusion.rs:90–122` copies a younger row at its target level,
   calls `retain_extrusion_parent`, memoizes that polar copy, and inserts the
   directed source link. For the supplied positive pair, C is the level-2
   copy and B the level-3 parent.
3. `candidate_intrusion.rs:513–606::merge_candidate_rows(C,B,...)` redirects
   C to B and sets B's level to `min(3,2)=2`. It ORs their non_generic flags.
   There is one canonical representative, regardless of the printed name.
4. `candidate_scheme.rs:303–334::Capture::row` canonicalizes the key first.
   Its local test is `level > boundary && !non_generic`. For that B/C
   representative, `2 > 2` is false. `expand_row:567–573` stops at such an
   older identity, leaving its mutable bounds in the live session.
5. Installation `:1320–1340` stores g's root and boundary. Each later Name
   `:1354–1380` separately captures and prepares a use. The fresh-use map
   `:981–1025` is operation local, so fresh eligible rows are independent
   across calls. But its fallback for this non-local B/C row is the original
   canonical source, in both maps. A new use identity does not freshen it.

This is the first discriminating publication construction: **in the existing
candidate mechanism, applying equality before capture makes B shared along
with C**. The earlier sufficient hypothesis “C fixed while B is a template”
cannot describe that particular successful merge/capture path. The two-use
fixed-anchor obstruction could still arise through a shared B; this note
does not claim its disappearance or that the source requires this path.
Equality timing after a completed first fresh frame needs a separate trace;
the assumptions above deliberately do not cover it.

Source Generalize classifies source records by their actual validating
component, declaration scope and typed dependencies. Its fixed walk does not
read a solver level or min-merge flag. Thus the derivation establishes a
candidate freshening consequence only. It cannot prove that the source's B
or C must be fixed, that its complete component relation is retained, or that
the candidate accepts/rejects this whole source.

## Event association and original Simple-sub prefix

`candidate_source.rs:394–411` constructs the nested f-y Apply input with
`owner=source.definition_root()`, hence Q for this carrier. It also retains
expression/callee/argument indexes, level, checking occurrence and operands.
`candidate_call.rs:30–59` retains that input and a native four-port demand.
Q is useful carrier ownership; substituting it for the approved origin G
would be an incorrect association. These fields do not by themselves forbid
a constructor from recovering the actual nested binding from the carrier.

`candidate_extrude` accepts endpoint/polarity/target, with one local polar
memo; `retain_extrusion_parent` stores copy, parent, polarity and target in
`Parent` (`candidate_intrusion.rs:23–28,171–219`). The pairs are retained;
the common source event with G/F endpoints is not retained in these outputs.
`settle_candidate_intrusion:375–486` constructs adjacency from solver bounds,
Function ports and effect tails, then compares type-copy/type-parent
components. It does not consume the approved Value-reference SCC or event.
This establishes a concrete constructor/consumer gap, not impossibility.

The [original-source derivation](../theory/2026-10-12-intrusion-occurrence-source-proof.md)
was checked against actual `Typer.scala:48–72,115–156,200–233` at original
Simple-sub `9bae772624c23b52a93c1b226157e16898b4d9db`:
monomorphic f lookup returns o, App creates `Function(B,R)`, the level crossing
extrudes it negatively, argument polarity reverses, and the actual polar
memo entries create C and D. At the candidate's shifted levels the same
prefix gives `B <: C`, `D <: R`, `o <: Function(C,D)`, at target 2. This
shifted prefix is conditional on the supplied source-to-native projection;
it is not an executed Scala/Yulang judgment of the full Unit/annotation
program. Original freshenAbove preserves boundary-level C/D and freshens
younger variables using a new memo; original Scala has no intrusion merge
or Value event certificate. It cannot independently certify the extension.

## Packet falsifiers and remaining premises

| Falsifier | Bounded result |
| --- | --- |
| Q incorrectly replaces G | Actual Apply owner is Q; treating it as the event origin would contradict selected G. No approved G/F event consumer exists in the inspected path. |
| Level/min-merge determines source classification | Refuted as a source derivation: these are candidate freshness predicates; selected classification requires §3.3 records and §5.1 typed dependencies. |
| C is accidentally freshened independently | Excluded on the successful pre-capture merge path above. Its canonical B/C identity is shared across distinct use maps. This does not establish lawful source fixed incidence. |
| Only merged-owner replay suffices for live third owner j | `merge_candidate_rows:601–605` enumerates the merged parent's lower/opposite products. `candidate_replay_bound:763–807` canonicalizes operands at that owner. It does not enumerate every third owner. `candidate_context_canonicalize_bounds:3125–3145` transports recorded third-owner bound provenance but performs no lower×upper replay there. Sufficiency still requires a separately established saturation/activation invariant at j; no reachable missed-comparison bug is claimed. |
| Actual event/pairs disappear | Pair provenance survives in Parent; event grouping and actual G/F endpoints are absent at the inspected producer and consumer seam. Missing fields do not refute realizability. |

The first missing original-source input remains the authentic innermost `f y`
Call, including actual recursive-f introduction/whole argument/entry/return
premises. After that, C's source realization and the equality's scoped
incidence must come from the actual demand/extrusion owners, so Build and
the fixed walk have operands to consume. Neither numeric levels nor pair
retention supplies those source declarations. No inspected rule rejected this
source. No claim about original acceptance, preservation, principality or
F5 cutover follows from this bounded trace.

## Verification, resources and freeze

Commands: bounded cat/sed/rg source reads, read-only Git HEAD/branch/status,
SHA-256 snapshots, baseline blob equality, and leased-note link/whitespace
inspection. No test, build, parser, executable probe, mutation, seed/range
enumeration or performance sample. Coverage is one candidate and its named
constructors; broader solver schedules and production source admission are
unverified. No independent executable oracle was used. The Scala source
independently supplies the original prefix, but shares the supplied native
projection with the witness and has no selected intrusion extension.

Local processes were lightweight and sequential, apart from independent read
commands. Peak CPU/RSS and exact reasoning wall time were not measured.
Assignment: researcher leaf; no children. No model override was requested in
the packet. Repository subagent defaults request gpt-6.1-sol/high, while actual
runtime model/effort metadata is unavailable and therefore unknown. Configuration
does not establish runtime execution settings. Independent review is pending.

Direct frozen dependencies (SHA-256; none changed by this producer):

```text
653861f60a148cbb1fcddf71b6426f58124f7fe9fbe353be2e2b8ea2ed86d768 notes/progress/2026-10-12-intrusion-admitted-two-use-witness.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
0063b88d17104f85182439d80360e42f8f99a5af4793eab70640a66f955ede25 notes/design/2026-10-12-intrusion-value-type-association.md
6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b notes/design/2026-10-10-parent-copy-scc-intrusion.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
81b483af26641f6ae39eeef9d10051e7691435d95e352882907f8571dba3cabe notes/theory/2026-10-12-intrusion-occurrence-source-proof.md
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49 crates/yu-solver/src/candidate_source.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35 crates/yu-solver/src/candidate_call.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0 crates/yu-solver/src/candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0 crates/yu-solver/src/candidate_intrusion.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1 crates/yu-solver/src/candidate_scheme.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987 crates/yu-solver/src/candidate_context.rs
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9 /home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala
```

Recommended next action: the constructive lane should supply the authentic
f-y Call and its source-owned C/equality incidence, then compare that incidence
to the canonical merged-row publication path above. Do not infer source
fixedness from the candidate's level merge.

## Commit packet

- Exact lease: `notes/progress/2026-10-12-qualified-intrusion-publication-falsification.md`.
- Baseline SHA: `5cb4ba6f9cc8fa65d347c3b53b6d4e6e5196d02f`.
- Dependency changes: none by this producer. The witness changed between
  baseline and final HEAD as described above; its current frozen hash is
  recorded: `1084618662cf885991f83e3d41a901d0d429531bb742a1c0c2f91b8a998ec0ef`
  to `653861f60a148cbb1fcddf71b6426f58124f7fe9fbe353be2e2b8ea2ed86d768`.
  All source/semantic hashes remain baseline-identical.
- Review status: frozen, unreviewed conditional construction/source audit;
  no independent certification and parent proof/implementation gates OPEN.
- Checks already run: static constructor trace, baseline/hash checks, local
  links and whitespace; zero builds/tests/probes.
- Proposed message: `research: distinguish intrusion merge from lawful publication incidence`.
- Shared-record deltas left for primary/curator: record the pre-capture merge
  consequence separately from source fixed/template classification; retain
  authentic f-y Call and C/equality realization as OPEN producer premises.
  No shared task/index/theory/authority or question file changed.

Writes stop at frozen handoff.
