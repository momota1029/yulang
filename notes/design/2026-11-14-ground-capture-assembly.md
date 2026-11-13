# Ground capture assembly after full-report readback

Status: partial proof companion, 2026-11-14. Continues
[ground capture readback](2026-11-14-ground-capture-readback.md).
Authority remains `spec/06-roles.md` §6 and the approved B4 statement.
All existing relations and integrated definitions are unchanged.

**Result:** finite readback now covers every observed capture of the actual
original inherited report, including a missing origin descending through
structural bounds before nominal endpoint fallback. Every needed binder has
one shared, normalized, minimum-mass Pattern label. Normalized-template
Paterson descent is proved from the existing conservative checker. The new
ground-root Acc reduction needs only `NormalizedCaptureAssembly`, defined
below; that assembly is still open.

**Not established:** unconditional ground-root Class P Acc for arbitrary
Checked registries, the original `ReachableCaptureFactorization`, or the
full unknown-hole `ClassPProducer`. The previous closed Show example remains
unchanged. No infinite execution or semantic gap was found.

## 1. A raw-normalization proof obstruction and its additive repair

The desired general substitution commutation statement is false:

    covered(normalize p) = true
      does not imply normalize(p[sigma]) = normalize((normalize p)[sigma]).

Here is a closed counter-computation in `GeneralPatternHiddenJoin`. Write
`R_l(a,t)` for a record field, `V_k(a)` for a variant, and `e` for a nullary
application. Take distinct variables x,y and define

    A = V_7(x) | V_7(y)
    B = V_7(x | y)
    p = R_3(e, R_3(A,e) | R_3(B,e)).

Both A and B normalize to `V_7(x | y)`. Consequently the two record tails
merge by equality, and hiding removes their common field. Thus p normalizes
to `R_3(e,e)`, which is covered. Substitute

    sigma(x) = V_8(app_0()), sigma(y) = V_8(app_1()).

Normalization of A's substituted row groups the payloads but leaves their
new join inside the payload. B's explicit payload is recursively normalized
and groups the inner variants. The results differ. The two substituted record
tails therefore remain joined, and hiding cannot cross that join. Lean proves
the failed equality and measures the simultaneous heads `[p,x,y]`: raw-first
substitution has mass 22; substitution into the normal form has mass 7.

This is a **proof-interface implementation gap**, not a semantic gap or a
Step counterexecution. The old local theorem requiring raw coverage remains
valid. The example does not formally refute the existential raw factorization
contract: it refutes the proposed commutation lemma and its intended transport
for these captures. No owner decision or additional runtime guard is needed.

The emitter already consumes normalized input templates. The additive
`GeneralNominalNormalizedGround` reduction now uses labels

    substArgs capture (normalizeArgs clause.arguments)

and the corresponding normalized head. It does not rewrite the registry,
the original declarations, or Step.

## 2. The checker's normalized descent, including records

`GeneralPatternConservativeSubstitution.substitution_bounds` proves, for
every covered raw Pattern q and **every** Pattern substitution sigma, the
following sandwich. Let tau(x) encode `normalize(sigma(x))`:

    size(subst tau (lower q))
       <= size(encode(normalize(q[sigma])))
       <= size(subst tau (encode q)).

Its list version sums the inequalities. At a variable the three expressions
coincide. Applications and variants preserve the bounds by addition. In a
record, `hide_size` supplies the upper bound. The conservative lower count
discards the tail and substitutes a size-one empty node; every remaining
normalized tail has positive size, supplying the lower bound. Captures need
not be covered, closed, or already normalized.

For a checked where-clause, both normalized templates are covered. Apply the
ordinary Roles substitution theorem to `checked.conservative`, then use the
sandwich on its two sides:

    mass(subst sigma (normalizeArgs child))
      <= size(subst tau (encodeArgs(normalizeArgs child)))
       < size(subst tau (lowerArgs(normalizeArgs head)))
      <= mass(subst sigma (normalizeArgs head)).

This is `checked_normalized_descent`. It uses no raw-normalization
commutation and no new declaration check. It includes hidden record tails
and any raw joins erased by the initial normalization.

The existing input-request producer normalizes a stored normalized template
again. This second normalization must be accounted for in child assembly;
global idempotence of the normalizer on arbitrary Patterns is not assumed.
The existing covered-template substitution theorem is available at that
boundary because Checked provides coverage of the first normal form.

## 3. Inverting finite meanings along the actual full report

`GeneralNominalFiniteHeadInversion.test_equal` proves that equivalent finite
constructor meanings with canonical signatures have the same Test. A role
probe with a singleton permitted head separates scalar, nominal identity and
arity, pair, variant tag, and record families. Record field probes recover
the label set; canonical sorting recovers the actual label list. A required
field distinguishes nonempty records from exact-empty. An optional impossible
payload distinguishes the empty record from exact-empty. Payloads themselves
may be arbitrary regular carrier values.

`GeneralNominalCanonicalPaths.Path` records arbitrary nominal argument edges
and canonical structural argument edges, independently of a finite tree.
`observed_follows` combines such a path, an actual endpoint observation, and
the root's closed finite meaning to construct a genuine `Follows` path in
that finite tree. Nominal inversion uses the carrier's invariant arguments;
structural inversion uses the preceding Test equality. The existing
source-preserving reification theorem then supplies an original Pattern part,
a closed endpoint meaning, and a nonincreasing existing checker mass.

`GeneralNominalReportPaths.inspect_rooted` and `many_rooted` extract these
paths from the real recursive inspector when its root origin is retained.
They cover all query constructors and both nominal endpoint reports.
Structural canonicality comes from the matched snapshot shape, rather than
from a new assumption about the declaration or a guessed projection.

The missing-origin case requires more than this rooted-path lemma. In
`GeneralNominalFallbackReadback`, `Endpoints` keeps an independent exact
finite meaning for each source endpoint. `source_child` combines the existing
`actual_structural_readback` with finite path inversion: a structural child
slot has the corresponding finite readback with no larger mass. Thus an
absent origin can descend through any number of matched structural nodes
while preserving both endpoint certificates. Once a nominal node creates a
fallback origin, `many_rooted` applies from its chosen lower or upper source
endpoint. These endpoints are never identified by overlapping bounds, and
no interval interior is selected.

`missing_supported` proves this for the full recursive inspector by mutual
induction with its list inspector. Missing variable captures have no actual
origin and cannot satisfy the observed-capture premise. Deferred or failed
branches contribute no such captures. `inspect_supported` combines the
retained and missing cases.

Finally, `GeneralNominalPacketCaptureReadback.packet_capture` connects this
to a real packet. `many_capture` locates its original report component;
`locate_sources` proves the bounds' source identities are the actual demand
arguments. Retained roots use `Inputs`. Missing constructor roots use the
existing `Safe` recovery/count argument, which proves endpoint equality;
containment then gives exact finite meanings for both endpoints. The current
state model justifies structural slot transport. `usable_closed` gets the
capture's observation existence from `Usable` and `packet.Holds`.

The conclusion is an individual closed capture readback with mass bounded
by the total input-label mass. It holds for arbitrary role arities, compound
heads, nested records/variants/nominals, and later strict materialized bounds.
No ancestry-depth bound, trace budget, or signature cover is a premise.
It does not yet bound the sum of all head occurrences.

## 4. Simultaneous shared labels and the exact remaining obligation

`GeneralNominalSimultaneousCaptures.simultaneous` constructs one substitution
for all needed names. `usable_same` transports each selected finite meaning
to every usable occurrence of that name. Closed reification normalizes the
Pattern while preserving its meaning and checker mass. A well-founded
minimum over natural-number masses chooses a least-size shared closed label.

This minimum matters: different source Patterns can denote equivalent
values. Choosing an arbitrary witness of bounded total mass is insufficient
for a per-position head budget. The theorem proves that the chosen label's
mass is at most **any** closed label read back at any usable occurrence.
It does not need uniqueness of source constructor keys or a semantic-tree
reification that invents catalogue names.

Names absent from all normalized child inputs receive `.var name`, of size
one. The theorem and the new `Ready` predicate explicitly retain this fact.
Independent review caught that merely requiring normality for these unused
names would permit arbitrarily large irrelevant substitutions and make the
universal assembly obligation false. The corrected interface preserves the
actual construction's defaults.

The minimization ranges over all representable closed Pattern meanings in
the fixed context, not just literal parts of the input source syntax. Its
selected label need not preserve an original constructor key. The earlier
path readback does preserve that key and supplies an eligible witness; the
minimum keeps the finite meaning and the per-occurrence mass bounds. No
catalogue inverse or global catalogue finiteness is assumed.

`GeneralNominalCaptureAssembly.ready_captures` derives `Ready` from the actual
`Installable`, `PacketGuard`, current model, packet model, and finite `Inputs`.
The sole remaining premise of `ground_accessible_of_assembly` is
`NormalizedCaptureAssembly`. It quantifies over reachable states, installing
guarded packets with children, their models and finite input labels, and a
`Ready` substitution. It must prove:

1. The **whole** normalized instantiated head has mass at most the sum of the
   input-label masses. This requires preserving constructor positions and
   multiplicities through flattening/sorting canonical records and through
   both original nominal endpoint reports. Individual-capture bounds cannot
   simply be summed against the total input mass.
2. Each normalized substituted child argument has a closed finite term of
   the declared arity and the existing `ArgumentValue` evidence for the
   actual emitter. This includes translation/substitution, record-tail
   hiding, variant normalization, the emitter's second normalization, and
   connecting needed binder labels to its input-only capture evidence.

Those two conclusions remain unproved. The new Ready construction discharges
the prior full-report readback and shared-label selection obligations; it is
not a proof of the assembly that consumes them.

## 5. Strongest accessibility statement and scope

The proved chain is

    Checked + InitialSource + PointSource + GroundRoots + NormalizedCaptureAssembly
      -> NormalizedCaptureFactorization
      -> NormalizedProduction
      -> InstalledDepthBound (mass rootLabels)
      -> Acc actual-inspection Step (initial context root).

The existing retrospective-model ancestry proof is used with the new
normalized descent: `depth + mass(site labels) <= mass(root labels)`.
Administrative actions and merges use the unchanged model restriction and
site-preservation facts. Existing finite invocation/allocation/report and
signature-cover theorems finish the conditional Acc proof. No global model
of an infinite trace is assumed.

Associated outputs and output-only binders are unrestricted in this
conditional statement. The capture readback proof itself does not inspect
their settlement trees: it starts from the finite input invariant at each
installation. Proving preservation of that invariant still needs child
assembly. No unconditional new subclass is claimed in this turn.

Roots with unknown holes remain outside this result. Their genuine
elimination simulation was not started: the ground-root assembly must first
close. The local path/fallback theorems already allow strict dynamic bounds,
but this does not extend the source initialization theorem to strict-interval
sources.

## 6. Review and validation

The primary constructed these bounded proofs. The registered prover role is
unavailable: the checkout lacks `rules/agent-orchestration.md`,
`rules/research-lab.md`, `rules/design-authority.md`, `.codex/config.toml`, and
`.codex/agents/prover.toml`; the live schema has no prover role. No prover
agent ran. A separate read-only reviewer checked the normalization example,
conservative sandwich, finite inversion, original-report fallback transport,
and accessibility quantifiers. The unused-variable interface correction
described above came from that review.

Validation commands and their final results are recorded after the checks.

Final commands from `lean/`:

| Command | Exit code |
| --- | --- |
| `lake build Yulang.GeneralNominalCaptureAssembly Yulang.GeneralPatternHiddenJoin` | 0 |
| `lake build Yulang > /tmp/yulang-ground-assembly-build.log 2>&1` | 0 |
| `lake env lean Audit/GeneralNominalCaptureAssembly.lean > /tmp/yulang-ground-assembly-audit.log 2>&1` | 0 |

The focused entrypoints build all ten new modules (756 jobs). The full build
completed 2244 jobs. All 28 audited declarations use only `propext`,
`Classical.choice`, `Quot.sound`, or fewer. Intermediate elaboration failures
were corrected before these checks. No parser or executable program fixture
was added; the hidden-join example is a kernel-checked Pattern computation.

From the repository root, `git diff --check` and
`python3 /tmp/yulang-ground-assembly-scope.py` exited 0. The scope checker
verifies byte-for-byte preservation of old file prefixes, exactly ten new
module imports, the new audit/note, the prohibited-token scan, and unchanged
branch/HEAD. The only modified existing files are `lean/Yulang.lean` and
`notes/design/INDEX.md`, with appended lines only. Earlier Lean modules and
all frozen paths are untouched. Branch remains `astra/ground-factorization-3`
at `898526b04164829e196293fee0128e756d41e208`; no commits or ref updates
were made.
