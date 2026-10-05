# Authority audit of recursive-name-return guard coverage

Date: 2026-10-06
Status: frozen research-only bounded textual derivation; unreviewed
Baseline: `41e5f4a1a03b472e7249d04611d57ba00b5eb448`
Exclusive lease: this file only
Method: exact reading of selected charter §§20, 22–23 against the paired O notes
Implementation authority: none

## Objective and result

Determine whether the selected clauses entail the falsification note's
candidate support-pair clause K. **They entail part of its discipline, but
do not entail its support-pair coverage rule.** Direct existential variable
comparisons receive the selected equal/older-level rejection, and every
actually derived comparison must re-enter the guard. Variable-only levels
and structural decomposition are selected. The additional inference from a
variable occurring inside an endpoint to a guard obligation against every
variable in the other endpoint is not specified by these clauses.

This is a bounded characterization of the inspected authority, not a
non-entailment theorem for a completed Yulang calculus. It does not establish
that the eventual source rule permits q3, that q3 escapes the selected guard,
or that K is inconsistent. Exact coverage remains a proof/representation
obligation. The assignment's designated PASS review of the two O notes is
primary-supplied provenance; their current headers still say unreviewed. This
audit neither independently certifies them nor promotes them to authority.

Accepted boundaries are retained: candidate RecGroup is not selected Yulang
source authority; no regular-tree carrier is selected; successful concrete
comparisons do not establish a transitive preorder; existential classification
of fresh R is not determined by its legacy category. No new user decision or
question bundle was consumed.

## Exact clauses and what they establish

The design index identifies the charter as a Reviewed research charter whose
selected amendments govern their scope. The following are user decisions
recorded in that charter, not authority inferred from its general status.

* §20, lines 549–556: “Elimination opens fresh rigid names `kappa` and checks
  one uniform arm under the declared interface and bounds with its captured
  environment fixed.” A caller-private equation is not an arm assumption.
  Lines 565–568 retain joint binder correspondence for dependent returned or
  stored roots and distinguish equality-kernel existential inference variables
  from hidden request binders. This specifies request introduction/elimination
  correspondence. It supplies no rule classifying a fresh recursive R row.
* §22, lines 605–610: “An existential introduced at level `l` rejects
  comparisons/unification with types at level `<= l` at generation/comparison
  time.” “Every derived comparison re-enters the same guard, including
  transitivity, aliases and bound replay, before committing a forbidden
  comparison or specialization.” Lines 612–614 explicitly require rejection
  of the eventually derived `kappa <: Int`; indirect propagation supplies no
  permission to narrow the existential.
* §22, lines 627–629: “Composite-type level definition, exact coverage of
  every comparison path, and preservation of this discipline remain
  proof/representation tasks. No definition, exception or completed full
  algorithm is selected here.”
* §23, lines 635–639: “Constructors and heads need no level metadata.
  Structural comparisons decompose through the ordinary rules; variable
  comparisons and extrusion then enforce the selected level discipline.”
  This supersedes the preceding head-level candidate. Lines 641–645 retain
  the guard on every derived comparison and explicitly leave “Exact
  variable/extrusion coverage” and preservation open.

§23 therefore narrows how the discipline is realized; it does not supply a
new constructor level or silently discharge §22's coverage task. The explicit
ground-narrowing example also prevents an inference that a constructor with
empty variable support automatically has no existential guard obligation.

## Four distinct steps in the proposed discriminator

Let `Ex(v,l)` mean that a source derivation has classified v as an existential
introduced at l. Let `V(t)` be the syntactic variable support used by K.
These are candidate proof notation, not new selected IR fields.

| Step | Selected consequence | Additional premise needed for K |
|---|---|---|
| Variable comparison | If an actual comparison directly relates `Ex(z,1)` and a level-one variable c, §22 rejects its equal-level specialization; above-level propagation is allowed by this guard component. | A source-derived `Ex(z,1)` certificate; passing this guard is not full subtype acceptance. |
| Structural decomposition | Ordinary structural rules and variable/extrusion enforcement apply without constructor levels (§23). | The rules for a constructor endpoint against a variable endpoint, including what extrusion examines or emits. |
| Support/occurrence lookup | An existential's source introduction and scope remain relevant. | A rule that every `(a,b) ∈ V(s) × V(t)` induces the stated permission test, including nested positions and repeated identity. |
| Derived comparison/replay | Every comparison actually generated by decomposition, propagation, aliases or bound replay re-enters the same guard. | A derivation showing that a particular support pair is a guard obligation or generated comparison in the first place. |

The falsification note's exact K tests the Cartesian product of the two
endpoint supports. It tests the peer variable's level whenever either member
is Ex; it assigns no constructor level. Guard inspection is explicitly not a
generated subtype edge. Consequently its table does not derive `z <: c`.
The phrase “an existential appearing anywhere triggers §22” is only a
paraphrase of this candidate coverage idea. It must not replace K's actual
cross-product formula, which creates no pair when the other support is empty.

Neither an occurrence inside a constructor nor its membership in V(t) is a
source existential introduction. Conversely, knowing that z was introduced
as Ex does not specify all the guard obligations arising from its structural
occurrences. Those are separate missing premises. Levels, fresh identity,
R storage, and mathematical existential valuation witnesses cannot replace
either premise.

## Conditional derivation and smallest distinguishing pair

Reuse the paired notes' completed incoming history for the smallest alias:

```text
my f x = g
my g y = f
my h = f

B(z) = P0(Top-, P0(Top-, z+))
q1: B(z) <: z
q2: z    <: Top-
q3: B(z) <: c
q4: B(z) <: r    (replay through the collected c <= r edge)
```

This inventory is inherited evidence, not independently reconstructed here.
All z, c, r have current level one. Conditional on `Ex(z,1)` and ordinary
c/r, K rejects q1, q3 and q4; q2 has no support pair. Conditional on no Ex
classification in this inventory, K's guard component is vacuous. These are
consequences of K and the decorations, not consequences of the source
clauses alone. The execution with Ex stops at q1; later table entries are
judgments of attempted shapes, not subsequent execution events.

The smallest distinct-variable distinguishing pair **within this audited
history** is q3: `B(z) <: c`, with `Ex(z,1)` and `level(c)=1`. Its lower
endpoint contains z, while its upper endpoint is c. It has no pair of
matching outer constructor heads to decompose. The exact missing implication
is:

```text
Ex(z,1), z occurs inside B(z), level(c)=1,
attempted comparison B(z) <: c
   ==> a permission obligation comparing z's introduction level with c's level
```

K supplies that implication. §§20, 22–23 do not provide its inference rule
or a derivation via variable/extrusion rules. They require the final coverage
proof to respect the discipline; they do not select Cartesian support as the
proof's premise. If an independently supplied ordinary-rule derivation emits
an actual forbidden z/c comparison, §22 already determines its rejection.
This conditional fact does not establish that such a comparison is emitted.

Two distinct variables are necessary for this distinct-variable test.
Symbolically `C(z) <: c` with one unary constructor is the smaller generic
occurrence test, but it is outside the recorded production inventory; no
source generation or acceptance claim is made for it. B's two P0 heads are
kept in the actual q3 witness. q1 is a smaller one-variable support test, but
its `(z,z)` obligation additionally depends on K's nested/self-pair coverage;
it is not the selected direct variable comparison `z <: z`.

No accepted reflexive exemption is inferred. Removing q4 leaves q3's missing
implication unchanged; removing the alias removes that caller pair. Changing
z's classification to ordinary removes this K obligation; changing c's level
above one changes its K outcome but abandons the audited level inventory.
Removing K leaves the structural coverage question unresolved. These are
symbolic sensitivity observations, not executed mutations.

## Independence, omissions and stopping condition

There is no checker or executable oracle. The clauses supply the selected
discipline; the paired O notes supply a common candidate support rule and
inherited comparison inventory. This audit independently reads the textual
scope of those clauses, but shares the paired notes' trace assumptions and
does not independently review their production derivation. A checker taking
Ex labels and K as inputs could check the conditional table only. It would
not prove either source classification or structural coverage.

No enumeration, seeds/ranges, tests, builds, probes, executable mutations,
formatters, compiler changes, or Git mutations were performed. Coverage is
the exact selected sections, the two designated O notes, and their four
attempted comparison shapes. Complete source typing, actual variable/extrusion
rules, ground comparison coverage, general Function variance, effects,
request-arm elimination, alias publication, preservation, principality and
full A/(L) remain unverified. No exhaustive search for another governing
specification is claimed; the assignment fixes the sections to audit.

This reading does not authorize a guard bypass or a semantic alternative.
The paired notes' origin gap and this coverage gap must remain separate. A
third model assuming the same K would leave the premise untouched. Recommended
next action: primary locate or derive the ordinary variable/extrusion rule
for q3 and show exactly which existential permission obligation it creates,
before another support-based experiment. No user decision is proposed here.

## Checks and frozen dependency snapshot

Read-only checks: `cat` of the required rules and designated O notes;
`rg` of the exact index/section locators; pinned `git show` of the charter;
`git rev-parse HEAD`; `git diff <baseline> --` the charter, index and three
rules; bounded numbered section reads; SHA-256 snapshots; target absence
check; one leased-note patch followed by text/dependency integrity reads.
HEAD matched the supplied baseline at the initial check. The tracked source
diff was empty. Both O-note `git show` attempts exited 128 because those files
are not in the baseline commit: they are explicitly designated frozen
working-tree research dependencies, not baseline-committed authority.

Some initial combined read output was truncated; the used clauses, rules and
O notes were read in subsequent bounded captures. No computation search is
running. At most four lightweight shell reads were requested concurrently;
zero build/test/probe processes or children. CPU, peak RSS and exact total
wall time were not instrumented. No numerical compute cap was supplied; the
static-only, one-output scope was enforced.

| Direct dependency | SHA-256 |
|---|---|
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/progress/2026-10-06-rec-name-return-o-classification-constructive-attempt.md` | `458794363c781bfbe0c9879a26573f36ff903ffa6303994528a81c49089ba65c` |
| `notes/progress/2026-10-06-rec-name-return-o-classification-falsification-attempt.md` | `8514ca2ed9cac0c0dc0261c1d91afa0881ea0de07dd20b5f03f8e54150dfff2f` |

Operating dependencies: research-lab
`ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd`;
design-authority `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29`;
git-concurrency `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e`;
design index locator `d56f970490ec9e4699f55c47d1e037bbcfab00592b054c9b138d517b208ab9f0`.
The primary must revalidate these hashes before integration if dependencies move.

## Commit packet

* Exact leased path: `notes/progress/2026-10-06-rec-name-return-guard-coverage-authority-audit.md`.
* Baseline SHA: `41e5f4a1a03b472e7249d04611d57ba00b5eb448`.
* Changed dependency hashes: none during this lane; the two O notes have no
  baseline blob and are pinned by the current hashes above.
* Review status: frozen unreviewed research-only authority characterization;
  no independent certification, new source rule, or implementation authority.
* Checks already run: exact clauses and paired-note reads, initial HEAD
  equality, tracked dependency diff, SHA-256 and leased-note integrity reads.
  No tests/builds/probes.
* Proposed one-line research-checkpoint commit message:
  `research: isolate support-pair guard coverage in selected charter clauses`.
* Shared-record deltas intentionally left for primary/curator: retain K as a
  hypothetical occurrence-coverage clause; record the q3 variable/extrusion
  derivation as separate from fresh-R origin classification; retain selected
  guard re-entry and variable-only levels as settled decisions. No shared
  task/index/authority/theory or question-board path was modified.

Writing stops at submission for frozen review.
