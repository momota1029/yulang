# Ordinary universal-use origin: attempted source discriminator

Date: 2026-10-06. Baseline: `bd441cc922e5bd244990f7c687fe42a245e04176`.
Method: static falsification attempt using the selected source acceptance set,
followed by a conditional variable-path derivation. No executable model.
Status: unreviewed bounded characterization; no source counterexample,
successor typing rule, policy selection, theorem closure or implementation
authority. Frozen on submission. Exclusive lease: this file.

## Objective, authority and direct dependencies

Find an accepted source that separates three possibilities: ordinary universal
scheme-use freshening introduces a §22 existential; it does not; or the
classification has no effect on the source's comparisons. The governing
sources are charter §§1–2,20,22–23; result-synthesis choice §4; approved
`function-call-view-formation/q1` answer `a2`; call-view design §§1–2,5; and
the expected schemes in the principal-scheme acceptance criteria. The previous
universal-scheme-use origin audit is a dependency and its historical `id(1)`
observation is retained without promotion to successor authority.

Charter §§1–2 withdraw the F5 closed-scheme machinery as the successor target.
Section 20 distinguishes universal operation-use instantiation, packaging an
existing witness, and elimination with fresh uniform-checking names. Section
22 guards existential introductions, including derived comparisons; §23
selects variable-only levels and leaves variable/extrusion coverage open.
Result-synthesis §4 preserves value/effect type polymorphism but defines no
universal scheme-elimination rule. The approved answer a2 and call-view §2
require preservation of shared source relationships through instantiation;
call-view §5 leaves the exact source judgments and preservation proofs open.
These selected meanings are inputs, not alternatives being reconsidered here.

## Smallest inspected acceptance witness does not expose a use

The selected ordinary identity criterion is exactly:

```text
my id x = x
  id : 'a -> 'a
```

Its body refers to its formal `x`; it contains no occurrence of the generalized
`id` scheme. Thus this particular criterion supplies no ordinary universal-use
fresh coordinate whose §22 classification could distinguish candidate rules.
Changing use classification alone, while preserving the definition judgment,
cannot be distinguished by this criterion. This is a statement about this
source's syntax and the scope of the criterion, not a theorem that all
implementations produce the same generalized scheme.

The other six displayed criteria have bodies applying or forwarding formal
`f`, `g`, or `x`, rather than using a named generalized `id`. They do not
explicitly require ordinary universal elimination of those formals. Treating
each formal occurrence as a fresh universal scheme use would add a missing
source rule. The approved internal provisional Handler view also supplies no
such rule. This inspection does not exclude a future general source judgment
that produces scheme uses there; it establishes no forced such judgment now.

The shortest useful *candidate extension* exposing a variable argument is:

```text
my id x = x
my pass y = id y
```

No assigned criterion explicitly selects a successor principal scheme or
completed acceptance derivation for `pass`. This is therefore neither an
accepted counterexample nor an Oracle experiment. It avoids relying on a
constructor level, but that does not fill its missing use judgment. Minimality
is only relative to this shape: deleting `id y` removes the named scheme use;
replacing `y` with a literal removes the explicit caller-variable endpoint.
No global source minimization or syntax acceptance check was performed.

## Exact conditional comparisons and the unresolved extrusion premise

Let `t` denote one fresh coordinate shared by the argument and result of a
candidate identity instance, `Y` the caller's value argument coordinate, and
`R` its result coordinate. A common structural *candidate value projection*
of a complete call comparison gives:

```text
Y <: t       t <: R
------------------ variable transitivity, if enabled for these endpoints
Y <: R
```

This display is conditional on a source call judgment that emits these two
comparisons through the complete role-indexed Function comparison. It is not
derived from the printed `'a -> 'a` alone and is not a standalone comparison
of effect ports. Even exact sharing of `t` is a candidate instance premise;
the selected preservation direction does not define its allocation judgment.

Now additionally assume `Intro22(t,l)` and source-derived levels for `Y,R`.
The direct comparison `Y <: t` is forbidden when `level(Y) <= l`; `t <: R`
is forbidden when `level(R) <= l`. If both levels exceed `l`, these two direct
comparisons alone supply no §22 distinction. The displayed derived `Y <: R`
has no `t` endpoint, so this display itself proves no fresh-origin guard
failure there. Any derived comparison that does contain the existential must
re-enter the guard. No constructor/head level is assigned.

Full classification irrelevance additionally requires all reachable replay,
alias, decomposition and extrusion paths to remain guard-neutral. The packet
does not supply the rule saying whether extrusion on this call creates or
relates `t` to a variable `Z` with `level(Z) <= l`, preserves an above-level
comparison, or rejects earlier. Hence even assigning hypothetical above-level
`Y,R` would not prove irrelevance for the complete call.

The exact conditional discriminator is:

1. A source judgment forces the shared coordinate `t` and the stated comparison
   path (including any extrusion-generated endpoints).
2. It classifies `t` as `Intro22(t,l)` and forces a comparison with a variable
   at level `<= l`.
3. §22 rejects that comparison. If every legal source derivation must take this
   path and no independent rule already rejects the source, the classification
   can distinguish acceptance from a candidate without this origin guard.

Without item 2, fresh allocation and mathematical solution projection
`exists t. C(t)` do not imply existential introduction. Without item 1 and the
forced-path clause in item 3, rejection of a proposed solver path does not
prove source rejection. Without complete path coverage, direct above-level
comparisons do not prove classification irrelevant. None of these missing
premises is supplied by the assigned clauses. This is a bounded premise-gap
characterization, not a conditional theorem about every source program.

## Independence, omissions and stop condition

The primary-selected criteria are an independent acceptance requirement from
the historical Oracle dump fixture, but neither supplies an independent
successor elimination oracle. This attempt shares the prior audit's selected
textual premises; it attacks the acceptance-set exposure and caller-variable
path instead of repeating the frozen `id(1)` observation. There is no checker
whose supplied transitions could be mistaken for proof of source transitions.
I did not author the prior audit and do not certify this note independently.

No source parser, compiler, tests, probes, seeds/ranges, mutations, automated
shrink, builds or performance samples were run. Unverified scope includes
`pass` syntax/acceptance, source-derived use allocation, its levels, complete
Function/effect comparison, every extrusion/replay path, alternative legal
derivations, public generalization and whole-language scheme elimination.
The historical `my id x = x; id(1)` evidence is only as reported in the pinned
prior audit; its frozen source files were not reinspected here.

The prior audit and this attempt leave the same source-origin premise open.
The sharper blocker is that the selected identity acceptance criterion has no
generalized use, while any added use needs both an independently defined
successor elimination judgment and its variable/extrusion path. Another toy
comparison model with assigned levels would leave this premise untouched.
Stop this attack rather than run that model. This is not a request to select
policy. The result needs delta review if an accepted governing source supplies
the missing judgment or any direct dependency changes.

## Commands, resources and dependency snapshot

Read-only commands: `cat` on the three required rules and assigned notes,
bounded `rg`/`sed` locators and section reads, `git rev-parse HEAD`, and a
Python SHA-256/byte-equality read using `git show <baseline>:<path>`. The initial
combined task/context capture was truncated; subsequent bounded reads located
the task and exact governing passages. No absence claim uses truncated output.
All ten direct dependencies matched pinned bytes at the snapshot below.
Output path was absent before creation. No Git mutation or other write occurred.

At most four read-command calls were batched; heavyweight process count zero.
CPU time, peak memory and total wall time were not instrumented. The assignment
specified small static reads and one output, with no numeric CPU/RAM/wall-time
limit; no numerical resource claim is made. This one prose file is the output.

SHA-256, all equal to live bytes at producer snapshot:

```text
ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd  rules/research-lab.md
9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29  rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e  rules/git-concurrency.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992  notes/design/2026-10-02-source-result-synthesis-choice.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1  notes/design/2026-10-05-inferred-function-call-views.md
13c6feb02727d8cc735dcb19843b337dee9126cd7afc519f3d18c6e1cdf95337  notes/progress/2026-10-04-principal-scheme-acceptance-criteria.md
8963987e193efe9c4778a457a163df0076391b4056734def0087164b4795e300  notes/progress/2026-10-06-universal-scheme-use-origin-audit.md
1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536  questions/2026-10-05-function-call-view-formation/approved-answer.md
6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0  questions/2026-10-05-function-call-view-formation/receipt.md
```

Recommended next action: primary should route the missing source elimination
judgment and its variable/extrusion derivation to the source-rule construction
lane, then return a frozen derivation for a discriminator; this lane has no
further independent acceptance oracle to probe.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-universal-use-origin-falsification-next.md`.
- Baseline: `bd441cc922e5bd244990f7c687fe42a245e04176`.
- Dependency hashes changed: none; ten direct fingerprints above.
- Claim/review: unreviewed bounded characterization and conditional path
  argument; frozen research-only artifact, independent review pending.
- Checks already run: exact governing passages and acceptance sources inspected;
  baseline SHA and ten dependency byte/hash comparisons. No executable checks.
- Proposed commit message: `research: bound universal-use origin source discriminator`.
- Shared-record deltas intentionally left for primary/curator: record that the
  selected identity criterion does not expose generalized use; link the missing
  source elimination and variable/extrusion prerequisites without choosing an
  origin classification, declaring a source counterexample or closing a gate.
