# Dot selection: constructive evidence-to-execution bridge

Status: **CANDIDATE PAPER DERIVATION; INDEPENDENT REVIEW PENDING.**
Author: current primary alone. No subagents, independent reviewers or proof
assistant ran. This is research preservation, not theorem-gate certification,
production conformance, a new Authoritative language rule or compiler approval.

## Original obligation and result

The user asked to extend the inference-independent operational safety work
through dot selection, and to close the proof as thoroughly as possible before
implementation. The previous operational manuscript required an already
selected, typed member/dictionary/field plan. This continuation supplies a
constructive declarative bridge from finite declaration, selection, direct
boundary and role evidence to a refined typed plan.

The new manuscript is `docs/yulang-dot-selection-safety-ja.tex`.
Theorem 10.2 constructs the typed elaboration; Theorem 10.3 applies operational
safety to it. The construction covers ordinary/reference/effect methods, role
member acquisition and field fallback, including their occurrence-specific
boundaries and whole Call effects. It does not take the complete selected
plan's typing, inference success, or a semantic safety oracle as a premise.
Individual body derivations and ordinary finite evidence remain the usual
premises of the declarative typing judgment.

The previous manuscript's dictionary-application prose did not fully specify
an internal grammar for constrained polymorphic member fields. This was a real
completion seam found during self-audit. The new manuscript explicitly defines
an administrative code abstraction/application (`eabs`/`eapp`), with a general
code sort and a syntactically restricted pure retrieval sort. The general sort
retains adapter effects. Application creates no source receiver, owner or
grant; its decorated execution uses the existing View effect/result transport
so latent protection is observed. The proof extends substitution, canonical
forms, one-step preservation and progress. No new evaluation-frame kind is
introduced. The old calculus and original user TeX remain byte-identical.
The final safety result depends on that explicit conservative completion and
on the earlier unreviewed operational proof, rather than pretending that the
old value grammar already contained these forms.

## Proof components and self-audit

- Direct-boundary evidence retains its occurrence, current record view,
  immediate/latent contract and structural code. Record nontransitivity is
  exhibited; composing two adapters cannot discharge a third direct query.
- Whole scheme instantiation uses one map across receiver, other arguments,
  associated types, ordinary conditions, role prerequisites, effects, profiles
  and capture support. No fabricated receiver-only role demand is introduced.
- Impl conformance is a finite derivation under rigid head/member binders.
  Explicit associated definitions stay fixed; omitted definitions are one
  candidate-wide template. Local existential substitutions cannot solve the
  head binders. Every loaded declaration, including unused impls, is checked.
- Role evidence has Hyp/Impl/Assoc constructors and a finite child-first DAG.
  Declaration headers and role proof trees are distinguished from recursive
  member bodies. Missing prerequisites and circular role evidence cannot be
  silently accepted. Qualified assumptions require one consistent realization.
- Snapshot lookup is made finite and explicit: ordered first-success scans,
  local/global uniqueness, upper-only handling, effect path collection,
  reference payload/common-variable probing and the precise current Ready
  query. This proves local replay on a supplied snapshot, not watcher/driver
  lifecycle correctness or future stability.
- The member/role/field translations construct the target derivations. Methods
  keep the receiver delayed inside Call; fields evaluate the current view.
  All casts, adapters, latent results and retrieval effects are accounted for.
- Finite declaration signatures are checked body by body and closed with the
  guarded recursive environment/template rules. Same-SCC/self use retains the
  open interface. Generalization and condition extension/quotient lemmas retain
  all original direct occurrences and fixed target identities.
- Worked derivations cover a two-input Index role with an associated result,
  a non-forcing Computation receiver and a Tick-effectful result adapter.
  The rejection table covers narrowed universals, split associated witnesses,
  missing prerequisites, cycles, missing required fields and inconsistent
  effect/owner instantiation. These are paper calculations, not runtime tests.

## Exact remaining premises and owners

The selected impl's applicability is established by its actual instantiated
head/index, body conformance and retained direct obligations; no undefined
`HeadMatches` premise certifies safety. **Uniqueness among every possible impl
and compact/head correspondence remain OPEN.** The original source requirement
of a unique selected impl is not waived by the fact that operational type safety
can be proved for any one correctly typed, fixed dictionary.

Still required for original compiler/source closure:

1. `role_solve`: prove compact/endpoint/head matching corresponds to the raw
   nontransitive packet, and establishes the intended unique implementation;
   build all required local evidence without candidate-body trial inference.
2. `selection`/`lifecycle`/SCC: construct and update authentic snapshots, register
   all dependencies, retry at the correct frontier, retain every direct/role
   obligation and actual value-use edge, and preserve generalized interfaces.
3. generalization/intrusion/linker: establish the actual occurrence, whole-packet
   and initialized-environment premises used by the mathematical lemmas.
4. source/compiler and VM/native: generate these derivations and realize this
   explicit machine. Theorem 10.2 alone does not prove either correspondence.
5. Independent review of both frozen manuscripts, especially the new internal
   evidence application and its refined View/latent transport.

Oracle first-success vs batch equivalence, final-graph reselection stability,
cross-overload principality/coherence, unrestricted evidence-search termination
and completeness, original Simple-sub A/B and Q1-Q8 are not promoted. The source
support envelope and accepted semantics were not changed to shorten the proof.
No compiler code was changed.

## Frozen evidence and checks

- Baseline: `ea750612c5b77d0370c8a844fe23f80ec3f9a0a2`.
- New manuscript SHA-256:
  `1d6d768e5c0dda419868ba63b29031bf641212a631294b0e61babb92c2d6c091`.
- Earlier operational manuscript SHA-256, unchanged:
  `7d71399381509b97cc080406401dafc06506a1fec614bf1b0ce4a8f1c95a87b4`.
- Original user TeX SHA-256, unchanged and unstaged:
  `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65`.
- Frozen source/spec inspection used
  `a58eefc31e22141574b6f20c6a5748151c6d79f1` via `git show`:
  method/role specs, generic conformance design, selection/lifecycle, effect
  helpers, SCC/uses queries, polarity projection and role matching owners.
  Reading those owners is source evidence for the locators, not full validation.

XeLaTeX produced a 21-page PDF at
`/tmp/yulang-dot-20261023/yulang-dot-selection-safety-ja.pdf`.
Final document log has no undefined-reference, overfull or other warnings.
Pages 4 and 18 were visually inspected. `git diff --check` and
`python3 tools/agent_sprint.py check` passed; the latter is static record/tooling
consistency, not live execution or independent review. Rendering is not proof checking.
No compiler builds, semantic tests, executable proof probes, unit tests,
background services or external publication were run.

Primary clock observations: 2026-10-23 13:06:29 UTC for the admitted work receipt,
13:41:24 UTC at manuscript freeze. This is within the 7,200-second envelope.
Runtime model and session metadata remain UNKNOWN. All four prior-session
UNKNOWN worker identities and quarantined leases remain reserved. Their files
and the other untracked user documents were not consumed, changed or staged.
Manuscript authoring is stopped; only exact-path record/Git integration remains.
