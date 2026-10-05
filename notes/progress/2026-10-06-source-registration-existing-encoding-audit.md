# Existing single-formal source encoding: registration audit

Date: 2026-10-06
Status: frozen research characterization; independently reviewed with one minor locator repair; no implementation authority
Baseline: `ce6abbf375e4dbcf5f98ef99826cc98bf557f5cb`
Lease: this file only
Method: bounded static grammar/example/owning-code correspondence audit

## Objective and governing scope

Find an existing concrete source encoding of the approved unannotated
`apply f x = f x` semantic shape, using one legal formal per binding, without
selecting new grammar or changing actual callable roles. The primary supplied
the zero/one-formal production boundary; this audit explores an alternative
encoding instead of repeating that multi-formal rejection investigation.

The Authoritative inferred-call-view document §§2–3 requires source-derived
slot/annotation/scope identity and typed call/owner/receiver evidence,
independent of pending comparison `Q`. Section 3 selects the provisional
protected Handler view and ordinary-value resolution for the approved shape;
it explicitly leaves their inference judgments open. Sections 1.1 and 5
separate that internal seed from actual role and written types and select no
grammar change. These decisions remain fixed.

The canonical syntax architecture's “canonical Statement binding / use
declaration extension,” Authoritative surface grammar (lines 11090–11229),
permits visibility-prefixed bindings and inline or indented bodies. Its
precedence-neutral structural-primary/tail boundary (4573–4588) locates ML
application syntactically. Braced-block and With-body syntax references define
composition but expressly exclude HIR/type/semantic interpretation. The root
architecture header is Proposal; authority here is the scoped Authoritative
addendum, not a blanket promotion of every historical paragraph.

The direct `f x` Pattern forms additionally rely on the later
[Authoritative F5 general-function foundation](../design/2026-09-21-f5-general-function-scheme-foundation-draft.md)
§§19–20 and 41. Section 20 admits sibling ML-application tails in canonical
Pattern, including binding-header positions; §41 is an explicitly approved
amendment that preserves this shared Pattern admission under delimiter-scoped
caller stops. This later authority supersedes the older architecture's
statement that ML-application patterns remain future surface. It licenses the
candidate's grammar composition, not its block-result, capture or typing
semantics.

## Result and exact claim class

**Bounded characterization:** an existing nested-binding surface candidate
avoids the two-formal header and does not require inline-lambda grammar:

```text
my apply f = { my step x = f x; step }
```

Each binding uses the same single-identifier-formal header shape admitted by
`plain_binding_header`. Canonical Statement/braced-block productions compose
binding, separator, and final identifier expression. Existing syntax fixtures
at `crates/yu-syntax/src/tests/declaration/binding.rs:854` cover local bindings
and subsequent expressions in braces and indented blocks. This is a
production-composition derivation, **not a fresh parser run or a typed
acceptance result for these exact bytes**. No source equivalence or completed
registration theorem is established.

A second surface candidate is `my apply f = step with: my step x = f x`.
The With-body production allows one nested canonical binding, but its scope
explicitly excludes companion semantics and target association. It adds a
further visibility dependency and does not improve the bridge, so no further
variant was pursued.

No examined governing source proves that either candidate denotes the approved
shape. This is a bounded absence boundary, not a claim that no equivalent
encoding exists anywhere in Yulang or its Oracle.

## Conditional structural derivation and missing premises

For the brace candidate, let `d_f` and `d_x` be the two distinct formal
occurrences; let `u_f`, `u_x`, `u_step` be the name occurrences in the inner
body and final expression; let `c` be the `f x` application occurrence.
A structural correspondence to `lambda f. lambda x. apply(f,x)` requires:

1. **H_binding:** each plain one-formal local declaration introduces its
   Function value, with the same binder/body correspondence as a root binding.
2. **H_scope:** the inner body resolves `u_f` to outer `d_f`, `u_x` to inner
   `d_x`, and the block's `u_step` to the local declaration `step`.
3. **H_block:** a block containing the local declaration followed by `step`
   exports that Function value, retaining its capture of `d_f`, rather than
   allocating another semantic kind or discarding the result.
4. **H_call:** typed elaboration gives `c` the source call/argument receipt,
   typed paths, owner/receiver incidences, and ordinary-value evidence required
   by the selected contract.
5. **H_registration:** the encoding correspondence preserves annotation
   absence and maps the approved formal/use instance to the same shared
   `beta`/`Slots(beta)` and original joint `nu,K,D`, including its provisional
   fully protected seed and scoped discharge. This must preserve the actual
   roles/entries of subsequently supplied callable values.

Under H_binding–H_block, ordinary lexical substitution of the local Function
value for final `step` yields the *candidate structural tree*
`lambda(d_f, lambda(d_x, call(c, u_f, u_x)))`. This is a conditional
AST correspondence only. It is not an effectful contextual-equivalence proof,
a registration rule, or a principality result. H_call and H_registration are
additional requirements even if that structural correspondence is proved.

The syntax references do not establish H_binding–H_block's meaning. The
approved source-shape statement does not itself establish H_registration for
a nested-binding encoding. In particular, substituting a concrete Pure value
for `f`, classifying every Value argument as implying Pure, or reading an
empty effect row into the seed would change the selected meaning.

## Source identity versus implemented transport

The candidate contains concrete, distinct ranges for the two formal
occurrences, their uses, the call, and the absence of annotations. Thus there
is no need to invent a token-level `f` or `x`. Lossless CST source identity is
sufficient to *name* those occurrences, but cannot generate a typed path,
`Flow`, receiver, protection fact, or a jointly scoped constraint assignment.

Current production steps stop independently:

- `module.rs:1471` accepts zero/one plain formal. `1155–1205` creates one
  parameter identity under a definition root, enters that scope, lowers the
  body, and wraps it in one `ResolvedExpr::Lambda`.
- `lower_body` rejects indented Statement blocks (`1305–1320`). Its inline
  route calls `lower_simple_chain`, which requires an associated childless
  atom (`1419–1423`) and resolves only Integer/Identifier leaves. The brace
  candidate has a composite body; it cannot become the required nested
  resolved Function/call tree on this route.
- `ResolvedExpr` has Lambda/Integer/Name/Error, without Apply.
  `ConstraintBatch::collect`, `yu-solver/src/lib.rs:913–964`, marks a Lambda
  complete only for supported Integer or resolved/parameter Name bodies;
  nested Lambda/Error bodies are Error. `1038–1051` consumes the existing
  one-Lambda recipe, not arbitrary source blocks/calls.

These implementation limits do not select source rejection semantics. They
explain why a syntactically composed candidate cannot supply a current HIR or
solver registration certificate.

## Alternative encodings and oracle independence

`my apply f = \x -> f x` would need inline-lambda grammar and its capture
boundary. Architecture lines 7981–7989 explicitly leave backslash-lambda
primary/boundaries for a dedicated addendum. The mention of “lambda” in the
structural-primary classification at 4581 supplies an architectural location,
not a lambda production. The retained research test at `tails.rs:4–23`
characterizes `host (\x -> x)` as Error tokens and explicitly disclaims accepted
source behavior. Its assertions were inspected, not executed here.

The retained HIR research route (`lib.rs:976–1012`) manually extracts multiple
parameters and builds nested research lambdas; `1756` and `1884–1887` use
`my call f x = f x` / compose forms. The associated progress note
`2026-10-04-hir-source-core-boundary.md:199–217` expressly excludes production
currying/type correspondence. This is a candidate construction sharing the
currying hypothesis, so its output cannot independently prove that hypothesis.

The runtime perf fixture uses `my leaf(x)` and a multi-argument recursive
function, but supplies no nested-binding capture/result or protected-formal
example. It is retained source text, not evidence this current compiler
accepts the candidate. No Oracle process, alternate semantics implementation,
reference interpreter, or newly executed checker served as an independent
oracle. The independent evidence categories are scoped grammar productions
and owning production code; neither proves the omitted typed source rules.

## Coverage, commands, resources, and stopping condition

Budget: at most 12 sequential lightweight top-level command invocations; zero
builds, tests, probes, Git mutations, child agents, or other output files.
Consumed: 12 top-level `exec_command` invocations, sequential. Work consisted
of `cat`/`rg` and short Python file reads plus read-only Git baseline/hash
comparisons. The final invocation writes this lease and checks its contents.
One command's repository Markdown locator scan took approximately 3.15 s;
other reported command times were below 0.1 s. Complete session wall time,
peak RSS, and CPU usage were not instrumented and remain unknown. No heavy
process ran; short read-only `git show` subprocesses ran sequentially.

Search envelope: canonical syntax architecture, current English syntax
references, supplied call-view authority, current HIR and solver collection,
retained syntax/HIR research examples, a relevant HIR boundary note, and the
ordinary-call runtime fixture. Broad early `rg` captures were truncated and
one queried `spec/` directory and `web/docs/reference/functions.md` were absent.
Subsequent reads targeted the decisive source sections. The public type/docs
paths referenced by the authority (`web/docs/reference/types.md` and
`type-theory.md`) were absent in this checkout. This is not exhaustive
repository-wide or external-Oracle search. No seeds/ranges, random sampling,
mutants, executable enumeration, or performance samples apply to this static
audit. The lease's note/hash checks are not compiler verification.

Failure conditions for extending this result: a governing source already
establishes H_binding–H_registration for this encoding; a dependency changed
from the pinned bytes; or a stronger current source rule invalidates the
surface derivation. A successful parser-only run would strengthen exact-byte
syntax characterization but would leave the decisive typed premise untouched.
Stop at that premise instead of running an equivalent toy probe.

Recommended next action: the primary should resolve the narrow nested-binding
block-result/capture correspondence (H_binding–H_block) against an existing
governing semantic source, then explicitly require its registration-preserving
bridge (H_call/H_registration). If no such authority exists, report that exact
premise for the affected gate; the current evidence does not require a grammar
change or reopen the approved role meaning.

## Frozen direct dependencies

Every dependency below was rechecked byte-for-byte against the pinned baseline
in the final invocation. No dependency hash changed. Shared task/index/theory
edits observed in the working tree were not consumed as semantic authority and
were left untouched.

| Path | SHA-256 |
|---|---|
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md` | `51d37bb77b069bfbcd8d7c320b7ced64f51c401b` |
| `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` | `08beb9711c2373e161a408b19a6ccd6c08e24e0b41791e7fac2ea0a332dec1ed` |
| `syntax-reference/en/src/statements/binding-use.md` | `18d08a59c211027dc95c9556d71703a8bda7b4c1d3dc72e253e7b7dae93c928f` |
| `syntax-reference/en/src/expressions/braced-statement-block.md` | `81f637db94d344162c4e2541ee4b955b4469180e755ee800aa39bf9074987b58` |
| `syntax-reference/en/src/expressions/with-body-tail.md` | `656b7191d1ae5dd7d740de2096b1ac55390233d445e4316bc4ab8d002cba8018` |
| `syntax-reference/en/src/expressions/operator-chain.md` | `56cd8495ad0b14cddb4da9fa8088e43647ce4d522ffcab19a08857d2dda1c842` |
| `crates/yu-hir/src/module.rs` | `ed92636de471b4d424a274f3509673c68761d9fa24fa06f07c9afc3bb3b9b7a5` |
| `crates/yu-hir/src/lib.rs` | `56aafd7d958acdfa3362ffcc7bf3e815d795f455597cf4f8e471194addb04c1b` |
| `crates/yu-solver/src/lib.rs` | `a2103c6735d7a4efad00231f973544dda59d42219dbf83439fffc17889168e59` |
| `crates/yu-syntax/src/pattern/mod.rs` | `f61a4928f9982e9885ba726213f1f6a6cef4feb89ebae38c98f629a9bafc4f03` |
| `crates/yu-syntax/src/tests/tails.rs` | `e498d36fc12b5fecfff06dd703e7136618a5f6836221362ce1e651fd400e5fc0` |
| `crates/yu-syntax/src/tests/declaration/binding.rs` | `16531ba977346996964cb3703ba63f47cb9e9a02064fc5662ea02ccbbe9feaac` |
| `notes/progress/2026-10-04-hir-source-core-boundary.md` | `8bb313da52ae419fa9ec72645f98db2d392558e7f2023489a93ab9a36e86e1ed` |
| `tests/perf/runtime/v0/ordinary_function_call/leaf_call_100000/main.yu` | `c82b003290bd7a18188e72235252b4ff968615fa7e431db151971287afd5dd4a` |

## Commit packet

- Exact leased paths: `notes/progress/2026-10-06-source-registration-existing-encoding-audit.md` only.
- Baseline SHA: `ce6abbf375e4dbcf5f98ef99826cc98bf557f5cb`.
- Changed dependency hashes: none; frozen SHA-256 inventory above.
- Claim/review status: bounded static characterization plus conditional structural derivation; frozen, unreviewed research checkpoint; producer reread is not independent review.
- Checks already run: read-only baseline equality and dependency SHA-256 inventory; exact lease absence before write; note-content/lease verification. No parser, compiler, tests, builds, or executable semantic checks.
- Proposed one-line commit message: `research: audit existing nested-binding encoding for source registration`.
- Shared-record deltas intentionally left for primary/curator: record the existing surface candidate, distinguish H_binding/H_scope/H_block from H_call/H_registration, and preserve the production HIR/collection boundary. No shared task/index/theory/authority/question-board files changed; no gate closure proposed.
