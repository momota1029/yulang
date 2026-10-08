# Same-family annotation markers at different Function positions

Date: 2026-10-09
Assignment baseline: `31cc8577314c1ac483e319777bf698df9b23ac34`
Historical source: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Method: minimized representation counterexample and bounded source correspondence
Status: frozen on submission; independent review pending
Claim class: historical characterization plus conditional attribution obstruction
Exclusive write lease: this file only
Language, implementation, activation and gate-closure authority: none

## Objective and governing premises

Test whether the frozen Oracle's argument-effect-contract sidecar can supply
C6's authentic annotation-to-contribution incidence when two occurrences of
`io` have different original Function positions. The answer is limited:
**the sidecar alone has no inverse recovering the argument-versus-return
position, and retains neither contribution/provider identity nor scope.**
This refutes that proposed reconstruction shortcut. It does not refute C6,
which explicitly requires the missing independent typed incidence, or prove
that the entire historical compiler lacks usable evidence.

Exact governing sections at the assignment baseline:

- FVIEW (`notes/design/2026-10-05-inferred-function-call-views.md`) §1.1
  separates written annotations, normalized inferred targets and internal
  views; §4 permits removing only the specified contribution from `f` and
  leaves correspondence and realization open. The accepted single example is
  `apply(f: _ -> [io] _, x) = f x`; permission does not imply action.
- Source contract (`notes/design/2026-10-05-source-contracts-and-common-allowance.md`)
  §§3.2–3.4 retains original Name/provider, Call/receipt, ordered operands,
  scopes and whole joint transport. §5.1 requires semantic as well as
  structural incidence. §6.1 retains the non-coverage kernel and original
  binder tree; subtraction needs its existing evidence. These are conditional
  formation/allocation premises, not a selected annotation-removal calculus.
- Annotation upper exposure (`notes/theory/2026-10-08-annotation-upper-exposure-constructor.md`)
  A1–A4 supplies an actual boundary, direct current endpoint, normalized
  target with designated output occurrence, and preservation of original
  identities despite equal endpoints. A5 original upper-use classification
  and A6 authentic seed are separate inputs. None is proved by a marker.
- Production Call proposal §4/C6 and §7/C6 and the C6 conditional derivation
  require genuine annotation/contribution incidence, then separate lawful
  change and frame evidence. This artifact attacks only replacing incidence
  with a family/depth key. It selects neither activation alternative.

No question-board path was read or written. Approved decisions are used only
as already incorporated into the pinned governing documents and packet.

## What the historical sidecar actually records

At the historical revision, `crates/poly/src/expr.rs:81` stores
`arg_effect_contracts: FxHashMap<DefId, ArgEffectContract>`. Each contract has
markers with exactly `(path: Vec<String>, depth: u32, resume)`, at lines
148–163. The `path` is the resolved **effect family path**, not a Function
child/occurrence path. The `DefId` key is real extra information: independent
formal keys `b_f != b_g` are distinguishable; a cross-formal collision that
silently drops this key is not a counterexample to the actual sidecar.

In `crates/infer/src/lowering/expr/lambda.rs:1357–1433`, a Function root starts
at depth zero. Each Function traversal sets `nested_depth = depth + 1`
(saturating), records both `arg_eff` and `ret_eff` at that same depth, and
traverses both parameter and result at that same depth. Tuple/application
children preserve the current depth. Resolved closed atoms generate
`PreserveMatchingPath` markers. `markers.contains` deduplicates identical
markers, so sibling position and multiplicity cannot be recovered from order.
`mark_lambda_param_effect_contract` at lines 896–909 inserts the result under
that formal's `DefId`.

The constraint lowering preserves more than this sidecar:
`crates/infer/src/annotation/constraints.rs:363–390` lowers Function argument
and return effects separately, places them in distinct `arg_eff`/`ret_eff`
fields, and exports `ret_eff.subtracts`. Thus the witness concerns a projection
of richer construction data. The assignment's older locator
`crates/infer/src/lowering/annotation/constraints.rs` does not exist at this
revision; the corrected path above was inspected. `tail.rs:538–575` also has
ordinary application operands/origins; these are not in the sidecar marker.
No dataflow theorem about all later consumers is asserted.

## Minimal formal typed pair

Let `A,B` be fixed ordinary value endpoints, `0` the empty effect allowance,
and `I` one resolved closed `io` family atom. Fix one formal key `b`, one
actual callable role and entry, one joint assignment `xi`, and no variables,
recursion, wildcard effect tails or depth saturation. Use the existing four
Function positions, writing

```text
F(A, E_arg, E_ret, B)
```

as metatheoretic notation for a complete Function view, not source syntax or
a new type constructor. The two boundary inputs are

```text
T_arg = F(A, I@o_arg, 0, B)
T_ret = F(A, 0, I@o_ret, B)
o_arg = (a, Function.arg_eff)
o_ret = (a, Function.ret_eff)
o_arg != o_ret
```

The hypotheses are that the two separate annotation derivations supply these
complete targets, legal original scopes and endpoints (A1/A3), and keep their
occurrence identities (A4). Role, entry, endpoints and `xi` agree. This note
does not derive these boundary derivations from raw syntax or use successful
comparison to form them. Their corresponding historical `AnnType::Function`
records have one singleton row in the designated field and an absent or empty
other row. Historical lowering treats an absent field as pure. The pair is
well formed at that representation level; acceptance of any source spelling
is unexecuted and not claimed.

Write `M_b` for precisely the historical marker projection under key `b`.
Direct substitution in the inspected collector gives

```text
M_b(T_arg) = (b, [(io, 1, PreserveMatchingPath)])
M_b(T_ret) = (b, [(io, 1, PreserveMatchingPath)])
```

The two original positions differ; their sidecar images agree. If an inverse
`R` of this projection recovered the designated original position on every
such input, applying `R` to this one common image would yield both
`Function.arg_eff` and `Function.ret_eff`, a contradiction. This proves
non-injectivity and absence of that sidecar-only inverse. It does not assume a
removal transition or a runtime trace.

This pair is minimal for the position-loss claim within Function-root
contracts: zero occurrences creates no positional issue; each witness here
has one Function and one atom. A single Function already has two distinct
fields mapped to depth one; nested Functions, tuple siblings, multiple Calls,
large ranges and saturation are unnecessary.

## Two occurrences in one interface and the approved f contribution

The simultaneous version has exactly two atoms and still one Function:

```text
T_both = F(A, I@o_g, I@o_f, B)

g-side input contribution:
  k_g, o_g=(a,Function.arg_eff), provider u_g, original scope sigma_g
f-side return contribution:
  k_f, o_f=(a,Function.ret_eff), provider u_f, original scope sigma_f
k_g != k_f; u_g != u_f; sigma_g != sigma_f
```

This is a **conditional typed incidence package**, not a claimed accepted
source counterexample. Assume the original constructor derivation supplies
both contributions at these typed fields, with legal scope routes into the
same root and one `xi`. Distinct original scopes are not independently hidden
or flattened; rigid family `io` is available on each route. Assume the admitted
annotation boundary `a` and its local clause `i` identify only `k_f` through
an authentic `Incident(a,i;k_f,o_f;...)` derivation; no such derivation relates
`i` to `k_g`. These are precisely the missing source premises under attack,
not conclusions inferred from the diagram. No A5/A6 protection premise or
lawful removal is supplied.

The selected FVIEW §4 permission, **if** the owning elaboration relates its
specified `f` contribution to this return incidence, can yield
`MayRemove(a,i,k_f;...)`; it cannot obtain `MayRemove(a,i,k_g;...)` by family
matching. The extra input incidence illustrates what must be framed; this
artifact does not assert that the exact approved spelling `_ -> [io] _`
normalizes to `T_both`, nor extend its source policy to arbitrary annotations.
The singleton `T_ret` is the direct positional counterpart of that approved
return clause; adding an independent same-family incidence is the conditional
stress case.

The collector gives

```text
M_b(T_both) = (b, [(io, 1, PreserveMatchingPath)])
```

because both fields emit the same marker and the second is deduplicated. It
also equals the two singleton images. The marker does not report which
position supplied it, whether there were one or two positions, `k_f/k_g`,
`u_f/u_g`, or `sigma_f/sigma_g`. Merely moving providers or scopes leaves it
unchanged because those coordinates are never read by the collector.
Therefore this marker is insufficient to certify the assumed incident fiber
`{k_f}` or the preservation of `k_g`. This is an information-loss result about
the recorded interface, not a source theorem that this package necessarily
exists.

If an independent consumer retains the complete original target, it can
recognize its `ret_eff` field. If it additionally retains the genuine
annotation-to-contribution/provider/scope map, it can distinguish these
contributions. Those added premises can repair this shortcut; the sidecar
non-injectivity does not show that no repair or complete Oracle bridge exists.
Selecting `ret_eff` by a known source rule is additional information, and the
rule still needs its original contribution correspondence.

## Independence, mutations and failure conditions

There is no executable oracle or checker. The historical result follows from
inspecting an actual producer's fields and branch behavior, independently of
any proposed C6 removal transition. It shares the assumptions that `io`
resolves to the same closed path and that the displayed Function records are
supplied. The conditional source stress case additionally assumes admitted
boundary normalization and typed incidence; it does not validate them. A
checker supplied those same incidence records or transition rules would check
consistency rather than prove their source adequacy.

Analytical mutations, not executed mutation tests:

| Change | Marker consequence | What it discriminates |
| --- | --- | --- |
| Move singleton io from arg_eff to ret_eff | unchanged | loses Function field orientation |
| Add the second same-depth io field | unchanged after deduplication | loses positional multiplicity |
| Change only provider or original scope | unchanged | has no provider/scope coordinates |
| Change formal key b to a different DefId | changed | actual sidecar preserves binder separation |
| Nest one io under another Function | depth changes to 2 | depth retains some nesting information |

Failure boundaries: this result does not apply to an augmented certificate
that retains original occurrence/provider/scope incidence; markers with
unequal resolved paths, depths or resume policies need not collide; the
DefId-keyed map must not be reduced to a global marker set. Claiming source
acceptance, event protection, numeric pop counts, activation or lawful removal
from this witness would exceed its premises. Source scope routes, boundary
normalization, actual comparison and seed origin remain independent obligations.

The next useful method is to retain and inspect the annotation constructor's
original return-effect occurrence with its provider/scope correspondence,
then compare it with an unrelated same-family occurrence. A third supplied
record probe would leave the same authentic-incidence premise untouched.

## Checks, coverage, resources and dependency snapshot

Commands/checks: full required rule reads; narrow task/index navigation;
`git rev-parse HEAD`; governing documents and historical source with
`git show <pinned-sha>:<path>` and bounded `sed`/`rg`; dependency SHA-256 and
live-versus-pinned byte equality using Python; leased-path creation guard;
final leased readback and hash. One requested historical locator failed.
Two narrow **read-only `git ls-tree` lookups** resolved it; this is a deviation
from the packet's historical-reads-only-by-`git show` instruction. Historical
source content was read exclusively with `git show`. No Git mutation occurred.
Initial aggregate source captures were truncated; all decisive governing and
historical sections were reread narrowly. No exhaustive repository or consumer
search is claimed.

Coverage: one Function root, depth one, one closed family, fixed DefId and
resume policy; singleton position pair plus the two-field simultaneous case.
Seeds/ranges, executed mutations, executable probes, tests/builds, benchmark
samples and production runs: none/zero. No subprocess compute wave, formatting,
compiler edit, shared-record edit, child or interactive question occurred.
Reads were sequential/lightweight; the one Python hash check used sequential
`git show` subprocesses. No numeric process/CPU/RAM/wall limit was supplied.
Aggregate CPU, peak RSS and full wall time were not instrumented.

Unverified scope: raw source normalization/acceptance; genuine source
construction of the simultaneous package; original A5/A6 eligibility;
all annotation/Call/consumer paths; implementation of generalization;
actual request/receiver behavior; lawful realization, principality, full
production membership and source adequacy. No gate status is promoted and
producer readback is not independent review.

| Pinned dependency | SHA-256 |
| --- | --- |
| FVIEW | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| Source contract | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| Annotation upper exposure | `b37cfbefb9e40635e98afb4c39341ca1f7a110e2061c711199b38949397c28ff` |
| Production Call proposal | `e6e333cdffc532310f58ad1fd56091b3e58185fb89802e9ac1814985182487dd` |
| C6 conditional derivation | `a7c64d8545fb1a2c66e88196aaf0ee67cda3bcaa85aa4845d42e4ca2c2fc045e` |
| Historical `crates/poly/src/expr.rs` | `fbee59668b778c09cf32ad5b59c919feb36726b1af75cb630bca1ca9b7aebd88` |
| Historical `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| Historical `crates/infer/src/annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| Historical `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |

The five current direct dependencies matched their pinned bytes at the hash
check. Historical blobs are read from their fixed revision. Integration must
recheck any later dependent movement; unrelated HEAD movement does not alter
the recorded projection calculation.

Recommended next action: primary should require an authenticated original
`ret_eff` occurrence/provider/scope certificate at annotation construction
before using the sidecar as a C6 bridge, with a separate frame obligation for
the same-family `arg_eff` contribution. This is a proof requirement, not an
activation choice or implementation selection.

## Commit packet

- Exact leased/changed path:
  `notes/progress/2026-10-09-same-family-annotation-position-counterexample.md`.
- Baseline SHA: `31cc8577314c1ac483e319777bf698df9b23ac34`.
- Changed dependency hashes: none at the direct-input check; pinned hashes above.
- Review status: frozen unreviewed research checkpoint; historical projection
  non-injectivity and conditional attribution obstruction; no C6 closure.
- Checks already run: policy/section reads, pinned historical branch/field
  inspection, dependency byte/hash check, creation guard, leased readback/hash;
  zero tests/builds/probes. Locator lookup deviation disclosed above.
- Proposed one-line research-checkpoint commit message:
  `research: expose same-depth annotation contribution position loss`.
- Shared-record deltas intentionally left to primary/curator: link this bounded
  marker non-injectivity result; correct the historical annotation constraints
  locator; preserve DefId-keyed distinction; keep authentic C6 incidence and
  independent realization/frame open; promote no authority or gate status.
