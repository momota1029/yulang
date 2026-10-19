# R117: exact Catch payload identity from source to runtime lookup

Status: frozen candidate conditional source/native correspondence, awaiting fresh
independent review. Author: `/root/r117_proof`; no descendants. Contract R117
revision 3, SHA-256 `2a8336e2c42228fca21ef156b84fc471f56d5636d63c508f12186da8670c4457`.
No parent theorem or production gate closes here.

## Parent and exact domain

The parent is static-to-runtime projection within the six-front effect-hygiene
program. The bounded question is whether the operation-arm payload bound by the
following original source is the binder constrained by candidate inference and
read by the runtime body, with the originating lexical environment retained:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my main = catch io::tick 7 { io::tick(p), _ -> p }
```

The source has no final LF; its contract hash is
`f3b8173cc77bc99e0d50b0d3dac60de7702eaae2d8874fd875d5ade97a76a059`.
The fixture is retained verbatim as `EFFECTFUL` in the pinned R116 CLI test.
R116's exit-0, exact `7\n`, empty-stderr observation is historical finite evidence
only. It is neither a general permission theorem nor proof of an uninspected
caller/identity join.

Preserve the original well-typed monomorphic assignment, operation signature,
selected-arm compatibility, actual request/event and owner hypotheses. Preserve
all independent effect, evaluator and Simple-sub A/B quantifiers. This note
introduces no inference rule, semantic selection rule or scope restriction on
the whole language.

## Conditional statement and notation

Let H be one authentic immutable HIR artifact with successfully retained
LocalSource L for this source's `main`. Let r be L's actual `source_root()`, c
the original Catch index, a its sole arm's original `SourceNodeKey`, j the
original body-name index and o that body's original HIR occurrence. Define
beta as the **constructed** payload ID, not an ID reconstructed from spelling:

```text
beta = LocalSourceCatchBinderId { owner: r, arm_source: a, ordinal: 0 }
```

All letters denote objects returned by the real constructors; no numeric root,
occurrence or parse identity is guessed. Assume successful candidate collection
of L in batch B, runtime construction P by `RuntimeProgram::from_hir` on the
same H, and an actual compatible request reaching selection of this original
arm in P. Let E be the lexical environment saved by that Catch installation,
and R be this request's actual `ReceivedValue` payload.

Then the following source implications hold at the pinned bytes:

1. L's body Name resolves to beta; beta's owner is r and its arm key is a.
2. Candidate collection associates beta with one representative component q;
   the body's endpoint is that same component. Its scheduled Catch action
   targets q against the original declaration's argument, preserving r and o;
   successful action execution admits the two argument links described below.
3. P retains beta, the original arm and body label. Selection extends E with a
   fresh initialized cell `(Binder::Catch(beta), R)` and evaluates that body's
   code there. Its Name lookup returns exactly that cell and R.

This is a relation between source resolution, candidate component and runtime
cell. A static component is not a runtime cell, and a lexical environment is
not an execution-owner ID or a snapshot of the mutable store.

## 1. Authentic construction and lexical scope

`module/local_source.rs:299` defines the ID with private owner, arm-source and
ordinal fields and derived equality/hash. Its getters expose those same fields.
`Builder::catch_value_pattern` at 1104–1118 constructs beta directly from
`self.owner`, the actual arm key and the supplied ordinal, retaining the
payload pattern's own source key/range/spelling. `_` returns Wildcard before
any binder construction. `Builder::key` at 802 reads the lowering counters'
source-node map; it does not invent an association from `p` text or an offset.

`Builder::catch` at 1137–1173 gets a from the original CatchArm node, constructs
the payload with ordinal 0 and continuation with ordinal 1, and stores the
pattern and original body index together in `LocalSourceCatchArm`. Here the
continuation `_` contributes no second binder. It schedules the body with
`LocalSourceScope::CatchArm { catch: c, arm: a }` and the very binder cloned into
the arm pattern. This is the constructor-to-body ownership join.

`Work::CatchArm` at 647–653 first saves lexical depth, then pushes the constructed
binder's spelling with `LocalSourceResolution::CatchBinder(beta)`, then visits
the body. `push_binding`/`restore` at 746–789 maintain the latest entry and its
previous entry, so this scope shadows an enclosing spelling and restores it
when the arm body finishes. Identifier construction at 1006–1041 clones the
latest lexical resolution. The exact body is a single `p` with no intervening
binder: its Name therefore has resolution `CatchBinder(beta)`. The scrutinee
is scheduled before the arm and its lexical depth is restored before the arm
work; the arm binder is not installed into the scrutinee's lexical scope.

Expression indices carry r. `LocalSource::expression` at 143–147 refuses an
index whose owner differs from L's owner. Occurrences are published from source
child order by `order_occurrences` at 108–133, retaining the body source key.
`source_identity.rs` records original parse/definition/occurrence provenance;
it has no separate Catch-binder map. This proof uses the actual private-field
Catch constructor, not a fictitious parameter-provenance row. The optional
shadow lookup is not production resolution: `shadow.rs:531` explicitly states
that boundary; `source_position` at 833 rejects foreign/ambiguous/missing keys.
No shadow name association is needed for this derivation.

## 2. Candidate endpoint and payload constraints

`candidate_source::emit_candidate_source` at 826–846 retrieves
`self.hir.local_source_for(r)` and requires pointer equality with L. It also
checks the receiver/root relationship, HIR ownership of every occurrence and
consistent occurrence-to-source-owner registration. Thus a structurally similar
LocalSource from another HIR cannot establish this collection premise.

At 864–869 each expression obtains its actual candidate component. At 934–940
`catch_positions` is keyed by the complete Catch-binder ID, taking the first
matching Name's value position. The exact source has one beta Name, so let q
be `positions[j].value`. This does not search for the string `p`.

Work visits the scrutinee before `Work::CatchArms` (973–975). In CatchArms at
1045–1087, the `retain` closure reads q with the arm payload's beta and inserts
`catch_binders[beta] = CandidateEndpoint::Component(q)`, recording its arm-level
component level. Wildcard continuation retains nothing. It emits a
`CatchOperation` action containing the original resolved declaration, owner r,
body occurrence o, `payload=Some(q)`, `continuation=None`, and the actual
scrutinee endpoint/effect. It then schedules this original arm body.

On visiting the body Name, 962–964 replaces its endpoint from
`catch_binders[beta]`. Consequently the body endpoint is exactly Component(q).
No missing binder silently falls back to a name or global: lookup failure is
an error. The Catch result's body constraint at 1159–1163 uses this endpoint
with occurrence o; thus the actual payload endpoint participates in the
original Catch result path. Name finishing at 1219–1244 treats CatchBinder
as an ordinary value read, not a module/local scheme instantiation or a
Computation formal. Its own effect facts still follow the existing route.

The action consumer at 1690 passes the retained operands unchanged to
`candidate_catch_operation`. In `candidate_effect.rs:932–959`, the original
function signature supplies `argument`; one Operation signature context retains
the declaration, r and o. Positive and negative argument terms are generated
using the same local value/effect/view maps, and admission is requested for
slots 60 and 61:

```text
argument-positive <= component(q) <= argument-negative
```

For this source those are the original `tick` argument's primitive Int ports.
These are the actual emitted/admitted constraint calls under successful
execution of that action, not a proof that a synthetic checker or an assumed
transition produced source. Preflight at 484–499 checks the single payload,
resolved monomorphic function signature and supported referenced-binder uses.
The constructive result concerns identity and the constraint consumer; it does
not prove convergence, principal inference, arbitrary propagation soundness,
permission equivalence or a globally complete runtime typing correspondence.

## 3. Runtime instruction, arm environment and body lookup

`RuntimeProgram::from_hir` at 249–326 obtains L from its supplied H and maps each
index through `source.expression(index)` before assigning the original source
ordinal's code label. At 449–476 it clones the Name resolution into
`Instruction::Name`; a CatchBinder Name gets `NameConsumption::Observe`.
At 540–553 it clones the entire original arm pattern, a, body label and range
into the Catch instruction. These are source-object copies, not fresh binder
construction from the string `p`. The same-H premise makes these beta and a
identical to those used by B.

`machine.rs:707–738` installs `Frame::CatchReturn` containing this handler code,
the current lexical environment E and a fresh installation with actual execution
owner, then evaluates its scrutinee in E. These static r and dynamic owner
identities have different types and roles. At 1516–1530 installation validation
requires the actual current owner, liveness and allocated occurrence; it does
not substitute the source root for a runtime activation.

At 1550–1606 `propagate_request` reads that actual saved frame, iterates its
retained operation arms, compares complete original operation IDs, preserves
the visibility branch and checks function shape, one payload and primitive
payload compatibility. The single-arm source has no duplicate-arm ambiguity.
This proof is conditional on those actual selection premises; it does not
infer visibility from a missing local Grant. The historical closed-primitive
result is reusable only under its complete-source/fresh-context premises.

At 1634–1655 selection pops this exact handler, abandons the uncaptured suffix,
and calls `bind(E, Binder::Catch(beta), R)`. At 1657–1682 the wildcard continuation
adds no binding and the state evaluates the original arm body in the new
environment E'. `bind` at 1980 creates a fresh cell initialized to R;
`extend` at 1972 retains E as the parent. Thus E' extends the originating
Catch lexical environment, rather than the environment of an unwound native
operation or another arm. Popping the handler changes control activation;
it does not replace this lexical parent with a saved store.

At 575–578 body Name lookup matches `Binder::Catch(candidate) if candidate ==
beta`. `lookup` at 1960–1970 checks the newest binding first, so it returns the
fresh cell before any parent binding. At 583–618 the initialized R is passed
to `consume`; the Observe branch at 1858–1872 returns R after validating its
existing value/view relation. It does not reexecute R or reconstruct it from
its primitive value. This proves the stated payload-to-body projection when
selection and that existing evidence check succeed. Evaluation of the literal
7 and every preceding native transition is outside this local lemma.

## Parent application, exact remaining edge and falsifiers

The result reduces this fixture's static-to-runtime binder obligation to an
explicit outer same-artifact join: successful authentic source formation and
candidate processing as above, followed by runtime construction from that
same immutable H. Within this envelope every inspected binder join and the
lexical parent is determined by actual source constructors and consumers.
There is no remaining name-based binder association to postulate internally.

The pinned sources do not include the public CLI caller that connects candidate
batch HIR ownership to the Arc passed into `RuntimeProgram::from_hir`. The
runtime's operation-v1-specific pointer guard at 253–257 does not establish
that join for this direct primitive fixture. R117-JOIN-1 remains OPEN, owned by
the public caller which invokes those two APIs; Luna must lease/pin that caller
before extending the claim. Required evidence is the same underlying HIR Arc
through both calls (or an explicit reviewed identity-preserving transfer), plus
the actual successful retained source/admission path. R116 output supplies
neither pointer equality nor a general proof of those constructor premises.

Falsify this bridge by a foreign L accepted despite the collection pointer
check; different full beta IDs at the payload pattern/body Name; a changed
candidate q at body/result consumption; runtime rebuilding beta from spelling;
a different original arm/declaration being selected; or E' parentage/lookup
returning another cell. Falsify a proposed public closure by a caller lowering
or substituting a second HIR artifact without a correspondence proof. An
uncaught request, failed visibility/evidence check or unsupported source is
outside the success premise, not evidence that general permission holds.

All six effect parents remain OPEN: ordered priority; Value/Computation entry;
wrong/sibling permission; unmatched outward request and suffix; continuation
capture/resumption; static-to-runtime projection. R100-P2 and evaluator/Simple-sub
A/B remain OPEN. Charter §§14–15 authorize the outside shallow direction, and
§21 fixes source roles; none closes these original obligations.

## Frozen inputs and resource receipt

Proof source hashes, verified against the contract:

```text
crates/yu-hir/src/module/local_source.rs 3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786
crates/yu-hir/src/shadow.rs 9f7a80055076a01cbd99a3eb9c5bc8c3f0db512f2e84032a53af0eacdad2375b
crates/yu-hir/src/source_identity.rs 7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3
crates/yu-solver/src/candidate_source.rs 66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c
crates/yu-solver/src/candidate_effect.rs 6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0
tools/inference-playground/src/runtime/program.rs 7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a
tools/inference-playground/src/runtime/machine.rs fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46
tools/inference-playground/tests/cli_approved_surface.rs 43fc3670b80e931a0865f3790a9a39b5755e09a6c591e89b2cbf9b18213ba43a
```

Authority/reuse: R116 rev3 contract
`0b9653736e84baa63a04a74bbc0b23742c17941be38b4cceede4cb91d0393ea5`;
`notes/design/2026-09-29-scc-intrusion-redesign-charter.md`
`547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed`;
`notes/theory/2026-10-16-runtime-primitive-event-visibility.md`
`7b27f8cf1d8024e249cc7d8a433c77438e3f59e5543cfc46a96a1af278eb3f56`;
`notes/progress/2026-10-16-playground-primitive-handlers.md`
`8d97124d8aafb618f116745754aecd123ac6f3d69f922b788f8d233a9c8f3ef6`.
The older runtime hashes in those historical proofs are not silently replaced
by today's pins; only their explicitly bounded semantic premises are reused.

Checks: static bounded source inspection and SHA-256 only. No test, build,
CLI, probe, formatter, Git, scratch or source edit. Requested Sol/high; observed
model/effort UNKNOWN. Time and final hash receipt are in the sole assignment
handoff. Both leased outputs stop after that freeze. Next step is fresh
independent compiler/spec review and Luna-owned caller pinning, not an unleased
read or production edit by this author.
