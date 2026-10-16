# Catch image: later lowers, conditional eligibility and retained ownership

Status: independently reviewed bounded source/operational feasibility audit.
Baseline: primary-pinned `2140859b1`. Exclusive lease: this file.
The proposed CatchImage is UNAPPROVED; this note selects no architecture.
Independent mathematical checked_result_semantics and source/authority
capture_source_review are CLEAN at producer SHA-256
`d21d4e96a875a49e9b9c93ef0a7a4b59e633ac7ed4347335f7b85098ac8c8534`.
The primary accepts the bounded discriminator/lifecycle characterization;
finite keys, source actions and complete native feasibility remain unproved.

## 1. Question, authority and claim class

Can ordinary monotone Simple-sub propagation retain an unresolved Catch image
and process later lowers without premature residual publication, generation-time
solving, search or source restrictions? This audit uses actual source and native
construction owners, independently of the other producer's live contract draft.

[Top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
sections1/1.1 require generation, accumulation and ordinary propagation while
types remain symbolic. They do not require all constraints solved before capture.
[Annotation hygiene](../design/2026-10-10-annotation-effect-hygiene-integration.md)
sections1.1/1.2/3 distinguishes permission, inflow and actual handler residual;
independent same-family effects survive. The original shallow operator remains
the one in [source ownership](../design/2026-10-02-typed-source-owner-realization.md)
section6: actual eligibility, outside selection/arms, raw continuation and
current-state forwarding.

Result: a scalar eager-forward/drop fallback fails a necessary stability
condition. No intrinsic impossibility of a retained qualified image is proved.
A bounded worklist argument below isolates its unproved native operation and
ownership premises. It is neither source eligibility derived from a toy table
nor an all-source/native theorem. No source-qualified counterexample is claimed.

## 2. Source-generated discriminator and actual later-lower route

Use original resolved occurrences of this source schematic:

```text
act E: our ping: Unit -> Int
p(u:Unit) = E::ping(Unit)
relay(cb: Unit -> [E] Int) =
  catch cb(Unit) {
    E::ping(payload), k -> k(0)
    Return(v) -> v
  }
answer = relay(Name p)
```

The syntax is semantic source notation, not a parsed/executed fixture. The
annotated callback/Catch shape is the source-selected annotation-hygiene
section1.1 case. The raw k response is the operation's Int. Formation retains
the complete declarations, primitive/world/instance/profile/receipt/guard
premises; this note does not assert their satisfaction or actual source
acceptance. Current native negative-formal preflight defers this annotation;
this discriminator is for the proposed extension, not a bypass of that guard.

Name original identities as follows; they are constructor occurrences, not
invented numeric native IDs:

```text
L_r      relay Lambda/formal cb registration and annotation occurrence
C_b      original body Apply cb(Unit), with its complete Function upper D_b
H        original Catch, scrutinee S and output R_H
C_out    original Apply relay(Name p)
U_p      same p provider and its original operation/return/consumer references
O_p      original E operation occurrence in p
A_H      arm occurrence, raw-k binder and its original k(0) Apply
```

Relay's generic body supplies its cb upper demand before main's actual
argument-provider lower has reached that formal. The outer Function comparison
later produces `actual_argument_p+ <: formal_cb-` through the contravariant
Argument child (`lib.rs:12644–12650`). Meeting that lower with D_b produces
the original ResultEffect child (:12659–12664); source operation construction
and declaration bounds can then supply E to the scrutinee. The original source
formal/use and provider origins remain separate. This is an authentic ordinary
later-lower dependency, not a private test API or a demand that source generation
wait for the callee to be known.

There is no claim that the current queue actually presents an E operand before
its needed context: that interleaving was not reconstructed or executed. In a
correct extension the first qualified E item may already carry the complete
symbolic permission/route record. The discriminator tests what happens IF its
eligibility inputs are still pending, and what must survive across later lowers.

For the independent-contribution variant, change only the arm to

```text
E::ping(payload), k -> { let ignored = k(0); E::ping(Unit) }
```

The extra operation has a DISTINCT original arm occurrence O_arm. By the source
outside-image equation (:410–436), it executes outside selected H. The same E
family does not route it through H's scrutinee subtraction. Retain raw k's
complete original continuation/current-world family as well: shallow selection
adds no H wrapper to it. As a no-resume control, the arm `k -> 1` discards its
raw suffix; it does not make the other variants' suffix effects disappear.

These are genuine source constructor branches, not arbitrary guessed eligibility
tables. This packet does not equate their source IDs or prove the complete
program contracts. The discriminator uses nullary E, matching the current
HIR SourceEffectId representation (`source_annotation.rs:32–36`); broader
invariant family-argument obligations remain unchanged.

## 3. The nonmonotonic shortcut and the actual invariant

Fix ONE original joint xi, provider/contribution, path, handler candidate and
event/current-state arguments. Unknown eligibility is lack of a discharged
original predicate, not a transition changing that event's language semantics.
Later native evidence and a genuinely later source event are different things.

For the original Request rule, the retained image has its original branches:

```text
eligible + accepted original arm: outside arm computation, raw k retained
ineligible or exhausted matching: original q forwarded, prescribed wrapper
```

The source equations supply those branches and their full operands. This note
does not prove either guard from row equality, nominal E, a profile label or
the absence of a currently discovered incidence.

Two unsafe reductions follow directly:

1. **Pending => forward E unconditionally.** If the later authentic guard
   establishes consumption, an ordinary committed `E <: R_H` remains an
   obligation. Later propagation has no ordinary subtraction of that already
   unconditional assertion. Keeping it may conservatively overapproximate,
   but does not establish the required handler precision/natural inference;
   it can also produce an erroneous closed-upper mismatch. No current compiler
   false-positive fixture is claimed here.
2. **Pending => handled/closed empty output.** A later authentic forwarding,
   outside-arm or raw-resume contribution is missing from that published
   conclusion. Later discovery can add a lower only if its live obligation
   and dependent consumers were retained; a closed solved-empty handoff loses
   that justification. A fresh unconstrained row with no lowers is NOT itself
   a closed empty result.

The necessary stability invariant is therefore: every unconditional output
assertion is justified by an original constructor/guard derivation stable under
lawful later constraint additions; unresolved branch predicates remain attached
to their original source operation, not replaced by guessed Boolean values.
This is a proof criterion, NOT an instruction to enumerate models at runtime.

## 4. Bounded sufficiency and the unproved operation law

For a fixed finite source/constraint graph AND finite reachable qualified
operation/edge keys, ordinary worklist propagation is sufficient **provided**
an image operation supplies all of the following:

- its genuine local source Request/Return/selection/arm/continuation relation,
  with original guards at the same whole tuple;
- immutable qualified lower inputs, or explicit still-owned pending inputs,
  preserving route/attachment/provenance, current-state and future binders;
- only stable justified unconditional output emissions; symbolic branch clauses
  can be accumulated before their guard operands are resolved;
- wakeup on EVERY relevant new lower/guard dependency, canonical transport and
  copied instance, with no same-generation completed memo suppressing that work;
- publication/use retaining the live image and all its free operands, or an
  exact owned suspension preventing dependent solved reuse;
- recursive references keyed and visited as finite registered graph edges.
  A dependency SCC can remain an owned symbolic equation; lack of a new lower
  is not proof of false eligibility or proof that the SCC is solved.

Under these premises, each step only adds a justified clause/bound to the same
constraint system. Fair processing reaches its finite-rule closure; no prior
bound must be retracted and no guard is solved during generation. This is the
ordinary positive worklist argument. It does NOT establish the premises for
CatchImage, nor assume every semantic predicate has a finite native evaluator.
Finite graph/reference retention is distinct from enumerating its unbounded
source response/history domain. The local operation/guard action and its lawful
copy behavior remain the decisive construction obligation.

For that bounded case, admitting each key once gives work bounded by the
visited keys/edges plus the sum of their local guard/map action costs, and
storage bounded by the retained keys/edges and operand payloads. This is not
a measured native bound: the operation owner must establish finite keys and
local costs across extrusion, equality and FreshUse. Finite source syntax
alone does not establish those facts, and no repeated global census is licensed.

## 5. Actual native seams and a specific inadequate wakeup mechanism

| Owner in `crates/yu-solver/src/` | Relevant existing behavior |
| --- | --- |
| `candidate_source.rs:870–885` | Catch currently emits whole S-to-R_H forwarding plus arm effects. No conditional image is executed here. |
| `candidate_extrusion.rs:442–489,876–899` | New effects become ordinary bound admissions; row/row orientation respects levels. This is accumulation, not an eligibility decision. |
| Same file:799–840 | Later bounds replay against retained opposite bounds through actual relation-backed work items. A new E lower need not create a FunctionPort dependency. |
| `lib.rs:11588–11598,12455–12478` | Duplicate suppression is relation/generation-sensitive. A new image dependency would need lawful reopening/completion behavior, not endpoint-pair equality. |
| `candidate_context.rs:2038–2122` | Replay queue/ack ownership distinguishes transferred, running and completed children. Existing acknowledgements are not automatically acknowledgements of a new semantic image operation. |
| `candidate_source.rs:1277–1317` | Owned source wait/publication staging exists, but its support-registration factory is cfg(test); production certificate creation is disabled. |
| `candidate_context.rs:2636–2653,2667–2715` | Synthetic source support invalidates on watched FunctionPort insertion only. This does NOT cover every later effect lower, image guard or future image operand. |
| `candidate_scheme.rs:38–87,776–825` | Captured graph contains rows, bounds, contexts/evidence and existing nodes. It has no CatchImage operation whose ownership/copy behavior is established by this packet. |
| Same file:1480–1495,1523–1541 | Local installation retains a live root; later use captures/freshens its graph. Root installation is not solved emptiness, nor a substitute for retaining a new relation. |

In particular, “wait for the current FunctionPort census, then publish the
residual” is not supported by the existing source-support mechanism: a later
effect bound can use ordinary replay without adding that watched dependency.
This is a concrete missing wakeup contract, not a hypothetical all-constraints
drain barrier. Existing owned replay/terminal work must be reused under its
proved limits, not mislabeled as completion of future semantic dependencies.

## 6. Handoff and verification

Next owner: establish the image operation's local source-guard/output action
and complete dependency footprint at authentic H, then give its later-lower,
copy/capture and completion/publication contracts. The decisive falsifiers are
an unconditional pending-branch E bound, a forgotten live image at FreshUse,
a newly admitted lower suppressed as completed, or deletion of O_arm/raw-k
survivors by family-wide subtraction. No new architecture is adopted here.

Checks: bounded source reads/rg, dependency SHA-256, Markdown link/fence and
trailing-whitespace inspection. No Git, code/shared edits, tests/builds/probes,
children, live contract draft reads or runtime measurements. Approximately
9 minutes; CPU/RAM unmeasured; zero seeds/samples. No all-source/global theorem,
Catch/OpCompat closure, source restriction or A/B parent retirement follows.

Frozen dependencies:

```text
efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38  crates/yu-solver/src/candidate_source.rs
2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b  crates/yu-solver/src/candidate_extrusion.rs
72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6  crates/yu-solver/src/candidate_context.rs
2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e  crates/yu-solver/src/candidate_scheme.rs
44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9  crates/yu-solver/src/candidate_effect.rs
2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f  crates/yu-solver/src/lib.rs
b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f  crates/yu-hir/src/module/source_annotation.rs
5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa  notes/design/2026-10-02-typed-source-owner-realization.md
a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
```

Commit packet: this file only, baseline `2140859b1`, research-only, independent
reviews CLEAN within the bounded scope above. Suggested checkpoint: `research: isolate Catch image later-lower and ownership invariants`.
Shared task/theory/index and original A/B status remain primary-owned.
