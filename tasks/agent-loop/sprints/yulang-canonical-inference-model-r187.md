# R187 revision 4 — canonical mathematical inference model

Revision 4 adds one exact source-owned constructor definition reported before
any content read. Revisions 2–4 add only delegated mathematical authorities.
The objective, method, output leases and 2400-second constructor grant are
unchanged; no grant reset.

Status: **ACTIVE bounded model-construction packet**. Baseline is commit
`41eb4bc24a82baa5ff203b48394041df76c848a7` in the existing checkout. Goal:
Yulang's mathematical type/effect inference guarantee against original source
rules. Rust/runtime correspondence is excluded.

## Why this packet precedes another soundness proof

The unchanged parent is `YulangClosure.SourceProblem.InferenceSoundness`,
`Contracts.lean:128–130`:

```text
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

R185 and independently reviewed R186 both leave the same prerequisite open:
there is no complete canonical mathematical instance of actual generation
and solving to which the all-constructor induction can be applied. R186 is
closed incomplete; its conditional App frame algebra is supporting evidence,
not a reason to retry its failed Lean module.

First freeze one explicit candidate model and its correspondence to accepted
mathematical authorities. This packet does **not** claim the parent theorem,
principality, or termination. It prepares the exact object those distinct
proofs must consume, so we do not add more conditional local lemmas.

## Fixed construction domain and content

Construct a single finite mathematical model for the original supported
source grammar, not a restricted fragment. Its specification must include:

1. A canonical constraint grammar and an independently defined
   type/effect denotation for assignments. Preserve whole indexed/joint Call
   data, contexts, providers, events, incidences, and effect permissions where
   the accepted rules require them; do not infer a relation from scalar port
   projections alone.
2. Exact generation equations for every accepted expression, pattern and
   statement constructor, with all binder/telescope scopes and conditional
   source clauses visible.
3. Mathematical state and transition definitions for constraint
   accumulation, propagation, levels, extrusion, intrusion, and
   generalization. State precisely whether each is part of generation or a
   separate transition, and how its obligations reach terminal solving.
4. One assignment/telescope interpretation and the exact transport invariant
   from generated constraints through those phases to the same-scoped source
   clauses. Keep the source judgment, generation, solving and scoped result
   independently defined.

Use `sourceRules`/`Build` only as the source-side target. Do not identify it
with abstract `generates`/`solves` without deriving that correspondence. No
uninterpreted admission predicate, unproved `LocalLaws`, desired-typing
assumption, independently chosen witness, or changed source rule may complete
the candidate model.

## Required outcome and parent metric

Return exactly one of these, with governing locators and a direct authority
map:

**A. Complete candidate model.** All definitions and constructor equations
exist for the accepted domain; each equation is independently matched to an
authoritative mathematical rule. A fresh reviewer accepts that correspondence.
This closes only the named prerequisite “actual generation represented by
one canonical independent constraint object.” The same-assignment soundness
induction and direct parent application remain OPEN until a later proof packet.

**B. Exact authority boundary.** Name the first required equation not fixed by
the accepted mathematical sources, quote its exact governing locators, and
show the conservative construction attempt plus the observably distinct
consequences of each permitted reading. Distinguish a missing formal
definition from a semantic choice; do not label a missing Lean declaration
underdetermination.

A syntax inventory, another list of App premises, a schematic readout, or a
set of conditional lemmas is neither outcome. Progress is the prerequisite
closed by A or the precise authority boundary established by B, not theorem
counts. After A, the next admitted packet is the all-constructor
same-assignment soundness proof over this exact model; principality and
termination remain separate obligations.

## Exact inputs, outputs and resources

The primary authenticated the 24 direct mathematical inputs listed in
`tasks/agent-loop/sprints/simple-sub-inference-soundness-r184-v4.md` (that
contract SHA-256 `518ee36cf16c5266a9cd7aabfec25eb7e42ceba9c9e6f7e9ce5970873d07b640`);
all 24 file hashes match. The 3 additional direct source owners in R186 v3
also match. Use those owners only. The R186 v3 contract
(`7bad077bbb3238b301e9c62f11f2303c5b73d118c01a84b622a3e849f538a7fa`),
R185 outcome (`f181a23577bf4d09988218eb9133268b5d82bbad4f68d1023d5046bc0633b60e`),
R186 reviewed outcome (`511727da5477e3a3616c6a03238b53ba70a12c6701a5443b411e2ded9f60475b`)
and parent dependency map
(`bdb83b830072e78c244cd2da6215e7ba5f2468df93afa5a3208c2a2419c08fe0`) are
authenticated navigation/evidence inputs. Authenticate every direct source
hash before reading it. Revision 2 additionally admits these three exact
direct mathematical owners, identified as delegated authorities of the
already-pinned top-level/source definitions:

- `notes/design/2026-10-12-intrusion-value-type-association.md` —
  `531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89`
- `notes/design/2026-10-05-source-contracts-and-common-allowance.md` —
  `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186`
- `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` —
  `9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3`

The primary authenticated these three hashes without reading their contents;
the constructor must re-authenticate each before its first content read. If a
necessary owner falls outside the combined admitted sets, stop and return its
exact path; the primary must pin it before any read.

Revision 3 additionally admits these exact operation/transport owners, which
the admitted intrusion association and Term source select for the actual
transition and its preservation obligation:

- `notes/design/2026-10-10-parent-copy-scc-intrusion.md` —
  `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b`
- `notes/design/2026-10-24-birth-level-scc-intrusion.md` —
  `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`
- `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` —
  `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`

The primary authenticated these hashes before reading their contents. On
first use, the constructor must re-authenticate all three and read them in
this order: operation state/guards/copying/SCC equations; later birth-level
decision and precedence; then the §4 preservation proof, only after matching
its hypotheses to the current transition. Do not follow further links
automatically. A newly required declaration owner returns to the primary.

Revision 4 additionally admits this exact source-owned constructor definition,
which the admitted source-Generalize construction §2 names for primitive/Call
port, provenance and license formation:

- `notes/design/2026-10-08-native-signature-formation-definition.md` —
  `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9`

The primary authenticated this hash before any content read. Re-authenticate
before reading. Limit inspection to the authority/status statements and exact
definitions required for the canonical source constructor/Call denotation.
Do not infer an exhaustive interpretation or a proved solver bridge from this
document, and do not follow further links automatically. Any further required
owner returns to the primary.

One `researcher` owns only these exact outputs for at most 2400 seconds:

- `notes/theory/2026-11-02-yulang-canonical-inference-model-r187.md`
- `tasks/agent-loop/inbox/yulang-canonical-inference-model-r187-proof.md`

Then one fresh independent mathematical/source `spec_auditor` review is
reserved for at most 600 seconds. Total R187 envelope: 3000 seconds; each
grant is charged when issued and is not reset. No proof-worker Lean check,
build, test, Rust/Cargo/runtime work, environment/cache, generated scratch,
root import edit, or production change is authorized. Existing Lean results
may be cited only under their exact pinned hypotheses; this packet is a
mathematical specification, not a kernel-checked theorem.

Stop at the grant, an input hash mismatch, absent semantic authority, a source
scope change, or the first exact unresolved defining equation. Freeze bytes
and report hashes, authors, coverage, exact resource use, and which named
parent prerequisite changed. No semantic choice is silently made.
