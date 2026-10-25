# R28 represented-judgment term substitution — r1

Status: primary admission candidate; no worker launched until this contract and
current state are committed. Claim class: constructive Lean intermediate lemma,
not the full-paper theorem or a semantic approval.

## Fixed goal and source claim

The parent is the full simultaneous term/type/name substitution lemma in
`docs/yulang-operational-type-safety-ja.tex:953–977`; the parent remains OPEN.
This packet takes only its term-substitution component over the six judgments
currently represented in `PaperExecutionSyntax.lean`. For arbitrary declaration
table `D`, graph environment `Xi`, source term environment `Gamma`, target term
environment `Gamma'`, and a simultaneous replacement vector `rho` whose values
are typed in `Gamma'` at the corresponding types in `Gamma`, define an actual
capture-avoiding syntactic operation and prove preservation of the original
judgment indices and result type for:

- `PaperValueTyped`
- `ValuesTyped`
- `ValuesAllTyped`
- `RecordPayloadsTyped`
- `PaperComputationTyped`
- `PaperContinuationTyped`

Binder lifting must be explicit in executable Lean definitions: under term
binders, prepend the bound variable and shift free replacement values; under a
`forall`/`typeAbstraction`, shift replacement value types through the type
binder using the existing shared type substitution machinery. Recursive/formal
substitution is simultaneous; do not implement it as a sequence of single
substitutions. Use R21's reverse-cons convention only if its actual definition
is required, and prove the exact order used here.

Raw syntax includes forms without represented typing constructors. Do not
silently map unsupported forms to themselves and report success. A partial
operation (for example `Option`) may reject such forms. Prove that every
represented typing derivation yields a successful substitution result and that
its result is typed at the unchanged result type. Preserve all six original
judgment indices. A successful derivation theorem may be factored into
constructive success plus typing preservation.

## Decisive falsifiers and required application

1. A lambda/continuation/pattern binder case where a free replacement
   `variable 0` is captured if lifting fails.
2. Two recursive formals whose replacements distinguish simultaneous
   substitution from sequential substitution and from reversed list order.
3. A type abstraction where replacement values are not type-shifted under the
   shared `D/Xi` binder.
4. Unsupported raw constructors cannot produce an `isSome` success result.

Apply the theorem to the R27 fresh graph-reference case: when recursive formal
variables are replaced by fresh graph references, use R27's six exact
lookup-preserving graph weakening lemmas to transport replacement typing across
the fresh graph extension, then apply the simultaneous term-substitution
result. This is an intermediate represented-judgment application only; it does
not type allocated recursive right-hand sides or prove graph heap/guardedness.

## Exact scope and open premises

No changes to paper semantics, source domain, existing partial typing relations,
R27 artifacts, dependency files, lake configuration, root imports, Rust code or
production compiler. No promotion of the manuscript as an approved language
specification. Omitted paper rules (including variants/nominals where absent,
handlers/mappers, graph allocation/recursive environments, primitive/pattern
judgments and registered template-body typing) remain omitted and OPEN. Full
term/type/name substitution, operation/owner correspondence, heap well-typedness,
guarded cycles, inference/executor, original A/B, source/native and production
remain OPEN.

Implementation lane: `NO_SAFE_CODE_SLICE` for this packet. Two inspected owners:
`PaperExecutionSyntax.lean` is the raw syntax/type-map layer and contains no
term-substitution operation; the compiler/runtime path has no approved
source-to-this-partial-judgment bridge. Adding production syntax or behavior
would exceed this proof-only claim and has no source-correspondence evidence.

## Frozen baseline, authority and exact dependencies

Baseline commit: `c0fe13db1f705eb71e7eb440ba6f31458ca90b51` on
`research/simple-sub-intrusion`. Fresh isolated checkout:
`/tmp/yulang-r28-term-substitution`. R27 is an accepted frozen intermediate
artifact, not integrated into main sources; copy its exact source into the
isolated R28 checkout as a read-only dependency before launch.

- Manuscript `docs/yulang-operational-type-safety-ja.tex`:
  `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`
- `PaperExecutionSyntax.lean`:
  `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`
- `PaperExecutionBinderLaws.lean`:
  `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`
- `PaperExecutionTypingSubstitution.lean`:
  `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`
- `PaperTypeFormation.lean`:
  `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `PaperTypeSubstitution.lean`:
  `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `DeclSubst.lean`:
  `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`
- frozen R27 graph weakening module (read-only isolated dependency):
  `b0ff39ad89fcb83559cca3147ae55fa7e7f6c31c1b130ec9cd7608e33d1f696e`
- R27 independent review:
  `65cae0d25f01e51e5330946234d105d19761a2d431424048c29689c14603b60a`
- R26 primary adjudication (records failed verification; no imported candidate):
  `6551f28f5da2bfff5905990c98abeac95b19f242b1ad6e27bdf370f27c3c25f1`
- pinned `lean-toolchain`:
  `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`
- `lakefile.toml`:
  `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`
- `lake-manifest.json`:
  `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`

No R26 cache or candidate may be read or imported. The primary verifies every
hash and pinned toolchain before launch and after handoff. Worker gets no Git,
network/dependency, test, default/full build, semantic, source, integration or
production authority.

## Exact leases, lane, review and checks

One fresh registered `lean_prover` leaf, no descendants, owns only these paths
in the isolated checkout:

- `notes/theory/lean/YulangClosure/PaperTermSubstitution.lean` (new)
- `notes/theory/lean/.lake/R28Audit.lean` (new)
- `notes/theory/lean/.lake/build` (dedicated cache)
- `tasks/agent-loop/inbox/paper-term-substitution-r28-worker-checks.txt` (new)
- `tasks/agent-loop/inbox/paper-term-substitution-r28.md` (new handoff)

The primary owns `tasks/agent-loop/current.json`, this sprint contract,
`tasks/agent-loop/inbox/paper-term-substitution-r28-primary-verification.txt`,
Git and isolated-checkout setup. After worker STOP and primary verification, a
fresh non-author M1 reviewer may write only
`tasks/agent-loop/inbox/paper-term-substitution-r28-review.md`; no checker or
cache access.

Use one registered constructive proof lane; no parallel implementation lane.
Review specifically the executable substitution order, binder lifting,
forall/type shifting, actual `Option` failure behavior, exact theorem types and
R27 application. A reviewer must independently inspect constructors and source
correspondence rather than rerun checker output.

Pinned serial commands from `notes/theory/lean`:

    lake build +YulangClosure.PaperTermSubstitution
    lake env lean -j1 -M1024 .lake/R28Audit.lean

The audit prints complete types and `#print axioms` for all six preservation
results, substitution success/composition core lemmas, binder-lifting and
forall-shift lemmas, unsupported-form falsifier, simultaneous-order falsifier,
and the R27 fresh-reference application. Reject `sorryAx`, project axioms,
`Classical.choice`, or unsupported axioms. Scan the changed dependency cone for
holes and checker bypasses. No full/default build or tests.

## Resource, runtime and stop conditions

Total envelope: 1800 active seconds, 14 literal Lean/Lake invocations,
180 checker seconds. Worker: at most 10 invocations, 120 checker seconds and
900 active seconds; primary: at most 4 invocations, 60 checker seconds and 600
active seconds, including two pinned-version queries plus the exact focused
build and audit; reviewer: at most 300 active seconds, zero checker
invocations. Every version query counts. Resolve native Lake read-only with
`elan which lake`; no unresolved elan proxy invocation. Use `LEAN_NUM_THREADS=1`
and project `-j1 -M1024`. Only one heavy checker process at once. No transfer of
R25–R27 unused budget. Preserve all 8 UNKNOWN historical reservations as
quarantined; global agent count stays below 12.

Stop on three failed worker checker invocations, first failed primary final
check, any source/claim ambiguity, unsupported-case leak, budget edge, changed
input/authority/lease, missing cessation evidence, or session end. Do not retry
an unchanged command. Freeze every output and record actual invocation/runtime,
model/effort observations (UNKNOWN if unavailable), cache hash, descendants and
writes-stopped receipt before review. The artifact remains an intermediate
research result unless the primary adjudicates it; it does not close the parent.
