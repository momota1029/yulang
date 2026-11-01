# R218 — what the original source model supplies for annotation meaning

Status: **source-input audit complete; original annotation reconstruction and
parent application remain open.** The result is a conditional input-gap
finding, not a counterexample to Yulang's actual annotation semantics. The
original `InferenceSoundness`, quantifiers, `supported` predicate, and adopted
effect-hygiene policy are unchanged.

## Exact source path

At baseline `yulang3/ef1873b5e9507192bc97fcdcbb1074eaae70f2e4`, the original
Lean syntax declares `Annotation := Nat`. `Formal` carries an optional ID and
the source-selected `outerComputation` bit. In
`OriginalSourceGeneration.sourceRules`, the Lambda clause builds the formal
context and places only `formal.annotation` and `formal.entry` on the
`sourceFormalRole` atom. It does not inspect an annotation tree or a signature
table. The same syntax module says IDs refer to resolved tables, but no such
table or resolver is a field of the source syntax, the original source
`Environment`, or the source-rule construction. This does not rule out a table
captured by a particular `Kernel` or `supported` predicate; the missing
obligation is the authenticated law connecting such a table to Lambda generation
and source typing.

There is an adjacent typed readout in
`OriginalSourceRecordBoundary.Declarations.annotation : Annotation →
Option (Ty Atom depth)`. `compileOwner` uses this field as the target of a
recorded annotation boundary cast. This is a supplied readout field: the
module does not construct it from a Lambda formal, connect its result to
`sourceFormalRole`, or prove that its rows have the owner/port meaning required
by formal inference for every supported source. It cannot by itself serve as
the missing source-to-role law.

`YulangClosure.OriginalSource.Environment` in
`OriginalSourceGeneration.lean:536` contains values, publications, names,
frames and an origin declaration; it has no annotation signature.
`SourceAssignment` similarly contains event, endpoint readouts and bindings,
but no annotation declaration map. `Kernel.atom` supplies the meaning of
`sourceFormalRole`; a particular kernel or support predicate could capture a
fixed table, but the inspected source/generation cone constructs no authenticated
annotation readout or law connecting one to Lambda generation and source typing.
`SourceProblem.supported : S → Prop` is generic and imposes no syntax-only
restriction. This audit found no attached law connecting the inspected original
annotation input to the supplied formal-role meaning. `Build` compiles the same
atom, and `Satisfies` interprets it using that same kernel, so this compilation
bridge does not independently derive the atom from source annotation data.

R208's `StaticAnnotationConstraintInterpretation.AnnotationEnvironment` is an
explicit `Nat → Option ResolvedAnnotation`, and the module describes this as
resolved source data. It provides a plausible place to model such a table,
but its comment explicitly leaves connection to the Rust parser open. In the
inspected original source model it is a separate candidate interpretation,
not an equation already consumed by Lambda generation.

## Conditional non-identifiability

Fix one original Lambda source with `formal.annotation = some 7`, the same
site, entry, pattern, body and scope. If the available input is only that
source syntax, two external readout maps can agree on every source field but
map ID 7 to different trees, for example:

```text
readout A: 7 ↦ int -> int
readout B: 7 ↦ int -> [E] int
```

The source rule generated from the fixed Lambda is identical in both cases;
the source syntax does not select which result-effect row is intended. This is
a conditional representation collision across possible external readouts.
It does **not** establish that two legal Yulang programs with the same
resolved annotation ID have different meanings, nor that the actual parser or
resolver permits either map independently. An authenticated original resolver
table and its source law would falsify this input-gap conclusion.

The row-owner discriminator remains distinct from this ID ambiguity. Frozen
Oracle `main` commit `a58eefc31e22141574b6f20c6a5748151c6d79f1` builds
`TypeArrow`'s `arg_eff` from the arrow's `TypeRow`, separately from a prefix
`Effectful` wrapper on its parameter. For `([E] int) -> int`, Oracle builds
`param = Effectful(E, Int)` and `arg_eff = None`; value-bound lowering erases
the wrapper. Current HIR stores the prefix row on the Function argument node,
and the candidate consumes that field as the argument-effect port. A faithful
four-port mapping must preserve the wrapper and arrow-row owners separately.
This is R217's existing frozen-Oracle finding; the complementary audit did not
independently inspect the frozen commit or run a second probe.

## Parent application and remaining obligation

No theorem or equation in this audit proves the original `sourceFormalRole`
premise from the generated constraints. The audit therefore applies to the
unchanged Lambda induction edge only as an exact missing input: a source-owned
declaration relation that resolves annotation ID, lexical/type scope,
complete recursive type/effect tree and row owners, then connects that same
resolved result to both generation and declarative source typing. The relation
also needs coverage for the unchanged `supported` domain. A lookup hypothesis
or an arbitrary `Kernel.atom` instance restates the gap rather than closing it.

Parent delta remains 0; roots remain 0/4 and packages 0/5. Effect-hygiene
theorem delta remains 0. No claim of semantic impossibility is made. The next
proof packet depends on locating or defining the authenticated original
resolver/data boundary; a new source field or language rule would require the
normal semantic review and approval gate.

## Lean construction and verification

`YulangClosure.OriginalAnnotationReconstructionR218` imports the unchanged
`OriginalSourceSyntax` and constructs a concrete Lambda with annotation ID 7
and Value entry. Its `AnnotationTree` retains an Effectful wrapper inside the
argument value separately from the Function's argument and result arrow rows.
Two explicitly external readout functions choose
`([E] int) -> int` and `int -> [E] int` for that same ID. The module proves the
source/formal is unchanged, both row-owner equations, the trees/readouts differ,
and no one source-only resolver can agree with both. The two readouts are
counterfactual interface inputs; the module does not assert either is the
original Yulang resolver.

The module SHA-256 is
`757e1aba95e32761360676facdab27ca11b34b4e1b986c8b0f1479ee33a604e6`.
Pinned native Lake and Lean identify Lake `5.0.0-src+eb6cafb` and Lean
`4.35.0` (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`). The first registered
leaf checker attempt failed before build: under its inherited
`RLIMIT_AS=1 GiB`, native Lake aborted creating a thread (exit `-6`, 24,256
KiB maximum RSS). The leaf stopped; the primary then took the cache lease.
Primary command:

```sh
LEAN_NUM_THREADS=1 python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py \
  --module YulangClosure.OriginalAnnotationReconstructionR218 \
  --theorem YulangClosure.OriginalAnnotationReconstructionR218.original_lambda_formal_unchanged \
  --theorem YulangClosure.OriginalAnnotationReconstructionR218.external_readouts_preserve_row_ownership \
  --theorem YulangClosure.OriginalAnnotationReconstructionR218.annotation_trees_distinct \
  --theorem YulangClosure.OriginalAnnotationReconstructionR218.same_annotation_id_distinct_external_readouts \
  --theorem YulangClosure.OriginalAnnotationReconstructionR218.conditional_no_common_source_resolver \
  --theorem YulangClosure.OriginalAnnotationReconstructionR218.no_source_resolver_agrees_with_both_external_readouts \
  --timeout 120 \
  --lake /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake
```

The primary invocation passed (exit 0): the R218 module built in three Lake
jobs; all six theorem types printed, and each `#print axioms` audit reported
that the theorem did not depend on any axioms. The helper's stated boundary
applies: this checks declarations under their printed hypotheses, not source
correspondence or the parent theorem. The failed child log is
`/tmp/yulang-r218-lean-check.log`; its writes and process ended before the
primary verification. No Rust command, test, new environment, package update,
or change to the shared import surface occurred. The existing project cache
was reused.

## Evidence pins and limits

```text
OriginalSourceSyntax.lean                    3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1
OriginalSourceGeneration.lean                126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef
OriginalSourceInterpretation.lean            feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef
OriginalSourceEnvironment.lean                0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132
OriginalSourceRecordBoundary.lean             c7889284745ebd23ec300cf3e4de0a8f7ffc4546a9af2eccf5df76d071a0dd1a
StaticAnnotationConstraintInterpretation.lean 1829ee637ab5cf3254e220e4c0fc1306f248499f087baa779287b947c67018c9
source_annotation.rs                          409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f
candidate_effect.rs                           4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15
```

The Rust hashes and frozen Oracle equations above are inherited from R217;
this audit did not inspect current Rust behavior or rerun its Oracle source
review. The complementary read-only source audit inspected the listed Lean
syntax, generation and interpretation owners and found no resolver law. It
proposed the conditional collision and named an explicit falsifier. Fresh
independent review is required before treating this report as an adjudicated
source-model finding.
