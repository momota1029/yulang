# Exact two-use source: parser, binder and candidate construction bridge

Date: 2026-10-12
Status: reviewed bounded source construction derivation plus primary-owned
executable observation. No semantic admission or parent theorem closure is
claimed.
Baseline: `2b4dcced1a7fe55212c79ce8b61b9a40c893def3`, branch
`research/simple-sub-intrusion`.
Original Simple-sub pin: `9bae772624c23b52a93c1b226157e16898b4d9db`;
no Oracle execution or new native derivation.
Producer: `/root/two_use_source_bridge`, leaf only.
Exclusive lease: this file. Budget: one reasoning pass, at most 30 minutes;
zero child-owned parser, test, build or inference processes.

## 1. Frozen statement and authority

Take exactly the first Yulang fence payload in the frozen
[two-use witness](../progress/2026-10-12-intrusion-admitted-two-use-witness.md),
including its terminal LF:

```yulang
my answer = {
  my f x = {
    my g y = { my drop z = y; drop (f y) };
    my first: int = g 0;
    g ()
  };
  f
}
```

This is 116 UTF-8 bytes; SHA-256
`bffcb9619342e28de83b54ff39871ccfe5be55f1791814f652af91d2dcebeaa2`.
Whitespace, braces, semicolons, application parentheses and annotation are
part of the input. No replacement source is used.

Required conclusion: this text reaches the current **opt-in** parser →
LocalSource → candidate generation route, with its four actual applications,
distinct source binders and the witness's scopes/levels. The construction
statement ranges over consistent `ModuleIdentity::source_root` identities
and fresh immutable artifacts for this input, `SyntaxEnvironment::empty()`
and `SemanticImports::empty()`, with the candidate feature enabled and normal
finite allocation available. Artifact brands and numeric ordinals are local
to each constructed artifact; this is not a statement about arbitrary import
or operator environments. No hypothesis assumes recovery-free CST admission;
that point is supplied by the parser trace and the exact executable observation
below. Resource exhaustion remains outside this finite successful construction
instance under the top-level principles.

The original recursive f binder, g binder, discarded-call wrapper drop, unused
first binding, x/y/z formals and all Name occurrences remain in scope. The
required source fragment is not reduced by dropping an unused binder or
substituting its returned value.

Governing authority: [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5; [local self-recursion](../design/2026-10-10-local-self-recursive-binding.md),
Selected source behavior and Proposed source-to-solver seam;
[parent/copy operation](../design/2026-10-10-parent-copy-scc-intrusion.md),
Value-reference SCC clarification, Nested Apply membership and Definition-root
Value ownership; [occurrence qualification](../design/2026-10-12-intrusion-value-type-association.md),
Approved extrusion-event qualification and Implementation and proof boundary;
[Source Generalize](../design/2026-10-08-source-generalize-definition.md) §§2–3,
selecting construction §§3–5 of its linked proof. The
[original occurrence obligation](2026-10-12-extrusion-occurrence-intrusion-proof.md)
§§1,5–7 keeps its original domain and quantifiers.

Exclusions: this bridge does not prove original source typing/admission,
complete Call, actual Source Generalize fixed/template classification, an
extrusion's origin/receiving Values, occurrence-qualified equality applicability,
equality activation/replay, preservation, required principality, soundness,
effect hygiene or F5 replacement. In particular the carrier's Q owner is not
a certificate of the conceptual G/F event endpoints. The parent A/B theorem
remains OPEN.

Claim class: **bounded source/implementation characterization**, with a direct
static construction derivation and one exact-input executable observation.
This producer does not certify a general theorem or independent review.

## 2. Actual syntax constructors, including separators and applications

`full_parse.rs::parse_file` (lines 317–343) uses the supplied source allocation,
its own scanned header and the selected operator environment, then calls
`cursor.rs::parse_root` (85–98). `header.rs::discover_header_with_cursor` stops
at the initial ordinary `my answer`; there is no source header operator/import.
`operator_compilation.rs::effective_full_parse_operators` therefore uses the
empty selected table. `root_statement.rs::root_statement_sequence` (112–249)
dispatches the initial statement via the actual binding classifier rather
than a synthetic CST.

The finite lexer vocabulary is supplied by `lexer.rs::scan_statement_keyword`
(711–723), `scan_identifier` (685–703), `scan_integer` (891–906), punctuation
(908–930), pattern colon (1013–1024) and declaration equals (1060–1079).
`current_item.rs::scan_current_item` (69–178) retains ordinary horizontal/newline
leading parts and reaches unfenced EOF without creating a fence boundary.

At each `my`, `statement.rs::classify_statement_item_lexical` (423–466) selects
Binding; `binding.rs::binding_follower_normalized` (83–124) accepts these
ordinary names. `binding_statement_normalized` (185–256) constructs exactly
BindingStatement → BindingHeader/BindingBody. `binding_target_normalized`
adds PATTERN_STOP_EQUALS; `pattern/mod.rs`'s IdentifierPattern branch
(735 onward) gives answer/f/g/drop/first. Its ML application branch
(1085–1142) gives exactly one bare formal for f/g/drop. The colon branch
(1060–1084) gives first's PatternTypeAnnotation; `pattern_type_annotation_rhs_normalized`
(1294–1337) passes `TypeOuterBoundary::EQUALS`, so `int` is the type expression
and the following `=` remains the binding separator, not part of that type.
`type_expr/mod.rs` (875–890,1227 onward) emits the Identifier and returns that
outer boundary. Each RHS begins on the same line as its `=`, taking the inline
BindingBody branch (`binding.rs:317–364`), which constructs one OperatorChain.

Every `{` takes `operator_chain.rs`'s LBrace branch (346 onward) to
`statement.rs::braced_statement_block_normalized` (562–607). Its actual
statement sequence (610–698) and explicit separator owner (1121–1142) give:

| Block | Statement children, in order | Separators |
| --- | --- | --- |
| answer body | f binding; final f expression | f's `;`, then final newline before `}` |
| f body | g binding; first binding; final `g ()` expression | g's `;`, first's `;`, final newline before `}` |
| g body | drop binding; final `drop (f y)` expression | drop's `;` |

The incoming/body baselines are respectively 0/2, 2/4 and 4/4, using
`observation.rs::delimited_baseline` (92–96). Explicit semicolons consume
following ordinary leading trivia once; closing newlines satisfy
`indentation <= baseline` (98–100) and yield trailing BlockStatementSeparator
nodes, whose empty child list is accepted by the LocalSource block walker.
Matched `}` uses the successful terminal branch (899–912). No empty required
statement is inserted. Trailing separators are preserved rather than assumed
absent.

`f y`, `drop (f y)`, `g 0` and `g ()` each contain an ordinary horizontal gap.
Thus `tail_normalized` does not select the no-gap CallTail branch
(`operator_chain.rs:638–659`); it selects `is_ml_argument` (758–768) and
`ml_argument` (782–827), constructing one MlArgument child of each original
OperatorChain. This distinction matters: `g ()` is an empty
ParenthesizedExpression inside MlArgument, not a no-gap `g()` CallTail.
`parenthesized_nud_normalized`/`delimited_items_normalized`
(`expression/delimited.rs:48–186`) constructs `()` without an expression
child and `(f y)` with one OperatorChain child. None has a comma, foreign
close, missing close or ExpressionDelimitedSeparator.

The exact primary-owned run in §5 observed no structural recoveries and no
syntax diagnostics. Recovery-free construction is an obtained fact for this
input; it is not an initial source-admission assumption.

## 3. LocalSource ownership and binder derivation

The actual API is `yu_hir::shadow::lower_module_with_local_source`
(`shadow.rs:38–44`), calling `module.rs:911–920`. That call enables
`local_source`, registers exact parse-owned source keys and uses
`lower_module_with_counters`. `plan_root` (1271–1326) admits the plain answer
header. The one definition-root constructor (988 onward) mints Q for answer.
`lower_plan` (1411–1428) calls `local_source::form` and stores its returned
carrier under that same Q before the ordinary body projection.

`local_source.rs::body` (223–255) checks the exact MyKw/Pattern/Equals header
and sole OperatorChain body. `form` (257–388) rejects recovery and forms this
carrier by its work stack. The block scanner (698–828) allocates every local
header in that block before scheduling its initializers. This gives:

| Binder | Constructed identity | Exact relevant resolutions |
| --- | --- | --- |
| f | HirLocalId(Q,0) | recursive f in `f y`; final outer f |
| g | HirLocalId(Q,1) | g in both consumers |
| first | HirLocalId(Q,2) | no Name use |
| drop | HirLocalId(Q,3) | drop in its block's final expression |
| x | HirParameterId(Q,0), owner f | unused |
| y | HirParameterId(Q,1), owner g | drop body y; argument y of `f y` |
| z | HirParameterId(Q,2), owner drop | unused |

These are constructor ordinals, not a proof based on matching spellings or
solver row names. `record_local`/`record_parameter` retain the original binder
source keys (745–787). Initializer work temporarily installs each parameterized
local's own identity, then its formal, before entering the body; Publish
restores the guard and installs the local for later siblings (329–374).
The latest lexical entry is consumed by the actual IdentifierExpression rule
(636–663). While drop's body is formed, y's entry still resolves to g's formal;
z does not retarget it. When `f y` is formed, f's self identity remains in the
outer initializer scope. Both g uses occur after g's Publish, and final f
after f's Publish. No Name here falls back to the module namespace.

The exact expression-slot trace is below. E(n) denotes LocalSourceScope::Expression
for carrier ordinal n; LI denotes LocalInitializer. Carrier scopes and inference
levels are distinct fields.

| Ordinal | Form/operands | Scope | Candidate level |
| --- | --- | --- | --- |
| 0 | answer Block: binding 0, final 1 | Definition(Q) | 1 |
| 1 | Name f → local 0 | E(0) | 1 |
| 2 | Lambda x, body 3; f initializer | LI(f) | 2 |
| 3 | f Block: bindings 1,2, final 4 | Parameter(x) | 2 |
| 4 | Apply(18,19), `g ()` | E(3) | 2 |
| 5 | Lambda y, body 7; g initializer | LI(g) | 3 |
| 6 | Apply(16,17), `g 0`; first initializer | LI(first) | 3 |
| 7 | g Block: binding 3, final 8 | Parameter(y) | 3 |
| 8 | Apply(11,12), `drop (f y)` | E(7) | 3 |
| 9 | Lambda z, body 10; drop initializer | LI(drop) | 4 |
| 10 | Name y → parameter 1 | Parameter(z) | 4 |
| 11 | Name drop → local 3 | E(7) | 3 |
| 12 | Group, inner 13 | E(7) | 3 |
| 13 | Apply(14,15), `f y` | E(7) | 3 |
| 14 | Name f → local 0 | E(7) | 3 |
| 15 | Name y → parameter 1 | E(7) | 3 |
| 16 | Name g → local 1 | LI(first) | 3 |
| 17 | Integer `0` | LI(first) | 3 |
| 18 | Name g → local 1 | E(3) | 2 |
| 19 | Unit, from `()` | E(3) | 2 |

Apply/Group slot constructors are `local_source.rs:489–578,665–692`.
`set` (454–475) mints a new HirOccurrenceId and records its exact SourceNodeKey
on every expression; separate Apply/Name/Group occurrences do not become one
identity. Slot 12 remains a Group facade between wrapper argument and slot 13.
There are exactly 20 carrier expressions and four local bindings. All depth
checks are below the existing 128 bound; no new source restriction is imposed.

## 4. Exact candidate producer and consumers

With `shadow-apply-candidate` enabled, Cargo selects `shadow-f5`, which selects
`yu-hir/shadow`. `CandidateInference::solve` (`shadow_apply.rs:78–115`) obtains
the artifact-owned carrier, runs `candidate_source::preflight`, then calls
`ConstraintBatch::collect_candidate_mode(hir,true,true)`. Preflight
(`candidate_source.rs:82–138`) accepts these resolved Names, bare formals and
the primitive int annotation. `source_annotation.rs:307–334,399–421` forms
first's authentic Int annotation, with no effect row.

There is a real ordinary-HIR seam here: `module.rs::lower_body` calls
`lower_simple_chain` (1564–1696,2087–2110), whose `direct_atom` test
(`yu-hir/src/lib.rs:184–209`) excludes the brace block. It emits an owned
UnsupportedExpression placeholder, rather than lowering this carrier into
ordinary ResolvedExpr blocks. `retain_placeholder_errors`
(`candidate_source.rs:143–159`) explicitly permits that owned placeholder;
the solve guard accepts only that error kind and preserves unrelated errors.
This is how the current private route enters generation; it is not evidence
of shipping ordinary HIR admission.

`yu-solver/src/lib.rs:1124–1136` selects the carrier and calls
`emit_candidate_source` (candidate_source.rs:168 onward). Work::Visit starts
at level 1 (250), increments only for block initializers (288–299), and keeps
Lambda bodies at the same level (270–286). Work::Initializer/Install retains
the open endpoint while the initializer is active, then installs at the parent
boundary (301–328). Applying those actual transitions gives exactly the levels
in §3 and publication boundaries f=1, g=2, first=2, drop=3.

During slot 14's f lookup, active_initializers contains f and g; the constructor
emits Action::Link to f's original initializer endpoint (381–389). During both
g lookups, g is installed, so each emits its own Action::Local at its actual
use level. The actions are executed by `execute_candidate_action` (657 onward),
which uses `admit_candidate_value_link` for Link and the local-use route for
Local. This identifies consumers without claiming a source Generalize law.

The Work stack visits a Call's callee, then its argument, then finishes the
Apply. Therefore `ApplySourceInput` records are constructed in this order
(394–410):

| Call input | Carrier Apply | Callee/argument | Level |
| --- | --- | --- | --- |
| 0 | 13: `f y` | Name f/local 0; Name y/parameter 1 | 3 |
| 1 | 8: `drop (f y)` | Name drop/local 3; Group 12 | 3 |
| 2 | 6: `g 0` | Name g/local 1; Integer 17 | 3 |
| 3 | 4: `g ()` | Name g/local 1; Unit 19 | 2 |

Each input retains original carrier indices, endpoints, argument/callee effects,
result/application effect, occurrence/cause and level. Each `owner` is Q.
`source_call`/`source_call_count` (`shadow_apply.rs:190–193`) expose these records
through the original HIR/store, rather than reconstructing them from printed
types. None of these callees is a formal Name; no formal-callee supplier is
invented. Pending original Call suppliers remain in `candidate_call.rs`.
Generated requests and actual record consumers establish this route's
correspondence; stored requests alone are not proofs of complete invocation
or semantic replay.

## 5. Primary-owned executable evidence and exact-input correction

The verification owner was the primary, not this leaf. The primary temporarily
created `crates/yu-solver/tests/research_intrusion_two_use_source_probe.rs` and
ran:

```sh
CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-apply-candidate --test research_intrusion_two_use_source_probe -- --exact --nocapture --test-threads=1
```

The first run used 4/8 spaces, so it was not evidence about the frozen 2/4-space
bytes. This leaf checked the probe and reported the mismatch. The primary then
reran the same command with the exact 116-byte fence payload. Corrected probe
SHA-256: `6b86a88ba7a7af3603685d488580dd9e2df99022f93cf7bfc8d6b09c5f026a30`.
The leaf read that corrected source; the literal and both selected empty
environments match §1. The primary reports the corrected run exited 0 with
one test and observed:

* `structural_recoveries=[]` and `syntax_diagnostics=Ok([])`;
* successful LocalSource formation, 20 expressions and the original local/formal
  binder resolutions, including recursive f/local 0 and y/parameter 1;
* four source Call records, carrier ordinals 13/8/6/4 and levels 3/3/3/2;
* successful private candidate construction with `candidate_conflicts=[]`.

The driver prints the recovery/CST carrier/Call observations and catches/prints
lowering or candidate errors. It has no assertions proving those observations:
**the test pass alone is not the evidence**. The primary's inspected output and
this leaf's direct producer/consumer derivation support the stated bounded
construction facts. The corrected probe is temporary and primary-owned; its
removal does not change a compiler dependency. Reproduction uses exactly §1's
source with `parse_file(source.clone(), Arc::new(scan_header(source)),
Arc::new(SyntaxEnvironment::empty()))`, then
`lower_module_with_local_source(ModuleIdentity::source_root(...), &parsed,
SemanticImports::empty())`, followed by `CandidateInference::solve` and the
four source Call observations. No replacement AST or synthetic constraints are
needed.

Every observed Call still lists SourceTypingAndAdmission, ApplicationTypingRule,
CompleteInvocationImage, WholeArgumentProviderCompatibility, GeneralizationAndFreshUseCorrespondence
and related effect/typed-occurrence obligations as unresolved. No test output
is interpreted as original successful typing or Source Generalize publication.
The private no-conflict observation is recorded only to show the call records
were actually exposed by this path.

## 6. Result, remaining boundary and checks

For this exact source, the parser/resolver/LocalSource/candidate-lowering seam
has concrete owner evidence and a matching finite executable observation.
The frozen witness's recovery-free-CST proviso is now supplied for this
construction instance. There is no identified missing parser, resolver,
LocalSource HIR or candidate generation constructor on this exact opt-in route.
Ordinary shipping HIR still has the UnsupportedExpression placeholder described
in §4; this bridge grants no migration authority.

The first remaining **original semantic** premise is still the `f y` whole
inert argument / actual receiver / entry / designated consumer / complete
invocation return law (`candidate_call.rs::PendingCallSupplier`, OriginalGenCall0,
ArgumentReifyAndWholeCarrier and ReceiverDispatchAndCompleteResultFutureInterfaces;
Source Generalize construction §3.1 Call). This packet does not try the same
native conditional proof again or reclassify that parent A/B obligation. Source
publication classification, event endpoints and equality/frame transport
remain distinct subsequent premises. The binder/Call records above preserve
their original incidence; none chooses witnesses independently or equates body
and invocation ports.

Leaf checks: bounded cat/sed/rg owner reads; read-only branch/HEAD/status;
source fence extraction and SHA-256; live dependency bytes compared with the
pinned Git blobs; final whitespace/source/hash integrity. `spec/` does not exist
in this baseline, so no absent specification was inferred. Some broad initial
captures truncated; decisive sections were reread in bounded windows. No
compiler/test/expectation/configuration/rule/question/shared-record file was
written by this leaf, and no Git mutation or delegation occurred.

Resource use: one reasoning lane, lightweight read/hash processes; zero child
tests/builds, zero Oracle runs, zero inference/performance samples by this leaf.
Primary verification: two sequential single-test invocations, one exact-input
sample and one indentation-mismatched preliminary sample, CARGO_BUILD_JOBS=2,
one test thread. The primary reported first-run build 3.11 s and test 0.03 s;
corrected-run timing, peak CPU/RSS and exact worker wall time are unmeasured
here. Requested runtime: registered prover, `gpt-6.1-sol/high`. Observed
effective model/effort: unknown; no Astra or hot-reload claim.

Independent review: `spec_auditor` PASS on the frozen artifact at SHA-256
`10a379db6cd91a9def8ccbd832ae0ae853d08be1305fc35850d249f093028606`. It checked
the exact-source, parser/CST, LocalSource, candidate levels, recursive Link vs
published Local consumers, and four Apply records against owning constructors
and test contracts. It found no overstatement of recovery-free construction as
semantic admission. The reviewer did not independently rerun the primary probe.

Unverified: complete semantic source admission, ordinary HIR/public path, event
certificate and approved Value-reference edges, classification/transport/
generalization, complete Call/effects, all-source preservation, required
principality, soundness and F5.

One next action: use this exact admitted-to-carrier source instance as the
input of the owning original `f y` Call proof; retain its whole argument,
receiver/entry/consumer/invocation premises and the parent gate OPEN.

## 7. Frozen dependency snapshot

All direct dependencies listed below matched the pinned baseline bytes during
this leaf's audit. No dependency was edited by this producer. The temporary
primary-owned probe is recorded separately in §5 and is not a committed
baseline dependency.

```text
653861f60a148cbb1fcddf71b6426f58124f7fe9fbe353be2e2b8ea2ed86d768 notes/progress/2026-10-12-intrusion-admitted-two-use-witness.md
08b963a7e2356a400dcb05b53c6fe6d3a917abe9e0df1582779c5c83858eb4f8 notes/theory/2026-10-12-extrusion-occurrence-intrusion-proof.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b notes/design/2026-10-10-parent-copy-scc-intrusion.md
0063b88d17104f85182439d80360e42f8f99a5af4793eab70640a66f955ede25 notes/design/2026-10-12-intrusion-value-type-association.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895 notes/design/2026-10-10-local-self-recursive-binding.md
24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8 crates/yu-syntax/src/full_parse.rs
f08aae49fcf048ad11890def7ef9cadab56825a63b8d87db44821a792fe9b142 crates/yu-syntax/src/cursor.rs
c6d1dc49625d1687ff0dae8f6808f4c97c3f78398aae3bc061c44b6fc9661626 crates/yu-syntax/src/root_statement.rs
cd3791144704226f67a05ae3d39aff9b42f4380073b3e9f9817951a493bce5ad crates/yu-syntax/src/header.rs
f1a5bd012f064d414d476acbc326c6a9804dc8128bf2e4f1800acb718a7d423b crates/yu-syntax/src/operator_compilation.rs
41efcce2b737a0362484e854a8549bda5f7bf0d2b911499553f1e449c6782a84 crates/yu-syntax/src/lexical/current_item.rs
9a18b24628844e2e5ab1bcc1dc26e05cb14bdb6fca35a3a2d31f45ba5180b3a1 crates/yu-syntax/src/lexical/lexer.rs
730e65947f889ef07014aa003eb846012d5cec6ae1434f77edf1cbd0e7096641 crates/yu-syntax/src/lexical/observation.rs
b6bbeefe6ef5c21e46c34cf97aed96b19703e6b55a1869f6396bc0458f06416b crates/yu-syntax/src/lexical/item.rs
c981a994a11c539256ef34382c4ae154395e5d438371db4959e914df58aa8c7c crates/yu-syntax/src/lexical/expression_item.rs
2570ef138c22c68ce4275e7612d9901a20316c43c1726691baa151e05e92f168 crates/yu-syntax/src/cursor/recovery/emit.rs
eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544 crates/yu-syntax/src/declaration/binding.rs
f61a4928f9982e9885ba726213f1f6a6cef4feb89ebae38c98f629a9bafc4f03 crates/yu-syntax/src/pattern/mod.rs
2e08a49960cd4010ba39641ae509afb7cf59711c1464d3349f5f6db590ebf01f crates/yu-syntax/src/type_expr/mod.rs
cd7b6ccd9e0bf92d90de5a0e9e5cfdede5f38990bacb12d60fff8e9fdf8edc2d crates/yu-syntax/src/expression/operator_chain.rs
2d6f43b2b02a560d7ad1aa76929969908df34fe6d884783b34baa9edc5f81b08 crates/yu-syntax/src/expression/delimited.rs
dc18a26663b4351b774a930bfcc8b343cf0c41651960b49ec2f2c6e744b0e89d crates/yu-syntax/src/statement.rs
51e5fa543cd65ced879a7561e0d602e686a072378cde5ec16a20b4afb875fc0a crates/yu-hir/src/lib.rs
943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5 crates/yu-hir/src/module.rs
687b49061273974fe874a8479a8db91ba24cc77fe92e6d2b96ae46a3626cf9dc crates/yu-hir/src/shadow.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed crates/yu-hir/src/module/local_source.rs
a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb crates/yu-hir/src/module/source_annotation.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94 crates/yu-solver/src/lib.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49 crates/yu-solver/src/candidate_source.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35 crates/yu-solver/src/candidate_call.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411 crates/yu-solver/src/shadow_apply.rs
7a599e95800c67ca4688b0f91917609345a252aae6d2ea6cd0f413eb1c07893c crates/yu-solver/Cargo.toml
a97f52fc6b9e577f23be4160ecdda9693bec8fe48c626d0e9b7c0e3b0c6fe8d1 crates/yu-hir/Cargo.toml
```

## Commit packet

* Exact lease: `notes/theory/2026-10-12-two-use-exact-source-bridge.md` only.
* Baseline: `2b4dcced1a7fe55212c79ce8b61b9a40c893def3`.
* Changed dependency hashes: none; all listed live dependencies equal baseline
  blobs. Initial and corrected primary probe hashes differ as documented.
* Review: bounded source-construction characterization independently reviewed
  by `spec_auditor`; no theorem promotion or implementation authority.
* Checks already run: direct construction/call-site audit, exact source/probe
  integrity and baseline dependency comparison; primary-owned exact source probe
  command in §5. No leaf executable compiler verification.
* Proposed checkpoint: `research: bridge exact two-use source to candidate constructors`.
* Shared-record delta for primary/curator: record that this exact source's
  parser/LocalSource/candidate generation bridge now has finite executable
  evidence; retain semantic SourceTypingAndAdmission/complete Call, publication,
  event/equality transport and the original parent A/B gate OPEN. No shared
  task/index/design/theory-map or pending question bundle was changed.

Writes stop at handoff.
