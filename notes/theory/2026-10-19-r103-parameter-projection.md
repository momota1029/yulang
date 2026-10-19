# R103: finite source-to-runtime parameter projection

Status: candidate source/native constructor evidence, pending fresh independent
review and the one Luna-owned projection test. Author `/root/r103_parameter_proof`,
assignment `R103-PROOF`, revision 1. Governing frozen contract:
`tasks/agent-loop/sprints/source-runtime-parameter-projection-20261019-r103.md`,
revision 2, SHA-256
`be75da329bc186bcc300bd7764f7a4dd7307f20cb6e1a8505917681b8eb6e7c5`.

## Claim, exact domain and reused observation

The parent is the finite R103 constructor claim: for the authentic LocalSource
of R97's exact C-loop cell, runtime Lambda emission retains the original formal
ID and selects its source annotation role; the positive receiving schema retains
the entire original formal and the Lambda SourceSite. The same source's
unannotated `loop` formal is the finite negative control. This proves no
source-wide static/runtime soundness or permission equivalence.

Use precisely the literal `DECL` and body at
`tools/inference-playground/tests/runtime_control.rs:14,186–190`:

```text
DECL = "act signal:\n    our ping: () -> int\n"
body = "my loop x = loop x\nmy ignore (x:[] int) = 9\nmy main = ignore (loop ())"
source = DECL + body
```

R97's pinned closeout records that its exact six-cell integration command passed
once, reached every assertion, and this C-loop cell completed with Integer `9`.
Its unchanged `machine` helper (`runtime_control.rs:16–42`) parses, checks empty
syntax diagnostics, lowers with authentic LocalSource, solves CandidateInference,
checks absence of candidate conflicts, constructs RuntimeProgram, selects `main`
and starts the machine. `assert_integer` checks completion after 10,000 steps and
the exact integer payload. These are **borrowed R97 observations** for this exact
cell, not a new R103 execution or a measured observation of its internal schema.
R97's proof/handoff originally left execution unobserved; its later pinned
closeout supplies that observation without rewriting those historical artifacts.

Let `r_i` and `r_l` denote the authentic `ignore` and `loop` definition roots in
one lowering, `p_i` and `p_l` their retained LocalSourceParameters, and `e_i` and
`e_l` their LocalSource Lambda expressions. Identity comparisons below are within
that one HIR artifact; a fresh parse/lowering need not reuse its opaque IDs.
Let `site(e,r) = SourceSite { source_root:r, occurrence:e.occurrence,
range:e.range }`. A Lambda site is the retained Lambda expression's site, not
the formal identifier's range or annotation's SourceNodeKey.

## Authentic constructor derivation

1. `module::plain_binding_header` (`module.rs:3005–3068`) retains the identifier
   pattern and its original `PatternTypeAnnotation` node for `(x:[] int)`;
   the unannotated `x` has no annotation. The top-level parameter constructor
   (`:2100–2138`) mints `HirParameterId(definition_root, ordinal)`, records the
   identifier origin, and passes that parameter into `local_source::form`.
   `HirParameterId` equality (`:410–449`) includes both root and ordinal;
   identical spelling `x` does not identify the two formals.
2. `local_source::form` (`local_source.rs:596–628`) copies the parameter's exact
   ID, admitted source key, range, spelling and scope into `LocalSourceParameter`.
   It parses the admitted annotation with the same definition owner, publishes
   the exact ID in the lexical parameter binding, and embeds that parameter in
   `LocalSourceForm::Lambda`. It allocates the body child independently. No
   replacement formal is minted by this top-level LocalSource projection.
3. `source_annotation::parse_annotation_with_marker`
   (`source_annotation.rs:359–387`) retains `owner.clone()` and the original
   annotation node's source key as `position`. `parse_type_source` (`:408–440`)
   produces `value=Int` for the endpoint and `effects=Some(parse_row(...))` when
   the leading node is a BracketRow. `parse_row` (`:529–582`) retains that row's
   own original source key, starts with empty concrete/variable vectors and
   ignores only the delimiters in `[]`; hence both vectors remain empty.
   Thus `p_i.annotation` is present, with owner `r_i`, original annotation key,
   Int endpoint, and **present empty outer row**, including the row key.
   For `p_l`, annotation parsing is not invoked and `annotation=None`.
4. `Builder::set` (`local_source.rs:818–846`) stores each expression's original
   source key and range, mints/records its occurrence, and stores its form.
   The projection below uses this actual retained `e_i.occurrence`, rather than
   assuming equality to a separately produced ordinary HIR Lambda occurrence.
   Source-key construction/retention is owned by pinned `source_identity.rs`
   (`:26–48`). `HirModule::local_source_for` (`module.rs:979–987`) retrieves the
   authentic carrier after checking source ownership through `source_carrier_for`.

The pinned R97 proof identifies the parser's pattern annotation and bracket-row
constructors, also visible at `pattern/mod.rs:1173–1194` and
`type_expr/mod.rs:1596–1620`. Its exact executed C-loop cell establishes whole
source reachability for this reuse. This note does not independently reconstruct
the unpinned `cursor::parse_root` dispatch or infer whole-input parsing merely
from those local syntax cases. No additional parser-owner read is needed for
the contracted R97 reuse; expanding that parser proof would require Luna.

## Runtime projection and finite conclusion

`RuntimeProgram::from_hir` (`program.rs:249–330`) selects each binding's actual
`SourceRootId::Definition`, obtains that root's LocalSource, and checks referenced
indices. Its code loop emits one `Code` per retained expression. For a Lambda
(`:488–508`), it constructs:

```text
parameter = parameter.id.clone()
role = Computation iff annotation exists and annotation.ty.effects.is_some()
root_schema = RootCompSchema::from_parameter(site(expression, source_root), parameter)
```

The `Code.site` constructor (`:555–568`) uses the identical source root,
occurrence and range as the site passed into schema construction. Equality here
is equality of these source components; no pointer identity is required. The
code label is an arena location, not a newly minted formal or source occurrence.

`RootCompSchema::from_parameter` (`receiving.rs:21–43`) rejects an absent
annotation, mismatched annotation owner, mismatched formal root, absent outer
effect row, or nonground/nonprimitive endpoint. Every positive predicate holds
for `p_i`: owner and ID root are `r_i`, its row is present although empty, and
its endpoint is Int. The positive branch clones **the whole original formal**
and the supplied Lambda site. It neither reconstructs the formal from `x` nor
substitutes a solved annotation. Consequently:

| Authentic source occurrence | Emitted instruction | Receiving schema |
| --- | --- | --- |
| `e_i`, original `p_i` with `[] int` | formal ID `p_i.id`, Computation | `Some`; formal is a clone of `p_i`, lambda site is `site(e_i,r_i)` and matches `Code.site` |
| `e_l`, original `p_l` without annotation | formal ID `p_l.id`, Value | `None`, at the first annotation-presence check |

The positive clone retains the formal's source key/range/scope/spelling and the
annotation owner/key/type, empty-row presence, row key and both empty vectors.
The instruction itself carries only the formal ID, role, optional schema and
body label; annotation retention is through the schema's full formal. The
negative result concerns absence of this constructor's certificate only; it
does not establish any global nonprotection theorem.

This discharges the finite R103 mapping as a candidate constructor argument.
It supplies one static-to-runtime projection premise alongside R97's ordinary
entry result. CandidateInference acceptance/completion for the exact C-loop cell
is borrowed from R97; this note does not inspect new solver owners or prove that
candidate permission judgments and receiving certificates coincide. Runtime
entry/receipt consumers are outside this new projection claim.

Original Simple-sub A/B and evaluator parent quantifiers remain unchanged and
OPEN. There is no claim about generation, accumulation, propagation, levels,
extrusion, qualifying intrusion, generalization, method/member production,
role dispatch, continuation/residual lineages, F1/FK1, semantic adoption or
production authority. In particular the R101 nested-handler source is not in
this domain. The method parent still needs its authentic executable binder and
consumer; this ordinary formal projection cannot supply them.

## Missing evidence and concrete falsifiers

`R103-PROJECTION-RUN-1`: Luna owns the finite new unit-test observation after
both writers freeze and fresh independent spec/compiler reviews are CLEAN.
The test must lower the exact source, identify the original Lambda occurrences,
construct RuntimeProgram, and compare original IDs and retained annotation
components to emitted roles/schema/SourceSites. No R103 test execution is
observed here. The paired test is not an input to this independently constructed
note, and no result is predicted as already measured. Any lost annotation owner
or key, erased empty-row marker, changed formal ID, wrong role, absent positive
schema, wrong Lambda site or unexpected loop schema falsifies the corresponding
finite projection obligation and stops R103. No production repair is proposed:
the inspected constructors already preserve the required data.

`R103-PARENT-SCOPE-1`: Luna retains all broader static/runtime and method parent
premises. Extending the source domain, reading a missing owner, or claiming
permission/runtime-entry equivalence needs a new contract. R97's integration
result cannot discharge the new structural assertions, and a passing R103 unit
test cannot establish the broader parents.

## Dependencies, provenance and resources

All contract hashes were checked against actual bytes before construction;
every pin matched, including pre-edit `program.rs`. The source argument uses
that frozen production baseline. The separately leased test-only addition is
not coauthored, reviewed or executed by this proof lane. Direct used dependencies:

```text
2a9e65fd973e4d9c7f0916440fe8438eb6e9a8b8cd7969dc8f89025d9cf1b1ce tasks/agent-loop/sprints/value-computation-entry-20261019-r97.md
77b4ea777a2fd413b356b5128cc55362f1126e6298bcb7c310f776cfd53b4b98 notes/theory/2026-10-19-r97-value-computation-entry.md
aa06b04ff9ad0fb882c89c26e0375fd21eddba489c44b7d54f6156585a66d734 notes/progress/2026-10-19-r97-value-computation-entry.md
6a84958c082f6ec9575cb13962ad395c4246a5e7636df6921429399503eabdfb tasks/agent-loop/inbox/20261019-r97-proof.md
b6d9b8206ca433839ab48b9822f8546bf89d40099a2e8e763da1cb6d210ec39d tasks/agent-loop/inbox/20261019-r97-implementation.md
2619e4c8bb006e2d98cf81887091ae372cb1ae3731de76e7b707a97db577009c tools/inference-playground/tests/runtime_control.rs
1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883 crates/yu-syntax/src/pattern/mod.rs
2e08a49960cd4010ba39641ae509afb7cf59711c1464d3349f5f6db590ebf01f crates/yu-syntax/src/type_expr/mod.rs
7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3 crates/yu-hir/src/source_identity.rs
c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a crates/yu-hir/src/module.rs
3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786 crates/yu-hir/src/module/local_source.rs
b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f crates/yu-hir/src/module/source_annotation.rs
484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11 tools/inference-playground/src/runtime/program.rs (pre-edit)
8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9 tools/inference-playground/src/runtime/receiving.rs
```

Requested model/effort: Sol/high (`gpt-6.1-sol/high`). Observed effective
model/effort: UNKNOWN/UNKNOWN; task metadata supplies no independent execution
attestation. Sole current author `/root/r103_parameter_proof`; no descendants
or coauthors. Historical artifacts retain their original authorship, including
R97's proof and implementation workers and Luna's integration receipt.

Proof allocation: 600 seconds, Astra 0, no renewal. Exact aggregate active-work
spent/remaining is UNKNOWN. Checks were bounded text/hash inspection and
construction against pinned source, plus writing/hashing the two leased outputs.
No tests, builds, compiler/runtime, formatter, CLI, Git, source edits, external
contact or scratch files. New paths are this note and the one exact R103 proof
handoff only. Independent review and Luna's single command remain pending.
Writer stops upon submission of the frozen handoff; no parent closure or ongoing
worker activity is claimed while that review waits.
