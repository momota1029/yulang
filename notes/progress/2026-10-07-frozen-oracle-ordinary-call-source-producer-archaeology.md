# Frozen Oracle ordinary-call source producer archaeology

Date: 2026-10-07
Yulang3 baseline: `67d9e5279c499ff445acabf0b7262d1a7e8d1231`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Status: bounded historical characterization; compiler-referee review passed
Authority: historical implementation evidence only; no semantic or production authority

## Question and result

The current open `ORIGINAL_ASSOC` producer must associate the original
five-node Call `call(result(name f), result(name x))` with its source-owned
slot/contribution at original `beta,p0`, while typing the complete receiver
invocation under the original shared `xi` and scopes. A bounded Frozen Oracle
trace of parsing, parameter ownership, lexical resolution, call lowering and
frame selection found no constructor for that complete original fiber. It did
find the historical header-to-formal and frame-to-formal mechanism below.

## Historical mechanism

Paths are relative to `/tmp/yulang2-oracle-rebuild`.

1. `crates/parser/src/stmt/binding.rs:16–33,56–146` separates a binding's
   header from its body and ends the declaration header at `=`.
   `crates/parser/src/pat/parse.rs:239–260` constructs applied header patterns;
   `crates/parser/src/expr/tail.rs:272–295` constructs expression `ApplyML`
   for an ordinary application such as `f x`.
2. `crates/infer/src/syntax.rs:108–123` extracts the declaration head name,
   while `crates/infer/src/lowering/expr_syntax.rs:401–435` separately
   collects argument Pattern children. Thus `step x = ...` retains `step` as
   the declaration and `x` as a formal pattern.
3. `crates/infer/src/lowering/pattern.rs:234–281` creates each formal as
   `Def::Arg` with a live type variable, optional source span and local
   binding. `crates/infer/src/lowering/expr/lambda.rs:724–736,887–894`
   assigns input/scope metadata, creates a Defined frame and records eligible
   unannotated locals in its frame index.
4. `crates/infer/src/lowering/name_ref.rs:73–75,146–174,208–221` resolves the
   innermost local to a `DefId`, allocates a `RefId`, and retains a `RefUse`
   with parent, value and source span. The ordinary chain route in
   `crates/infer/src/lowering/expr/chain.rs:104–119,151–153,537–547` lowers
   the head and application tail directly into poly IR; this path has no
   intervening HIR record.
5. `crates/infer/src/lowering/expr/tail.rs:89–126,535–627,630–686` lowers
   operands and source ranges, creates a four-port negative Function demand,
   retains `Expr::App`, and conditionally records App and argument-boundary
   spans. `tail.rs:740–798` allocates/reuses a subtraction marker keyed by
   `(selected frame, formal DefId)`. The selected frame is chosen at
   `tail.rs:801–830`. The frame map shown in
   `crates/infer/src/lowering/local.rs:179–193` has no Call `ExprId`.

The smallest parser discriminator is removal of the header's applied formal
pattern: the declaration head remains `step`, while its extracted formal list
changes from `[x]` to `[]`. This distinguishes formal/frame setup from direct
body lowering. It is a CST/control-flow discriminator, not an admitted source
counterexample.

## Boundary and claim limits

Conditioned on successful ordinary parsing/lowering, a local formal, and the
unannotated Defined-lambda/frame guards, the traced constructors retain lexical
definition/use identities, source ranges, live inference endpoints, an
application node and frame/formal subtraction evidence. They do not produce
the original static signature slot, an independently typed complete receiver
invocation contribution, exhaustive `Slots(beta)`, or the original joint
`(nu,K,D)`/`xi` interpretation. In particular, endpoint IDs, spans, App IDs or
the frame/formal marker cannot be assigned to `s`, `c` or `p0` by equality.
The demand is submitted before App allocation and span registration, so these
records also do not independently certify a pre-query original association.

This is bounded absence in the inspected constructor chain, not a
repository-wide nonexistence proof, current source adequacy result,
counterexample to an approved rule, or theorem closure. No Oracle output or
success result is used as semantic evidence; no rule is adopted from Oracle.
The next target remains an independent derivation of the original
owner/view-kernel introduction for the fixed Call, preserving every legitimate
original witness and its complete receiver contribution.

## Scope and checks

The pass traced identifier parsing, binding-header extraction, formal creation,
lexical resolution, ordinary application construction and frame selection.
Sixteen Oracle source files were inspected; all sixteen matched pinned blobs
byte-for-byte. Newly recorded SHA-256 values:

| Oracle file | SHA-256 |
| --- | --- |
| `parser/src/stmt/binding.rs` | `3e17d035b5009b61fe34f193ab5aac3304cc81b42c590ba7ebd4b15b0e151817` |
| `parser/src/pat/parse.rs` | `443458232068b1b0f0ca0c354f8ee5145d1fcf7f2d0aee760ad6c1cb4ba1a419` |
| `parser/src/expr/tail.rs` | `ff3aaa7bb28ec77f0b7942f2ae6c1d435babe5cc9ec10127ca58a4df1623d52f` |
| `infer/src/syntax.rs` | `ee305b7659205a4d934c387452380bfc89e05606edc1b44ab732aa82a3b3ee96` |

No Oracle execution, tests, builds, mutations or file writes occurred during
the research pass. Parser acceptance completeness, imports/aliases,
method/effect-operation calls, solver correctness, generalization and runtime
adequacy were not examined. The current Yulang3 baseline was `67d9e527…`;
governing source contracts remain unchanged and authoritative.

An independent compiler-referee review traced the cited chain and verified
Oracle HEAD plus all eleven explicitly cited files against the pin; all four
displayed SHA-256 values matched. No correctness findings were reported. The
review did not certify the producer's full sixteen-file inspection count,
parser completeness, solver/generalization behavior, runtime adequacy or
repository-wide absence.
