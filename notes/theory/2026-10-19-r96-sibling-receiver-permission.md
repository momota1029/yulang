# R96: exact nested-helper receiving-view contrast

Revision 1, 2026-10-19. Sole author `/root/r96_proof`.
Status: **candidate source correspondence and conditional finite runtime derivation**.
Independent review, public preparation and execution are pending Luna. This is
neither a reviewed theorem nor production or semantic authority.

## Parent and application

The R96 parent asks for one finite candidate permission-owner contrast for the
two strings below. Its original wider effect-hygiene parent retains provider,
annotation-position, receiver, request, residual and witness lineages under
`xi=(nu,K,D)` and independent outward contributions. Original Simple-sub A/B,
F1/FK1 and evaluator quantifiers remain OPEN and unchanged. R50 remains
NOT_ADOPTED; R85 remains AWAITING_USER_ADOPTION.

The construction here supplies the previously untraced nested-local formal,
annotation and lexical-name ownership premise. Applied to the existing runtime
constructors, it explains why the helper's own received view contains its
boundary while the captured outer view does not. The exact public preparation
and complete outcomes remain unproven until Luna's authorized run. The negative
expectation is **RuntimeUnavailable::HandlerEvidence**, an implementation
observation: it is never a language refusal or nonprotection theorem.

Authority is charter §21, whole-argument scheduling §1/1.1 and top-level
inference principles §1/1.1. Both `[io] int` formals are Computation parameters
because of their outer source annotations. Receipt retains the whole inert
argument; body usage does not choose entry role. The source law alone grants
no implementation approval. Generation, accumulation, propagation, levels,
extrusion, qualifying intrusion and generalization retain their obligations.

## Exact source domain

P is UTF-8, 210 bytes, no final newline, SHA-256
`765a89c4cee89ceaf4213663b1be8e3110d0f81f4026d2112ddf4ee2f9a23780`:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my relay (thunk:[io] int) = {
    my helper (pending:[io] int) = catch pending { io::tick(p), _ -> p }
    helper(thunk)
}
my main = relay (io::tick 7)
```

N changes precisely `catch pending` to `catch thunk`, yielding 208 bytes,
SHA-256 `e1b42dbbbd1141c35857a552123e78f4bb8fe69d55bdd2429aaa6614f135705c`.
No other byte changes. The implementation worker reports the matching pair in
`nested_helper_permission_tracks_its_own_received_view`; its frozen file hash
is recorded below. Different inputs have separately branded source IDs; the
symbols below are independently instantiated in each input, never numeric
identity assertions across programs.

## Finite source construction

Use `runtime_receiving.rs:12–38`'s shared Arc SourceText, scan_header, empty
SyntaxEnvironment and SemanticImports. parse_file checks source allocation and
enters the ordinary root parser (`full_parse.rs:317–340`). Normal Act/member,
formal-pattern, computation-type, operation-path and Catch-pattern token
fragments are the same grammar cases inspected in R88 §§3–5. Those constructor
facts are reusable at these fragments; **R88's authentic whole-source bridge
is confined to U/O/S and does not cover P/N**. No acceptance claim for the
nested source follows just from R88 or its tests.

Here the new containing syntax follows these actual owners. The inline `{`
after relay's equals enters OperatorChain's LBrace branch
(`expression/operator_chain.rs:351`) and `braced_nud_normalized`
(`statement.rs:522–624`), which creates BracedStatementBlockExpression and
runs the Braced statement sequence to its closing `}`. It retains the private
helper BindingStatement followed by the final `helper(thunk)` OperatorChain.
The helper body is inline Catch; it uses the inline branch of
`declaration/binding.rs:328–360`, rather than an IndentedStatementBlock.
The closing brace precedes the distinct column-zero main binding. These are
normal constructor paths for the displayed tokens; syntax diagnostics and
actual parser success remain public-run obligations, not observations here.

Let R be relay's definition SourceRootId, t its original thunk formal, h its
local helper HirLocalId, d the helper's original pending formal, and p the
arm's CatchBinder. `module.rs:2100–2138` mints t from R and the original formal
ordinal, then passes that same formal to LocalSource form. The spaced annotated
parenthesized pattern is accepted by `plain_binding_header`
(`module.rs:3005–3062`); its identifier source key and PatternTypeAnnotation
are retained. `local_source.rs:596–628` copies t and its original annotation
into Lambda(t,body), parses the annotation with owner R, and publishes
`thunk -> Parameter(t)` in the lexical environment.

`body()` (`local_source.rs:465–500`) preserves the actual inline OperatorChain;
its braced expression reaches `block()` (`:1236–1362`). The block constructor
retains the helper as h=(R,local ordinal), its name/key, its initializer slot I,
one formal d and final expression F. It calls plain_binding_header on the
actual helper declaration, allocates d through parameter_id, records d's
original identifier SourceNodeKey and `local_parameter_owners[d]=h`, and
parses d's **own** `[io] int` annotation with owner R. d is distinct from t;
its lexical owner is h even though both parameter IDs and annotations have
source root R. RootCompSchema's root-owner equality does not erase that
lexical distinction or combine runtime receiver boundaries.

The block queues Restore, final F, then its initializer. Work::Initializer(h)
(`:654–698`) temporarily installs helper's self binding, publishes
`pending -> Parameter(d)`, emits Lambda(d,Catch(...)) at I and queues the
original helper body. The outer lexical thunk entry stays live. Catch queues
its scrutinee before installing the payload binder (`:1117–1188`):

| Source occurrence | Exact retained resolution |
| --- | --- |
| P Catch `pending` | Parameter(d), the helper formal |
| N Catch `thunk` | Parameter(t), the captured relay formal |
| common `helper(thunk)` callee | Local(h) after Publish restores initializer scope |
| common `helper(thunk)` argument | Parameter(t), outer relay formal |
| arm `p` | CatchBinder(p), belonging to this arm |
| main `relay` | unique ModuleDef(relay) |

These follow `latest` lexical lookup before module lookup (`:1004–1044`).
Work::Publish restores the initializer guard before installing h for F;
therefore d cannot leak into F. h has no actual self reference in its body,
so the RuntimeProgram ownership walk (`program.rs:334–410`) does not classify
it recursive. A temporary static self binding alone creates no recursive knot.

`source_annotation.rs:134–314,359–587` registers unique family io and distinct
tick/other member IDs and retains both annotations' outer concrete io row and
Int endpoint. `resolve_operation` is shared by expression and Catch pattern;
the argument tick and arm tick designate the same resolved member. Each
signature is Int→Int without outer effects. Catch retains one payload Binder(p)
and wildcard continuation; no continuation binder is created. The final call's
adjacent CallTail holds the naked thunk expression; main's parenthesized
argument retains Group(Apply(Operation(tick),Integer(7))). Source keys, ranges,
indices and occurrences come from the original nodes, not guessed ordinals.

## Candidate preparation seam

CandidateInference::solve selects solve_mode(false,false)
(`shadow_apply.rs:270–281,385–430`). It preflights every actual LocalSource,
permits only registered placeholder errors, collects candidate constraints,
creates InferenceSession, then runs run_candidate. `candidate_source.rs:451–505`
accepts these concrete Int annotations, resolved monomorphic Int→Int operation
and single-payload Catch shapes, subject to actual formed-source availability.
The work traversal registers both Lambda formal IDs, visits local initializers
at the child level, installs locals before the final expression, and emits
FormalEntry/FormalAnnotation and FormalNameEffect actions for the actual
computation formals (`:973–1044,1220–1257`). It visits Catch scrutinee/arms and
both Apply children. Thus N's captured formal is not silently substituted by d,
and neither branch bypasses the solver.

This inspection identifies the real generation/solver owners; it does not
calculate the resulting Simple-sub graph or prove run_candidate success,
absence of candidate_conflicts, native K,D or general inference completeness.
The exact preparation assertion remains **UNOBSERVED / UNPROVEN** for P and N.
The test helper asserts solve success and no conflicts before constructing the
runtime, so either failure falsifies this slice before outcome comparison.

Independently, RuntimeProgram::from_hir consumes the retained LocalSource
(`program.rs:277–330,414–566`), validates source-root indices/labels, copies
binding h and maps both Lambdas to Computation with RootCompSchema. The schema
checks original formal/annotation source-root ownership and ground Int
(`receiving.rs:21–43`). Both Parameter Names are Execute, using their exact
formal IDs; Local(h) and CatchBinder(p) are Observe. Block, Apply, Catch order,
arm body and original source sites are retained. The test uses default runtime
evidence, selects main and obtains execution_roots/start. Success of this
whole public construction/start path is likewise UNOBSERVED / UNPROVEN.

## Conditional finite runtime derivation

Assume the exact public preparation above succeeds, ordinary allocation limits
are not exhausted and the frozen instructions execute as inspected. The
following is a source-backed candidate reduction, not observed execution.

1. main obtains relay's closure and constructs inert D_R for its entire
   `(io::tick 7)` argument. Callee return allocates uR and its computation entry
   binds t to D_R with new view V_R and boundary bR. Its annotation supplies
   the schema, and its original entry receipt is retained
   (`machine.rs:879–1009`, `receiving.rs:123–175`). No tick runs at entry.
2. relay's block initializes h to a closure whose saved lexical environment
   contains t→V_R (`machine.rs:630–644,1889–1927`). Publishing that closure
   neither executes its body nor rebinds captured t. The final call obtains h,
   constructs a fresh inert D_H for the whole naked Name(t) argument, and
   direct_formal_root (`:1478–1494`) reads V_R without executing t. Receiving
   delay copies its image dependency. Invocation uH is fresh and later than
   uR; helper entry creates V_H with image bH→bR and binds d to D_H. The
   closure environment still separately contains captured t→V_R. Entry's
   receipt of V_H under uH does not execute V_H.
3. Both branches install the helper Catch under owner Invocation(uH)
   (`:707–735`). P reads d: consume records the genuine uH/V_H receipt and
   opens execution E_H, then executes D_H. D_H reads t in its saved relay
   environment, records uH/V_R and opens E_R before executing D_R.
   N reads captured t directly: consume records uH/V_R and opens E_R,
   then executes D_R. It never reads d and opens no E_H. Executing a Delay
   changes code/environment without changing the current invocation owner
   (`:1860–1884,1929–1934`).
4. Evaluating tick obtains/evaluates its Int payload through the operation
   consumer and creates the request carrier; executing it emits fresh q with
   observations of the authentic active executions (`:1011–1069,1789–1804,
   1935–1956`). P's observation list includes V_H and V_R; N's includes V_R.
   The family, operation, payload and helper Catch owner are identical
   structural choices across the two runs; no cross-run event-ID equality is
   asserted. Their Lambdas make `closed_primitive` false
   (`primitive.rs:30–37`), so neither uses the ambient negative certificate.
5. Propagation unwinds execution delimiters to the installed Catch while uH
   is live. For the matching tick arm, local_grant checks q's authenticated
   observation, active candidate owner, that owner's own io schema, its
   genuine receipt of the exact observed view and image reachability
   (`receiving.rs:230–323`). In P, V_H's uH receipt and bH supply the positive
   grant even though its older inherited coverage may be unknown. In N,
   uH/V_R **does have an authentic read receipt**, but V_R's image contains
   only older bR, so traversal stops before finding bH. The unused entry
   receipt for V_H cannot match an observation of V_R. Neither matching io
   nor equal Int endpoint manufactures the missing view incidence.
6. With the positive grant, tick's Int payload, single Binder(p) and wildcard
   continuation meet the remaining bounded candidate selection conditions
   (`machine.rs:1580–1684`). The handler is removed shallowly, the suffix is
   abandoned, and p is bound to the payload; arm Name(p) returns Integer 7.
   Ordinary helper/relay returns then complete P. In N, the existing missing
   positive grant branch returns HandlerEvidence at the handler site before
   selection. This says nothing about whether the source language ought to
   refuse, permit or otherwise interpret this case.

No residual emptiness follows from P's ground result. No continuation is
captured or resumed. This local derivation supplies no arbitrary foreign
continuation case, F1/FK1, native residual correspondence, K,D, broad sibling
safety, method typing/dispatch, general inference, semantic adoption or A/B
closure. The two views are not interchangeable providers, witnesses or native
residuals. The five other hygiene fronts remain independently OPEN.

## Evidence, falsifiers and mutual TODOs

Observed evidence is read-only source inspection, byte hashing and the
implementation worker's freeze receipt. Public parsing, HIR construction,
CandidateInference/no-conflicts, RuntimeProgram/start and outcomes have not
been run by this author. The argument above is conditional at those seams;
review can reject even a predicted result that a green test happens to match.

`R96-PREP-1` (owner Luna, exact existing test helper): execute the one authorized
filtered command only after source/proof freeze and clean spec delta. Required
inputs are these P/N hashes and the frozen test. Output is the exact exit,
diagnostics and both assertions. Falsifiers include syntax diagnostics,
StructuralProjection, CandidateError/conflicts, RuntimeUnavailable during
construction/start, P failing to complete as 7 or N giving any other outcome.
No repair/retry is authorized by R96.

`R96-SOURCE-REVIEW-1` (owner Luna-appointed fresh reviewer): independently inspect
the nested body/formal/local-name constructor and local_grant path against the
frozen dependencies. Falsifier: helper annotation lost, d substituted for t,
helper argument wrapped so direct_formal_root does not apply, capture replaced
by helper view, or a different owner/view observation at q. A blocking/major
finding stops this slice. This author cannot certify the combined result.

R88 is reused only for unchanged grammar fragments; its U/O/S bridge is
rejected as whole-input coverage. R92 contributes the existing Block/Publish
and runtime-local mechanisms, re-inspected here; its indented-body fixture and
CLI stdout 23 do not prove P/N. R95's bounded method/role correspondence is
background prerequisite history and establishes no permission behavior here.

## Frozen dependency manifest and resources

Contract revision 1 SHA-256
`195468ceef7c5fe29aee157260e9f0c218a5dd3e95ed759c40f1f86b348d4892`.
Baseline is Luna's R95 bounded prerequisite and R92 runnable example; no Git
baseline was independently observed. All following hashes are SHA-256.

```text
70836f75b3e39633d5dbb07ca6b469591b623513ddbf740e21756896e3ac6479 tasks/agent-loop/inbox/20261019-r96-spec-review.md
6ff65fc977c88837ec279b84088a6c2d89ebfc7f78915e7ac985904fcaa26bf2 tools/inference-playground/tests/runtime_receiving.rs
8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9 tools/inference-playground/src/runtime/receiving.rs
484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11 tools/inference-playground/src/runtime/program.rs
fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46 tools/inference-playground/src/runtime/machine.rs
97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153 tools/inference-playground/src/runtime/primitive.rs
3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786 crates/yu-hir/src/module/local_source.rs
c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a crates/yu-hir/src/module.rs
b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f crates/yu-hir/src/module/source_annotation.rs
7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3 crates/yu-hir/src/source_identity.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb crates/yu-solver/src/shadow_apply.rs
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c crates/yu-solver/src/candidate_source.rs
24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8 crates/yu-syntax/src/full_parse.rs
eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544 crates/yu-syntax/src/declaration/binding.rs
81db2aec4774f2cd1ddc12b64fd9206cf41cdf3eee00ed740676ffc6d7fc5669 crates/yu-syntax/src/expression/operator_chain.rs
fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797 crates/yu-syntax/src/statement.rs
1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883 crates/yu-syntax/src/pattern/mod.rs
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed notes/design/2026-09-29-scc-intrusion-redesign-charter.md
7b2d2556f4b6a93d7beb73a78f476bfea7d0f94de0c5f77649f6cd15ff69a530 notes/design/2026-10-02-source-call-scheduling-choice.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81 notes/design/2026-10-11-yulang-inference-top-level-principles.md
185eff03dfcef4cd9ea346434d60e34b39fcc0f34d46641b160decb58f0f1782 notes/theory/2026-10-19-r88-ordered-selection-source-bridge.md
95b4f651f132c289264e331b580264359f71f0c7da62db7f935972577732463d notes/theory/2026-10-19-r92-indented-binding-body-correspondence.md
dfdf5272569db6c41e5b19f817b0f1cb39b35dac185fa2459edc7844d4b8cdf1 notes/progress/2026-10-19-r95-final-source-correspondence-verification.md
```

Requested model/effort gpt-6.1-sol/high; observed model/effort UNKNOWN/UNKNOWN.
Identity `/root/r96_proof`; session
`current-conversation-2026-10-19-r96-sibling-receiver-permission`. No coauthors
or descendants. R88 author `/root/r88_proof`, R92 author `/root/r92_proof`;
R96 paired-test author `/root/r96_implementation`, separate lease. Proof grant
600 seconds, Astra 0; no renewal. No tests, builds, compiler CLI, Git, external
contact or source edits performed. Reads/hashes only; unavailable `python`
hash attempt exited 127, then python3 completed the read-only calculation.
Only this note and `tasks/agent-loop/inbox/20261019-r96-proof.md` are new;
no scratch/generated paths. Freeze ends the assignment; next step is Luna's
run/review seam. Final hashes and write-stop receipt belong to the handoff.
