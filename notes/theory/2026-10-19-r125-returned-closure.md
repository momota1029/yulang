# R125: original x through a returned closure and local alias

Status: **conditional finite source/runtime correspondence; fresh review pending**.
Assignment `R125-PROOF`, revision1; sole author/writer `/root/r118_proof_lane`;
no coauthors or descendants. Contract rev2 SHA-256
`e97f2b72e4c73089f10174255c754c3e465cd1026d2fc7af67bd217b6940770d`;
baseline `145aca5f6`.

## Parent, exact claim and premises

For the exact59-byte/no-final-LF source, specified SHA-256
`246f6fe5ff1a9685bf8ae3e264402a22e71be668d997330df3f92e0d272f672b`:

```yu
my main = { my capture x = \y -> x; my f = capture 7; f 9 }
```

the original inner-body Name retains parameter ID x through candidate and runtime
construction. The returned closure retains the environment containing x's cell7;
alias f stores that same closure value/view. Later invocation binds distinct y
to9 in an extension of the saved environment; exact-ID lookup of x returns7.
Returning from capture retires its invocation, not the retained environment.
This is one finite component of the static-to-runtime frontier; no general
closure/lexical-scope/alias/recursive-source theorem or parent closure follows.

**H:** actual exact-source parse/HIR/LocalSource formation succeeds, preserving
original source keys, local/formal IDs, body/Apply shapes and lexical scope.
**A:** ordinary candidate preflight/collection/solving accepts without conflicts,
and complete RuntimeProgram/start admission succeeds on the same HIR. Independent
source typing/ordinary transition correspondence remains a premise; no endpoint
type is proved from an executable value alone. **E:** all inspected value/view,
binding/label/owner and ordinary execution checks succeed. **B:** resource,
identity and I/O checks succeed, with completion within10,000 transitions.
These actual successful source/admission/bounded execution premises are not
observations by this author. No tests/builds/CLI/probes ran.

Charter §21 selects Value entry separately for own unannotated x and y. Both
whole argument expressions are delayed then forced/rebound within their actual
invocations, including unused y. §24 selects the ordinary unannotated inner
function literal's pure receiver role; this is distinct from ParameterRole::Value.
The runtime parameter-role enum does not itself certify Function-role elaboration.
No pure-to-handler rule, universal handler classification or permission fact is
inferred from the Value role or absence of a runtime request.

Original Simple-sub/evaluator A/B, all six effect parents, F1/FK1 including
foreign continuations, method M/T/A and R85 adoption remain OPEN, with unchanged
domains/quantifiers and provider/residual/witness lineages.

## Original source identity and LocalSource construction

Let R be main's authentic source root; h_capture/h_f its distinct local IDs;
p_x the original named x formal; p_y the original inline y formal; o_x the
inner body's original Name occurrence. These symbolic identities denote actual
constructor products, never IDs reconstructed from spelling or type.

The returned ParsedFile/source-key premise is explicit. Under H,
full_parse.rs::source_root/SourceNode::children/key preserve its original parse
brand, green allocation and offset; source_identity::source_keys indexes actual
nodes. `lambda_nud_normalized` (expression/lambda.rs22 onward) constructs the
original LambdaExpression with Backslash, y Identifier and Arrow, then delegates
the original body within OperatorChain. This is a local constructor fact, not
a full grammar/lexer admission proof. Body x and header x are distinct original
occurrences. Named x has IdentifierPattern source origin; inline y records its
own Lambda source key plus binder-token range, not a fictitious IdentifierPattern.

LocalSource::block (1236 onward) retains h_capture and h_f in original order,
their initializer labels and final expression. It allocates p_x for capture's
actual formal, records its key and local_parameter_owners[p_x]=h_capture, and
keeps annotation=None. Work::Initializer (654–699) temporarily installs the
named function's self scope, pushes Parameter(p_x), emits its original named
Lambda, then visits its body. Work::Publish restores that initializer scope
before installing Local(h_capture) for the later f initializer/final expression.

For the inline Lambda, Builder::expression (977–1006) validates the original
slash/identifier/arrow/body shape; parameter_id mints p_y distinct from p_x;
record_inline_parameter retains its original key/range; annotation stays None.
It schedules restoration, pushes Parameter(p_y), then forms body x in that
environment. latest lookup (1007–1040) finds p_x still active under distinct y.
Thus o_x has exactly LocalSourceResolution::Parameter(p_x), not p_y or a module
name. Formation's source scopes and original node provenance are retained.

After Publish, capture7's callee resolves to Local(h_capture); final f9's callee
to Local(h_f). The zero-formal f initializer retains the entire original
Apply(capture,7), not a new function definition. The actual source therefore
supplies `Lambda(p_x,Lambda(p_y,Name(Parameter(p_x))))` plus the two ordinary
Apply sites and local binding records. These conclusions are applied only under
H's authentic successful constructors, not proved by a fabricated carrier.

## Candidate endpoints and runtime Lambda/Name identities

candidate_source::emit_candidate_source (826 onward) requires pointer-identical
HIR-owned LocalSource, correct parent/root and authentic occurrences. It registers
p_x and p_y separately (867–889) and maps parameter Names through those exact
IDs to CandidateEndpoint::Parameter(recipe position) (894–901). The original
inner body endpoint is p_x's parameter position; it cannot silently become
p_y by equal shape or scope nesting.

Both annotations are None, so formal registration selects Value. Lambda visits
retain original omitted-formal identity/levels. LambdaRecipe (1409–1425) connects
each actual formal registration to its actual body endpoint: the p_y lambda's
body endpoint remains p_x's. Local h_capture/h_f Names schedule their own Local
actions unless genuinely active recursive linking applies; ordinary Apply
records its complete callee/argument/result endpoints/effects, cause and level.
This is constructor/endpoint preservation, not proof that all constraints solve,
that local instantiation/generalization is complete, or that static components
are runtime cells.

shadow_apply::solve selects ordinary solve_mode(false,false). The pinned mode
preflights actual retained sources, collects the ordinary candidate batch,
creates its session and runs candidate inference (385–430). Successful solve and
absence of conflicts remain A. No one-off inference rule or bypass is introduced.

RuntimeProgram::from_hir preserves each actual Lambda parameter/body label and
Name resolution. Both Lambda parameters are Value; their parameter Names Observe
under the own-annotation role map (program.rs414–476,488–516). Local binding IDs,
initializer labels and final body are preserved. Its recursion walk (346–373)
finds no Local(h_capture) self-reference in the initializer; the temporary
formation self binding is not an executed recursive knot. Both runtime locals
are nonrecursive. This source has no handler or computation-root consumption.

## Finite environment, cell and value derivation

Use actual environment arena links E0/E_x/E_y; original p_x/p_y; local cells
c_capture/c_f; parameter cells c_x/c_y; value handles V_capture/V_closure/V7/V9.
These are separate kinds, not numeric ID claims or a source-root/owner equality.

1. Main's block starts with E0=the empty module environment and a pending main
   Root. begin_local (1891–1928) allocates c_capture=None and a pending Local
   frame. Evaluating its named Lambda creates V_capture with executable
   Closure {parameter:p_x,body:inner_lambda,environment:E0,...} (630–645).
   The function body has not run. data/allocate retain its original source and
   executable object and attach an opaque view.
2. Local completion stores exactly that received V_capture/view in c_capture,
   then extends E0 with Binder::Local(h_capture)→c_capture (1141–1162).
   It begins f's initializer, allocating c_f and preserving that caller environment.
   Name(h_capture) reads V_capture by ID and Observe validates its matching view.
3. Apply obtains V_capture first, allocates a whole inert Delay for7 in the caller
   environment, enters actual invocation u_capture and pushes ReceiverReturn
   plus ValueEntry(p_x,inner_lambda,E0) (880 onward,964–975). It then evaluates
   the argument inside that invocation. literal::integer gives canonical7;
   ground_data creates V7 and its ground view (1984–1997).
4. ValueEntry (1081–1099) calls bind(E0,Parameter(p_x),Received(V7)), allocating
   initialized c_x and E_x whose parent is E0. It evaluates the original inner
   Lambda **under E_x**. Lambda evaluation creates V_closure with executable
   Closure {parameter:p_y,body:Name(p_x),environment:E_x,...}. That captured
   environment is the constructor's current lexical environment, not a later
   reconstruction from caller spelling or the retired invocation descriptor.
5. ReceiverReturn retires u_capture and returns the same V_closure and view,
   changing neither executable map entry nor E_x (1070–1080). It does not execute
   the returned closure, recursively force latent code, pop E_x/c_x or snapshot
   store. Environments/cells are machine-owned vectors; extend/bind append;
   ordinary leave_owner retires invocations, not these retained arena records.
6. The original pending Local f writes exactly that V_closure/view to c_f, then
   extends its saved caller environment with Local(h_f)→c_f. Alias f changes
   neither executable body/parameter nor captured E_x. Its caller environment
   contains local f/capture, but is not substituted for E_x on closure invocation.
7. Final Name(h_f) locates c_f by Local ID and observes the original V_closure.
   Callee selection retrieves the existing executable map entry and clones its
   fields, including saved E_x. It delays9 in the caller environment, enters
   distinct actual invocation u_y and installs ValueEntry(p_y,body_x,E_x).
   Although y is unused, the declared Value entry evaluates9 first inside u_y;
   ground_data constructs V9 with its own ground view.
8. bind(E_x,Parameter(p_y),Received(V9)) allocates c_y and E_y whose parent is
   **saved E_x**, then evaluates original body_x there. The Name's retained
   resolution is Parameter(p_x). lookup (1960–1970) checks E_y's p_y, sees
   p_y≠p_x, follows parent E_x, finds Parameter(p_x)→c_x, and reads V7.
   It does not look up the text x or return c_y/9. u_capture may be inactive;
   that does not expire the stored lexical parameter cell.
9. Observe validates V7's original ground view, creates a genuine receipt under
   current u_y and returns that same received V7. ReceiverReturn retires u_y;
   main's Root publishes V7 and the selected-definition phase returns its cached
   value. No source binder or closure environment is rebuilt at return time.

## Retained-value view consumption, not permission inference

receiving::ground(value) (105–113) stores the exact handle with image=None and
unknown=false. opaque(value) (95–104) also stores the exact handle/image=None,
with unknown=true. machine::data uses opaque for each closure; ground_data uses
ground for literals. The view is not the closure's captured environment.

matches_value (185–187) compares only the stored value handle to the received
handle. Thus the returned closure's authentic opaque view passes subsequent
Observe consumption despite unknown=true; no ground tag or permission certificate
is required to alias/call it. consume (1858 onward) validates that relation and
records a genuine receipt, then Observe returns the same received record.
receipt appends owner/view/site/formal metadata; it does not rewrite the value,
the view's unknown flag or the executable closure environment. These exact
consumers establish the alias/read links above under E.

No local_grant query, request/continuation capture, root-view projection or
unknown-coverage negative conclusion is needed for this source. No general
profile completeness is inferred from opaque/ground/matches_value. Runtime
parameter entry still forces9 under §21 even though the source function literal
is pure under §24; receiver role and argument demand remain different decisions.

## Public result, prior evidence and next owner

Current lib::prepare constructs one HIR Arc, solves a clone, rejects conflicts
and returns it; execute gives that same HIR to RuntimeProgram and runs its
source schedule. This inspected wiring does not establish H/A. Under B it
renders completed Integer7 plus LF. main prints only successful output and
returns success with empty stderr. The finite prediction is exactly `7\n`.

Existing runtime.rs::returned_closure_retains_its_lexical_capture (42–45)
contains these same bytes and asserts7 through execute(...10,000,false). This
is source/test inventory, not a new observed run, source-generation proof or
proof of environment identity. No other test's recursive/annotation claims
are imported. The new public stdin test is independent finite surface evidence.

- `R125-SOURCE-1` / Luna source reviewer and HIR/candidate owners: establish H/A
  for original x/y/locals/body/Apply identities and retained source. Wrong
  parameter/inline origin, lexical resolution, unsupported source or conflicts
  falsify it; assumed transition fixtures cannot prove actual construction.
- `R125-ENV-1` / compiler/source reviewer, runtime/receiving owners: verify
  V_closure→E_x→c_x through return/f alias, E_y.parent=E_x and exact p_x lookup.
  Changed closure/view/environment, returning9, expired lexical cell or text/
  type reconstruction falsifies the bridge.
- `R125-CLI-1` / implementation/verification lane: frozen exact stdin cell,
  three CLEAN reviews, then only contracted one-shot command. Failure, timeout,
  non-admission, exhaustion or different streams leaves observation OPEN.
- `R125-REVIEW-1` / Luna: fresh compiler/source, spec and regression reviews;
  producer/coauthor cannot certify it or close universal parents.

No code edit or additional implementation TODO/lease is requested. Next in-scope
result after freeze is independent source/environment review and the already
authorized public observation; no further producer work remains in this envelope.
Ordinary generation/accumulation/propagation/levels/extrusion/qualifying intrusion/
generalization and separate provider/residual/witness lineages remain unchanged.

## Dependency hashes, authors and resource receipt

All21 direct input pins and contract matched before writes. The complete frozen
manifest is contract rev2 above; core proof-defining hashes are:

| Input | SHA-256 |
| --- | --- |
| charter §§21,24 | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| runtime.rs | `f8bebfd4eb4571e2814b83ea8473c035b429fe1eed4e07d26942a096143306ec` |
| machine.rs | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| receiving.rs | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| program.rs | `c2363ad42104b895519bb29a8eb9aeda545bd0176cebbd78750d3a2df90849ca` |
| literal.rs | `2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f` |
| HIR local_source.rs | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| HIR source_identity.rs | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| candidate_source.rs | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |
| shadow_apply.rs | `838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543` |
| full_parse.rs | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |
| expression/lambda.rs | `56357346a0f59330a202936f88337af1490b1839f339dc113b0b35f2d8c777b0` |
| lib.rs | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |
| main.rs | `75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100` |

Exact full paths and remaining inventory hashes are rev2's immutable rows.
No unlisted source was read. No historical proof or existing test assertion is
upgraded to actual execution/source admission. Source/test/charter byte authors
UNKNOWN; contract/status owner Luna; sole present proof author above.

Requested configured Sol/high; requested concrete version and observed model/
effort UNKNOWN/UNKNOWN, no switch assumed. Firstclock `2026-10-19 10:59:10 UTC`;
cap420sec unchanged. Unmeasured preclock locator work remains conservatively
charged in handoff. Exact CPU/memory/launch-start duration UNKNOWN. Static
listed text/hash inspection only; no executable verification/tests/builds/CLI/
probes/formatter/Git, external contact or descendants. Only this note and
assigned inbox are new; no scratch/generated paths or foreign writer edits.
Final time/hash receipt is in handoff. **Freeze rev1 and STOP.**
