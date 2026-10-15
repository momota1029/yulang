# Inline lambda HIR formation: lexical construction and source bridge

Status: independently reviewed local formation theorem and actual source bridge;
primary adjudicated the original private HIR formation gate complete
Baseline: `0ac1c96e7cdf78528be8965ea9ea53549b7b90fa`
Branch: `research/simple-sub-intrusion`
Lease: this file only; leaf, no delegation; production verification owner: primary
Method: bounded static constructor inspection and induction on the explicit work stack
Implementation delta inspected: `local_source.rs` SHA-256
`53e3b324cac9364ac7313e44f9cc739d876427c9018df2a22e5a88119c46c1f9`;
`shadow.rs` SHA-256 `676f003fb641a060e497c47ceb406a2fd1814a34d621758c34fc958c3b807612`

Primary adjudication: independent compiler-referee review accepted the original
C1–C5 bridge. One reversed CatchArm ordering word was corrected to match the
actual source, then independently delta-reviewed with no remaining findings.
Specification review and 33 focused implementation/consumer tests passed;
tests are not premises of this theorem. All 12 dependency records matched
before progress synchronization. See the
[integration record](../progress/2026-10-15-inline-lambda-hir.md).

## 1. Frozen parent statement and exclusions

Quantify over every finite actual parse product P, every admitted enclosing
binding RootPlan r in P, every artifact-branded definition root d supplied by
`lower_plan`, its original admitted parameters, namespace and source inventory,
and every unary `LambdaExpression` occurrence L reachable in r's body through
the private LocalSource builder's supported expression/statement constructors.
The body envelope includes every previously admitted ordinary body form and
their supported nesting, with further unary lambdas admitted recursively. It
is not restricted to identity, integer, callback-only, named-helper, ASCII or
unshadowed bodies. Original CST nodes, lexical extents, binders, source ranges
and capture identities are fixed; no source rewriting is permitted.

The required successful-formation conclusion is:

1. Each L creates exactly one distinct parameter p owned by d, with no alias to
   any root, named-local or other anonymous parameter, and exactly one Lambda
   arena record whose body points to its actual body formation.
2. Every ordinary name use in that body resolves to its nearest live binding;
   absent an intervening shadow, a captured name retains the exact incoming
   resolution identity. Resolving a name never recreates a captured identity.
3. Lambda exit restores the incoming lexical environment exactly: its
   parameter and body-local bindings cease to be live before any enclosing
   sibling resumes; preexisting bindings remain intact.
4. The literal, its introducing binder token, and actual body retain authentic
   positions/ranges from P. There is no fabricated `IdentifierPattern` for a
   direct lambda binder. Given an available ShadowArtifact of P, same-parse
   joins succeed, and foreign parse/artifact
   joins cannot impersonate them.
5. Recovery/malformed lambda input cannot publish a fabricated consistent
   LocalSource or HirModule. A private failure may leave scratch counters
   changed; complete rollback is not required.

The successful-formation statement is not allowed to become vacuous: the complete
bridge must additionally show that the new constructor admits every such
well-formed L whose ordinary body and enclosing formation pass the existing
structural, identity and resource checks. All lexically admitted identifier
spellings, including Unicode, suffixes and `_`, stay in the parent domain.
The primary's binder audit resolved `_` as an ordinary named formal under
the existing F5 foundation sections 3–4/21. It is not a Catch wildcard in
this context. Contextual words in the body retain ordinary expression grammar;
the claim concerns actual IdentifierExpression uses, not reinterpretation of
keyword expression constructs as parameter references.

Fixed hypotheses are an immutable proper CST tree from the actual parser;
actual source-key inventory from that parse; root parameters enumerated by
`lower_plan`; successful checked identity allocation; and the existing private
attempt/publication boundary. C1–C5 in section 5 fix the original
constructor/consumer obligations; section 6 establishes their correspondence
to the inspected implementation delta. Availability of a ShadowArtifact is
needed only for its accessor conclusion: its preexisting depth/element and
diagnostic preflight can reject some parse products for which LocalSource
formation succeeds. Authentic parse keys and ranges are retained regardless;
this proof introduces no LocalSource source restriction from that envelope.

Excluded: new parameter syntax, ordinary production-HIR cutover, named-group
creation or generalization boundary selection, expected-context callback
typing, Simple-sub constraint activation/levels/extrusion/intrusion,
generalization, complete Call, Force, effect hygiene, runtime representation,
execution, whole-language soundness and principality. These remain separate
gates. A formation result establishes none of their conclusions.

## 2. Governing authority and exact source owners

The primary's accepted task is the next private HIR connection after the
completed unary parser. The parser authority is
`notes/design/2026-10-15-unary-lambda-parser.md` sections 2–3 (complete header,
direct Identifier token, ordinary full body) and 5 (parser-only approval;
binding and wildcard meaning deliberately deferred). Its parser proof is an
input; no new parser preservation proof is attempted here.
The primary's authorization/construction receipt is
`notes/progress/2026-10-15-inline-lambda-hir.md`, “Authority and bounded
construction.” It records the user's continuation approval and compatible
typed-origin construction. The binding rule reused for `_` is
`notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md`
sections 3–4/21: a recovery-free Identifier formal and local-first spelling
lookup, without a wildcard exception. That reuse adopts none of the old F5
solver route or historical support restrictions. The source-Generalize design
`notes/design/2026-10-08-source-generalize-definition.md` section 2 preserves
original formal/source scopes; this HIR bridge does not instantiate its full
semantic event records.
`notes/design/2026-10-11-yulang-inference-top-level-principles.md` sections 3–5
govern construction-directed proof and private abnormal-path safety.
`rules/compiler-engineering.md`, “Natural compiler behavior and proof-obligation
economy,” forbids artificial source restrictions and favors provenance retained
at its real introduction. `rules/design-authority.md` fixes adoption authority;
this note proposes no new API or meaning. The delegation, model routing,
leased-write and freeze rules read for this packet are
`rules/agent-orchestration.md` (“Proof delegation and decomposition,” “Model
routing and Astra escalation”), `rules/research-lab.md` and
`rules/git-concurrency.md`.

| Actual owner at baseline | Evidence relevant to this claim |
| --- | --- |
| `yu-syntax/src/expression/lambda.rs::lambda_nud_normalized` | Opens the actual LambdaExpression; emits direct Backslash, Identifier, Arrow; opens actual OperatorChain body. No IdentifierPattern is emitted. |
| `yu-syntax/src/full_parse.rs::SourceNodeKey` | Node keys retain parse brand, green allocation and start. They are node identities, not token keys. |
| `yu-hir/src/shadow.rs::source_keys` | Explicit traversal inventories actual parse-owned node keys. |
| `yu-hir/src/module.rs::lower_module_with_local_source` | Fresh private counters/source identity; opt-in LocalSource flag; ordinary lowerer is separate. |
| `module.rs::lower_plan` | Enumerates root parameter IDs at ordinals 0..R; calls `local_source::form` with those IDs; inserts carrier only after successful formation. |
| `module/local_source.rs::form`, `Work` dispatch | Root recovery preflight; root named-parameter introduction; explicit LIFO scheduler; completion requires every slot present. |
| `Builder::push_binding`, `restore`, IdentifierExpression arm | Single lexical stack/latest-spelling map; prior-binding links; exact identity lookup and namespace fallback. |
| `Builder::block`, Initializer and Publish work arms | Root-wide checked parameter ordinal stream; temporary recursive self, parameter shadowing, publish-after-body and block restoration. |
| `Builder::slot`, `key`, `set` | Fresh owner-branded slots, parse inventory lookup, checked occurrence minting, actual node range/scope retention. |
| `shadow.rs::HirSourceIdentity::record_parameter`, `ShadowArtifact::parameter_source_position` | Baseline map stores node key only; consumer admits root or named-local parameters and promises IdentifierPattern source. Section 6 bridges the formerly missing anonymous admission/direct-token distinction. |
| `module.rs::lower_module_with_counters` | Returns HirModule only after every plan succeeds; `?` propagates failed private formation. |
| `yu-solver/src/candidate_source.rs`, preflight and Lambda visit/finish | Already consumes LocalSourceForm::Lambda and exact parameter ID/body index, creates formal registration and LambdaRecipe. This is a seam inventory, not proof of callback-context or solver correctness. |

Paths abbreviated in the table are under `crates/`. Baseline line locators:
`local_source.rs` 392–562 formation, 565–649 stack/slot/key, 650–666 set,
668–864 expression dispatch, 879–968 Catch, 970–1019 conditional,
1021–1151 block; `module.rs` 911–921 opt-in entry, 1391–1429 root parameters
and carrier insertion; `shadow.rs` 354–362 source keys, 396–398 parameter map,
718–747 parameter-position join. Symbol names govern if line numbers move.

## 3. Existing lexical invariant: direct derivation

For stack E = `lexical[0..n]`, define Live(s,E) as the greatest index j<n
whose entry spelling is s, when one exists. Invariant I is:

- `latest[s]` exists exactly when Live(s,E) exists, and equals that index;
- each entry j's `previous` is exactly Live(s,E[0..j]) for its spelling;
- each retained resolution is the original supplied identity, unchanged;
- each pending restoration depth is the length of a preserved stack prefix.

The initially empty stack/map satisfy I. `push_binding(s,q)` reads the prior
latest index before extending E, retains it in `previous`, appends the exact
q and changes only `latest[s]` to n. Thus I holds after a successful push;
no new parameter/local/capture identity is minted by pushing.
Its fallible reservations precede the append; this is sufficient for the
successful induction, without asserting universal allocation recovery.

For `restore(k)` with a preserved prefix k<=n, consider its last entry e.
By I the current latest for e.spelling is that last entry. If e.previous is
Some(j), j is exactly its nearest surviving predecessor; restoring the map to
j is correct. If None, no surviving entry of that spelling exists, so removal
is correct. Other map entries are unchanged. Induction on n-k restores
precisely E[0..k] and its latest map. No entry in the prefix is mutated.

IdentifierExpression consults `latest` and copies that entry's resolution;
therefore it selects exactly Live. A miss uses the original namespace with
the existing unique/ambiguous/unresolved distinction. Existing true/false
literal fallback occurs only on a lexical miss; a same-spelled live parameter
continues to shadow it. No restricted spelling alphabet enters this argument.

The work-order premise is actual construction, not an arbitrary transition
axiom. Block pushes its saved Restore, final expression, then initializers in
reverse order. Initializer saves its guard, optionally pushes its temporary
self binding, pushes Publish below its body, then parameters in order. All
descendant work completes above Publish. Publish restores the guard and
installs the completed local; the next initializer sees earlier publications.
The final expression runs before the block Restore. CatchArm first pushes
Restore at the incoming lexical depth, then installs its arm binders and
schedules its body above that Restore. Conditional schedules each
child above a matching Restore at the original depth. These actual LIFO
brackets preserve their saved prefixes; none can pop an ancestor prefix.

Consequently the existing schedule supports nesting arbitrary supported body
constructors without leaking their local scopes. It also preserves recursive
named-local visibility: a lambda inside an initializer captures the existing
temporary self identity; its parameter may shadow that spelling, and exit
restores the temporary self before Publish performs its existing restoration.
This proves a lexical-stack lemma for the inspected implementation, subject
to fresh independent review. It does not establish the absent inline rule.

## 4. Existing freshness, slots, provenance and publication

Root parameter IDs are `HirParameterId::new(d, ordinal)` for 0<=ordinal<R.
Builder starts `next_parameter=R`. Each existing local parameter consumes the
current ordinal, advances it with checked_add, then creates its ID. Induction
on successful allocations gives pairwise different ordinals in the same root,
disjoint from all root parameters. Different branded roots cannot alias.
Inline parameters must use this same stream; independent per-lambda ordinal
counters would falsify this argument immediately.

Each `slot` reserves an unwritten position at the arena's previous length.
Each actual expression constructor transfers that pending responsibility to
one work item or fills it. Named-parameter Lambda loops fill the current slot
and reserve one next body slot. The inline step has the same local
shape. `set` retains the actual node's key/range, supplied scope and newly
minted occurrence, so equal source keys never imply equal occurrences.
On a successful empty queue the completion loop rejects any unfilled slot.
The single-write property additionally follows from the constructor ownership
of each pending slot; it is not checked merely by the Option completion loop.

`form` rejects recovery in the entire root before creating Builder; by proper
tree descent, this covers every reached literal and body. The actual parser
records missing/invalid bodies beneath the recognized lambda. The new arm
must still validate its own direct shape, rather than extracting an arbitrary
descendant Identifier or body and ignoring unexpected siblings. No valid
lambda constructor exists at baseline: expression dispatch falls through to
StructuralProjection for LambdaExpression. Thus no inline source reachability
or authentic inline-parameter lookup is established at this baseline.

Any Err from shape/key/identity/allocation/completion flows out through form
and lower_plan. Carrier insertion occurs only after form returns Ok; HirModule
construction occurs only after every plan succeeds. Some identity/counter
writes may precede failure, and earlier roots may already have private carriers;
the opt-in entry's fresh counters are private to the failed attempt and no
HirModule is returned. This proves no partial publication at these actual
callers, not safe retry on reused failed counters or full memory restoration.

## 5. Fixed inline-constructor obligations

The first static pass froze the following obligations before implementation.
The lexical lemma extends to the Lambda constructor exactly when the actual
implementation establishes them; section 6 gives the source bridge.

**C1 — authentic direct shape.** From L itself, validate the significant direct
children/tokens as Backslash, one Identifier, Arrow and the one actual body
OperatorChain, allowing existing trivia. Reject recovery/unexpected extra
structure. Use the direct token's actual text/range and introducing L's key;
do not manufacture a node, substitute a named helper, or search descendants
for a convenient binder. The full ordinary body goes to the existing builder.

**C2 — one identity/one structural edge.** Consume exactly one checked ordinal
from the shared `next_parameter` stream; create p at d; reserve exactly one
body slot b; fill the incoming slot with Lambda(p,b), actual L provenance and
the incoming scope. Retain p's introducing scope, and give body formation
`LocalSourceScope::Parameter(p)` as for existing parameter introduction.
Do not call `next_named_group` or `record_named_group`: carry the enclosing
group attribution through unchanged. This statement does not choose a new
generalization boundary or equate named-group membership with receiver entry.

**C3 — lexical bracket.** Save k=lexical.len() before activation of p. Put
Restore(k) below the actual body work; activate p according to the separately
authorized binder semantics; schedule the actual body above that restore.
For every admitted identifier, including `_`, the resolved ordinary named-formal
contract uses `push_binding(spelling, Parameter(p))`. All recursive body work is pushed
above Restore(k), so I proves nearest-shadow selection inside and exact
restoration before the next enclosing item. Pending application siblings and
named initializer publication remain below this bracket.

**C4 — canonical retained provenance and admission.** Retain that this parameter
was introduced by L and its actual direct binder token, separately from named
IdentifierPattern provenance. `SourceNodeKey` cannot designate a token. The
selected API uses an actual introducing node key plus direct-token range,
carrying authentic evidence without a new CST. The consuming source-position operation must admit exactly the
retained root-owned anonymous parameter, check artifact/parse identity, and
return the genuine kind of introducing position. A map write alone is not
enough: baseline `parameter_source_position` rejects anonymous p because
`owns_parameter` enumerates root formals and local_parameter_owners enumerates
named-local formals. Adding p to a fake named-local owner is not a bridge.
Existing named-parameter IdentifierPattern results must preserve their meaning.

**C5 — existing-body and failure reachability.** Inspect the implemented arm,
its dispatch/callers and provenance consumers to establish C1–C4 on every
relevant path; no early body-shape restrictions or downstream fabricated
source are allowed. Preserve the private error propagation of section 4.
Focused checks owned by the primary should attack nested/sibling lambda
shadow restoration, capturing root/local/self IDs, fresh IDs among local and
anonymous parameters, full existing body forms, exact direct binder/lambda/body
ranges, foreign-parse joins and malformed bodies. Those checks corroborate
the source bridge; they do not replace the induction or prove inference.

Under C1–C5 and the resolved binder activation, induction on strict source
descent and the LIFO work expansion gives the frozen formation conclusion:
C2 and section 4 supply freshness and the unique body edge; C3 and I supply
lexical scope and capture; C1/C4 supply original provenance; section 4 and C5
supply private failure publication safety. Nested lambdas reuse exactly this
step, with their Restore above the outer Restore. No assumed solver transition
or reconstructed typed relation enters the argument.

At the first-pass baseline this implication left **actual emission and consumer
admission of C1–C5** missing. The second pass below changes that evidence by
inspecting the new owning constructor and consumer. It does not substitute
another equivalent conditional lemma. No two failed proof attempts occurred.
The economy audit identifies provenance reconstruction as D debt subordinate
to the A/B formation claim: the implementation now retains the introducing
fact instead of fabricating an IdentifierPattern and reconstructing ownership.

## 6. Actual implementation bridge for C1–C5

The primary supplied a frozen two-file implementation delta with the hashes
in the header. Every assertion below concerns that exact delta over the pinned
baseline, not an inferred implementation from the conditional obligations.
No compiler code or test is written by this proof leaf.

**C1 at `Builder::expression`, LambdaExpression arm, lines 796–825.** The
iterator is over L's direct children/tokens, excluding only the four existing
trivia kinds. The first three elements must be tokens of the required kinds;
the fourth must be an OperatorChain node; a fifth significant element rejects.
The branch therefore selects exactly the header/body topology actually emitted
by `lambda_nud_normalized`, without a descendant search or fabricated node.
The root recovery preflight already excludes Missing/Invalid/Error anywhere
in L or its body. Existing parser body recovery is not converted into a valid
body by this branch. Every admitted raw Identifier spelling is copied from
the actual token; no spelling predicate, ASCII filter or wildcard test exists.

**C2 at `Builder::parameter_id`, lines 565–569, and the arm's lines 811–825.**
The sole allocator reads `next_parameter`, advances with checked_add and
returns `HirParameterId::new(self.owner.clone(), ordinal)`. The named-local
parameter loop now calls this same helper at line 1116. Its replacement is
the exact old read/checked-advance/new-ID sequence, so existing named parameter
identities/order are preserved. Root parameter ordinals remain 0..R, and the
initial next_parameter remains R. Induction over actual calls gives one unique
root-owned p per L, disjoint from root/local/other literal parameters. No
global source-order numbering promise is needed: block header collection may
allocate named-local formals before its initializers are processed.

The arm calls `slot` once for b and `set` once for the incoming index, with
Lambda { parameter, body: b }. It saves the incoming scope in the retained
parameter and Lambda expression. Its one body work item has
`LocalSourceScope::Parameter(p)`. Neither named-group allocator is called;
the exact incoming named_group is passed to both the Lambda and body work.
No synthetic LocalSourceBinding, local owner or generalization boundary is
introduced. The copy in the parameter payload does not allocate another ID.

**C3 at lines 821–824.** Restore is pushed with the length of the incoming
lexical stack, then p is pushed with the original spelling and Parameter(p)
resolution, then the actual body work is pushed. `set` follows without popping
or executing any work. When this branch returns to the form loop, body work
is on top, Restore immediately below it, all preexisting continuation work
below Restore. Any child expansion pushes above this bracket. The preserved
prefix invariant in section 3 applies, so a completed body restores exactly
the incoming environment before an enclosing argument sibling, conditional
branch, Catch arm or named-initializer Publish can run.

Nested same-spelled literals push their own previous links and restore to
the outer p; a lambda body-local shadows p only in its existing extent; a
free captured reference copies the original root/local/Catch/self ID.
The parameter spelling `_` follows precisely this ordinary binding path.
Contextual expression syntax is untouched: only actual IdentifierExpression
nodes perform this lookup. A failure between any of these pushes returns Err
through the owning private attempt; it is not interpreted as successful exit.

**C4 at `record_inline_parameter`, `parameter_source_origin` and `retain`.**
The arm gets `source=self.key(&node)` from the original inventory and
`range=crate::range_of_token(&binder)` from that direct original token.
`range_of_token` uses Rowan text_range endpoints without arithmetic offsets.
It stores ParameterOrigin::InlineLambda { lambda: source, binder_range }
under p and copies the same source/range into LocalSourceParameter. `set`
independently records the actual L source key/range and a fresh occurrence.
No local_parameter_owners entry is made for p.

The source identity's `parameters` map is the one canonical origin registry.
Existing `record_parameter` wraps its unchanged original key with
IdentifierPattern; inline records use their distinct variant. The typed
accessor admits p only if `owns_parameter` admits the existing root formal,
or p's root has the exact HIR artifact brand and that origin registry contains
p. Cross-artifact roots fail before source lookup. Then check_source_parse
requires the accessor's ShadowArtifact to own the identity's parse-root key;
equal text from another parse fails. The selected source_position lookup
additionally checks the actual key's parse brand and uniqueness.

For an available ShadowArtifact of P, `retain` visits every original raw node
and token, keeping kind/range/parent/children, independently of whether the
narrow semantic skeleton can project inline lambdas. Its source-position map
includes every node kind, including LambdaExpression; the separate restricted
temporary node index does not limit this map. A well-formed L has positive
width, and distinct such CST occurrences cannot share both its green node and
start: disjoint positive-width siblings have different starts, and a proper
finite tree cannot contain its own green allocation recursively. Thus the
original L key joins to one raw lambda position.

The typed accessor checks LambdaExpression kind and searches only that raw
position's direct children for a non-node Identifier with the retained range.
C1 supplies its existence and uniqueness: precisely one significant direct
Identifier was admitted, and a real identifier has positive width. The result
is the exact original binder PositionId. A missing match fails MissingSource;
multiple matches fail AmbiguousSource, rather than choosing a witness. This
lookup is validation of constructor-retained evidence, not reconstruction from
spelling or a new binding relation. The old accessor calls the typed one and
returns MissingSource for InlineLambda; it still returns the original node
PositionId for every previously registered IdentifierPattern parameter.

Body provenance retains the original granularity: Work::Expression receives
the actual direct OperatorChain, and its ordinary constructors set authentic
descendant node keys/ranges at the body index. An application tail does not
gain a newly invented full-chain HIR range. The whole actual body OperatorChain
and its original range are also retained as the Lambda raw position's unique
direct node child in ShadowArtifact. Thus literal, binder and body can be
related to P without a second body parser or synthetic range ledger. The
claim does not require an additional HIR occurrence for a transparent chain.
When ShadowArtifact's independent preflight is unavailable, those parse-owned
keys/ranges remain authentic; this proof does not assert that its depth/element
limits are removed or restrict the successful LocalSource envelope to them.

**C5: source coverage and private publication.** Production syntax dispatch
already places LambdaExpression in an ordinary OperatorChain head; the existing
head work path reaches the new expression arm. Application arguments,
parenthesized expressions, local initializers, conditional children and Catch
bodies reach it through their unchanged ordinary schedules. No alternate
shape-limited callback or synthetic helper is required. The arm sends its
one full actual body OperatorChain to the exact existing expression work
path, so every body previously accepted in an enclosing expression remains
available there, including nested literals recursively. All preexisting form
arms are unchanged; the only existing allocation replacement is the equivalent
named-local helper call. No new named-header, annotation, visibility or
generalization requirement appears. Checked identity/resource availability
remains explicit and is not claimed for arbitrarily large finite input.

Strict descendant descent extends the finite work-expansion argument: the
new step schedules only L's strict body descendant and one Restore; it neither
duplicates nor abandons its incoming slot responsibility. Existing constructor
expansions handle disjoint strict descendants. Structural induction therefore
proves nonvacuous supported-body coverage and exactly-once successful literal
formation. Its lexical sub-induction is section 3, freshness section 4 plus
the actual allocator above, and provenance C4 above. No new source hypothesis
or alphabet restriction has been added to make this induction succeed.

The new step has no catch/recovery-to-Ok path. Any failure from shape, key,
checked ordinal, body slot, stack push, body formation or set propagates to
form, lower_plan and the private entrypoint. Final slot and annotation checks
still precede form's Ok. Module publication still follows every plan's success.
Thus a malformed or failed literal cannot publish a fabricated successful
carrier even if private identity maps or queues were partially mutated.

These source cases discharge the originally missing C1–C5 bridge in this
constructive derivation. No remaining local constructor premise is assumed.
The producer initially left parent closure to independent review and primary
verification; their completed adjudication is recorded above. Solver formal
registration still consumes retained IDs and body indices as inventoried in
section 2; no expected-context, activation/replay, Call or runtime theorem
follows from supplying these HIR inputs.

## 7. Snapshot, resources and handoff

SHA-256 of frozen direct dependencies at the baseline:

| Dependency | SHA-256 |
| --- | --- |
| `crates/yu-hir/src/module/local_source.rs` | `96a77474b9e63eecaf3b5be926e82af9a88d531b40fd758f6009b33ba87c4f44` |
| `crates/yu-hir/src/module.rs` | `70678eb23bf50813f77b7be3f90442c3b3faea2c754593cf6f35d3f7c0fcf645` |
| `crates/yu-hir/src/shadow.rs` | `72ff4cef4ac504c26c85a55b4a310111366b372709cc0770e0e20fcdaad2b931` |
| `crates/yu-syntax/src/expression/lambda.rs` | `56357346a0f59330a202936f88337af1490b1839f339dc113b0b35f2d8c777b0` |
| `crates/yu-syntax/src/full_parse.rs` | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |
| `crates/yu-solver/src/candidate_source.rs` | `90db34173d366ed826b34492da0fb2f1c5422b1b41e43fcda14892ec8415e7ab` |
| Unary parser design | `fdfeb76e0fef7f6725c7240a71f50cd63191c1eb6c5fdc0581f921e8fe447cfd` |
| Top-level inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

Second-pass dependency changes and additional exact sources:

| Dependency | Final SHA-256 / change |
| --- | --- |
| `crates/yu-hir/src/module/local_source.rs` | `53e3b324cac9364ac7313e44f9cc739d876427c9018df2a22e5a88119c46c1f9`; actual inline arm and shared allocator |
| `crates/yu-hir/src/shadow.rs` | `676f003fb641a060e497c47ceb406a2fd1814a34d621758c34fc958c3b807612`; typed origins/accessor |
| `crates/yu-hir/src/lib.rs` | `329f3cfdc73fd6b00bc11f31055736b7c024f7ae835ce88bfe827c18dda0b2f6`; unchanged from baseline, actual range helpers inspected |
| F5 foundation design | `781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83`; sections 3–4/21 binding contract |
| Source-Generalize design | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`; section 2 scope preservation |
| Inline HIR authorization/progress receipt (dispatch snapshot) | `de75e90c35e991e4b4712ff9f1e0d7b8af8c406c3161ec434a308877b56814de`; original authority/construction input, later status synchronization excluded |

All other direct source dependencies in the first table remain at the recorded
hashes. Baseline HEAD remains the original pinned SHA. The progress receipt's
status section is primary-owned and may subsequently change; its supplied
authority/construction text is the frozen input used here.

Reads: named rules/config/skill, current task/index/lab locators, parser design,
prior flat formation proof, the formation implementation and narrow caller,
identity and candidate consumer ranges above. Second-pass reads inspect the
exact implementation diff, original Identifier binding contract, actual
range helpers, raw-position retention, typed accessor and publication owners.
Commands were bounded `cat`, `sed`, `rg`, `sha256sum`, read-only Git
baseline/status/diff inspection and
`apply_patch` on this lease. The untracked note received a clean static
whitespace check with `git diff --no-index --check /dev/null
notes/theory/2026-10-15-inline-lambda-hir-formation.md`.
No compiler/tests/expectations/design/shared-record
edits, builds, tests, probes, measurements, Git mutations or delegated jobs.
Budget: initial static pass and one separately assigned bounded implementation
bridge pass, each at most 15 minutes; one lightweight shell command per tool
call (two independent reads briefly overlapped), zero heavy processes, zero
samples; no RSS measurement. No executable test or fixture is a proof premise.
Requested runtime: `gpt-6.1-sol` / `high`. Role declaration/config inspected:
prover registered, model/effort pins absent, configured defaults Sol/high.
Observed effective runtime model/effort: unknown; no Astra request or claim.

The requested independent review and focused implementation checks are now
complete as recorded in the primary adjudication. The next callback-context
consumer obligation remains outside this theorem and OPEN.

Commit packet: exact leased path
`notes/theory/2026-10-15-inline-lambda-hir-formation.md`; baseline
`0ac1c96e7cdf78528be8965ea9ea53549b7b90fa`; dependency hashes above; no
dependency edits by this leaf; original unreviewed handoff was independently
reviewed and adjudicated above, not self-certified. Static producer inspection only; verification owner primary,
no tests/builds/measurements run. Proposed checkpoint message:
`research: bridge inline lambda HIR formation to source constructors`.
Shared-record deltas completed by primary: C1–C5 actual-source bridge is
supplied for the frozen implementation; `_` uses the existing named binding
rule and provenance has a typed original-token join. Independent review and
primary verification are recorded separately; the original local parent is
closed while all callback/solver/runtime exclusions remain.
