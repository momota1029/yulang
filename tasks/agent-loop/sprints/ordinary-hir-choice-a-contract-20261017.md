# Sprint ordinary-hir-choice-a-contract-20261017

Status: ACTIVE, Luna-admitted at baseline `0c0fda3974d1db2c91256667f93c46effa18c8d0`.
Branch: `research/simple-sub-intrusion`; contract revision: 3.
Rev3 supersedes rev2 SHA `7bbfcb0942b5b4681d9c686208dd236f291af0a74b48de5c7f7bb4f9931754dd`
only to pin the fixed literal's lexical classifications, competing literal and
operator branches, header scan and effective operator table. Outcome, output
leases, budget and non-goals are unchanged.

## Parent and fixed outcome

Parent remains the original Yulang inference/execution goal: original A/B
claims, quantifiers, source/native correspondence, F1/FK1, N-Transport, complete
Call, soundness, principality and termination. Every original theorem gate stays
OPEN; this packet does not narrow claims or infer theorem closure from design.

The user selected direction A: develop ordinary HIR admission for structurally
associated application syntax. This authorizes drafting and review of a complete
successor contract only. It does not adopt that contract and does not authorize
compiler or test edits. Implementation requires the user's explicit approval of
the exact reviewed contract and its named supersessions.

Fixed outcome: close the conditional parser/CST-shape premise for the source
`my id x = x; my apply f = f 1; my answer = apply id`; then produce and
independently review one complete, implementation-ready successor specification
for direction A, or stop with the exact incompatible/open choice. The fixed
literal instantiates the general rule; it cannot serve as a specimen whitelist
or evidence of semantic Call typing.

Success evidence: parser constructors establish the exact supported tree/range,
association, occurrence-key distinction, recovery and artifact identity facts;
the successor contract settles all admission/consumer/identity/error/resource
questions listed below; compiler, spec and architecture reviewers independently
accept the same frozen bytes, with all blocking/major findings adjudicated.

## Authority, baseline and dependencies

User authority: current conversation, direction A answer. A supersedes neither
language semantics nor the prior HIR contract by itself.

Baseline: `0c0fda3974d1db2c91256667f93c46effa18c8d0` on
`research/simple-sub-intrusion`; working tree was clean before admission.
Existing frozen directional/proof inputs:

```text
notes/theory/2026-10-17-accepted-call-hir-projection.md 0c1a29f3d590f68064e980459a4373400702034a2366591dae32fe7b1572e25f
notes/design/2026-10-17-accepted-call-hir-admission-contract.md 2f3b6dbb6e735b3c5da96f0bbdaa8357f7580435999e08136ce24e1bf19174ab
```

Direct code pins:

```text
crates/yu-syntax/src/declaration/binding.rs eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544
crates/yu-syntax/src/pattern/mod.rs 1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883
crates/yu-syntax/src/expression/operator_chain.rs 81db2aec4774f2cd1ddc12b64fd9206cf41cdf3eee00ed740676ffc6d7fc5669
crates/yu-syntax/src/expression/tails/mod.rs a3ee107c996e028765570c7ba89b12857cd072eddc988b5b4c8eb66ffc753b8c
crates/yu-syntax/src/expression/delimited.rs e65c4d500ce0878faf13f1a8d31da816e5db9b6af4690b505c8875d27b700f95
crates/yu-syntax/src/full_parse.rs 24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8
crates/yu-syntax/src/cursor.rs f08aae49fcf048ad11890def7ef9cadab56825a63b8d87db44821a792fe9b142
crates/yu-syntax/src/root_statement.rs c6d1dc49625d1687ff0dae8f6808f4c97c3f78398aae3bc061c44b6fc9661626
crates/yu-syntax/src/statement.rs fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797
crates/yu-syntax/src/cursor/recovery/emit.rs de091c117486f7990dc6872bf2ee7659c0e3e7e148e255f47b56b7836fe7c59d
crates/yu-syntax/src/lexical/item.rs 0a1dcbd84874f6abd571e0ce7035b9ba7682ebdf7c2348c030a1ba77deabcd25
crates/yu-syntax/src/lexical/current_item.rs 41efcce2b737a0362484e854a8549bda5f7bf0d2b911499553f1e449c6782a84
crates/yu-syntax/src/lexical/lexer.rs 97c69c86888784ee4b3eb04d8e4685f6370dbf451631c83ec1838fe7abfc36e1
crates/yu-syntax/src/lexical/expression_item.rs c981a994a11c539256ef34382c4ae154395e5d438371db4959e914df58aa8c7c
crates/yu-syntax/src/lexical/trivia.rs 887f1499fe63d870a70777626f0357c502a356d106c623d9a79e3596a17aba19
crates/yu-syntax/src/lexical/observation.rs 730e65947f889ef07014aa003eb846012d5cec6ae1434f77edf1cbd0e7096641
crates/yu-syntax/src/lexical/stops.rs edcf37bbe061c0966ba786d9090361c6c3befdbe3f99aa79f29271bd5230bf5b
crates/yu-syntax/src/literal/mod.rs d54b4ef01cb3c9d46048b5638f9837eb050816a5e7edd35460f20cf1e557fd40
crates/yu-syntax/src/literal/rule_literal.rs d21f7e27eb89dfa3c6717b895726e827974728be962faefcb08c9ce9092753ee
crates/yu-syntax/src/lexical/operator_scan.rs 145002d4254aaf186fa5176d0c6c56d89c88235e29e2da9ab1d33790a31ca3a2
crates/yu-syntax/src/operator_compilation.rs f1a5bd012f064d414d476acbc326c6a9804dc8128bf2e4f1800acb718a7d423b
crates/yu-syntax/src/syntax_environment.rs 3f1e2c97c49318e02c595aa739bfb48532f7631d38afaaac4d8dfca6142cb973
crates/yu-syntax/src/operator_table.rs 369ce0a3a8f5ac39da9da572cfe4fab6f61dd4ca07c554848cfcc44aa7051643
crates/yu-syntax/src/lib.rs 18709b87b1b761374b5b81f90fcbf37d001fd7d981597e889aef05ad3f230f93
crates/yu-syntax/src/header.rs cd3791144704226f67a05ae3d39aff9b42f4380073b3e9f9817951a493bce5ad
crates/yu-syntax/src/declaration/operator_header.rs 021e79529445054e5d54bfccf93d2287e94221a99e1554fbd7c715cb0706edbd
crates/yu-hir/src/lib.rs 5bdcb7c0df022da919cef5402c62dc1c7baf0700a4d06e526a608cbd7db21464
crates/yu-hir/src/module.rs 2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e
crates/yu-hir/src/module/local_source.rs ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5
crates/yu-hir/src/source_identity.rs aa97bc34be51644cf944b2813af47ad9243a8eb270850eeb6df34b9cddb3b3a2
crates/yu-hir/src/shadow.rs 2dffd7fd6542eed9fd3346e0672e76197c248be9c84334f341c4d612234b7ee9
crates/yu-solver/src/lib.rs 2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f
crates/yu-solver/src/shadow_apply.rs bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf
crates/yu-solver/src/shadow_candidate_source_crosswalk.rs 392d665579a74810134846e1274c0c9ce975a7eb0e2cfb9ad79a07af2cd2eeb0
```

Governing design pins retain the prior accepted-call sprint contract's cited
operator association, associated-chain ownership, simple-module admission,
direct-root behavior, ordinary successor carrier and inference-principles
documents. Any indispensable unpinned source dependency returns to Luna before
reliance. Process rules: `rules/goal-driven-sprints.md`,
`rules/design-authority.md`, `rules/testing.md`, sprint decision
`notes/design/2026-10-16-goal-driven-sprints.md` and
`tasks/agent-loop/README.md`.

## Sequence, exact leases and bounded resources

1. Astra / requested gpt-6-astra medium, at most 480s: source-constructor audit
   and symbolic source-key evidence. Exact write leases:
   `notes/theory/2026-10-17-choice-a-call-cst-source-key-audit.md` and
   `tasks/agent-loop/inbox/20261017-choice-a-call-cst-source-key-audit.md`.
   No numeric/runtime tree claims without execution. Rev2's added owners permit
   proving root wrapping, semicolon progression, statement selection, and
   accepted identifier/integer token emission plus trivia placement. Keep
   Restrict lexical derivation to this unfenced, single-line ASCII literal:
   current-Item assembly/EOF, statement and expression payload dispatch,
   statement keyword, identifier, integer, exact equals and semicolon scanners,
   ordinary horizontal-space scanning/observation, ML-gap classification and
   semicolon stopping. The three negative-branch owners establish that literal
   and dynamic-operator parsing do not take over these operands. Establish the
   actual effective operator table from the pinned empty syntax environment,
   empty header and operator compilation/table owners; `SyntaxEnvironment::empty`
   alone is not that evidence. Do not generalize to comments, Unicode, fences,
   strings or arbitrary layout. If an indispensable fact falls outside these
   function branches, freeze the exact residual instead of assuming it.
2. After confirmed STOP and frozen audit, Luna/high, at most 420s: exact
   successor contract. Exact write leases:
   `notes/design/2026-10-17-ordinary-hir-application-admission-successor.md` and
   `tasks/agent-loop/inbox/20261017-ordinary-hir-application-admission-successor.md`.
3. After the combined bundle is frozen, three sequential fresh independent
   reviews: spec auditor <=100s, compiler referee <=100s, architect <=100s.
   Review same exact artifact and direct dependencies. No author/reviewer
   overlap; freeze changed bytes as a new revision and delta-review findings.

Fresh sprint cap: 1500s total: source audit 480, design 420, reviews 300,
coordination 120 (including selector), reserve 180. One author or reviewer at a
time. Preserve all three inherited UNKNOWN leases and their reservations; do
not reclaim, overlap or misreport them. Authors report actual worker IDs,
requested/observed model metadata (UNKNOWN if absent), STOP and write cessation.

## Successor contract questions that must be settled

The contract must give a general supported grammar with nested/group
boundaries/exclusions; ordinary and opt-in API behavior; precise superseded
admission clauses; operand error ownership and order; recovery and unsupported
behavior; root/child occurrence allocation and stable prior identities;
source-key-to-node/artifact mapping; atomic publication/no partial structures;
all Apply producers and consumers, especially shadow inventory and ordinary
solver collection; work/storage bounds and failure disposition; and regression
obligations. It must account for headers versus ML expression tails, trivia,
grouping, malformed/recovered forms and direct-root behavior.

Any incompatible identity/error contract or unresolved observable semantic/API
choice is returned as concise alternatives with consistency and existing
language-spec impact. No choice is adopted silently.

## Non-goals, tests and stop

No source/library/compiler/test edits, test execution, Cargo/build, solver
acceptance, source T, original Call proof, soundness, principality, termination,
production promotion or final semantic/API adoption. No nested CLI or temporary
outputs outside exact leases. Design admission does not mean type inference or
Call semantics.

Stop at reviewed exact contract or exact unresolved choice, contradictory
authority, budget exhaustion or a new dependency/source-domain question. After
review, present the concrete contract and exact supersessions to the user for
explicit final approval before granting any code/test lease.

Closeout reports: (1) original theorem conditions genuinely closed (expected
0), (2) new compiler behavior/test evidence (expected none), (3) unproved item
and one next cut. The subsidiary HIR-APP-CST-1 source-fact may close if the
constructor audit proves it, but that is not counted as original theorem
closure.
