# R49 Luna owner-map handoff

Sprint-ID `active-root-admission-20261019-r49`, contract revision 1, SHA-256
`6a8fa0a9f1189e247b6462b45083f814e0420ee53000f60b19d6d6ffcb3a57ff`.
Assignment `R49-LUNA-OWNER-MAP`, handoff revision 1. Parent: full inference /
evaluator theorem and original Simple-sub A/B, OPEN 0 -> 0. Baseline commit
`49f7680234ddfd2c9f3ad198c81a502ebdc916a1`; R49 activation commit
`a267651d139061a80f9f8ce81912841e2b5006e8`.

## Result

Frozen map: `notes/progress/2026-10-19-r49-active-root-owner-map.md`, SHA-256
`6cb3926f0fad89d6a220c8d7cff75353fd38d7faf5df6bc2c8632651ebd2652b`.

**Bounded `NO_SAFE_CODE_SLICE` for the unchanged scoped active-root path.** The
authoritative self-recursion rule requires an exact active monomorphic root
Link and excludes LocalScheme/FreshUse during initialization. Source scheduling
retains the active Name's `Action::Link`; the Apply also retains an exact
`LocalCalleeRoute`. The scoped authenticator ignores the Link and requires an
exact occurrence-indexed `LocalFreshRoute`, which is published only after a
Local capture/FreshUse route succeeds. No inspected authority says a monomorphic
Link satisfies that experimental gate, and no existing owner transfers such a
certificate. The first missing contract is the rule for authenticating an
active monomorphic callee at this consumer, bound to the exact occurrence,
root and active lifetime. This is not a claim that recursive application is
ill-typed or impossible under source semantics.

No source edit, fixture edit, build, test, Cargo, runtime or Git action occurred.
No code or semantic change is authorized by this handoff. The R48 obstruction
and no-test result remain intact. Sol's R49 proof lane is still RUNNING; this
handoff is the frozen implementation-side producer result, pending independent
review and Luna adjudication. The whole R49 assignment is not DONE yet.

## Evidence pins and resources

The active recursion authority, approved answer, R48 closeout and all six
pinned source/fixture files match the R49 contract. Exact hashes and owner
locations are listed in the frozen owner map. R48 commits: `6f848b778` and
`49f768023`; R49 start commit: `a267651d1`.

Requested lane: Luna/high read-only owner map. Effective model metadata UNKNOWN.
The 600-second map grant is charged; total R49 cap 2400s, currently 1500s
charged for proof and map, 900s remain for reviews/integration. Astra zero;
no verification process. CPU/RSS UNKNOWN.

Only the two R49 Luna paths were written. No descendants. **WRITES_STOPPED for
the owner-map lane.** Luna continues only as primary coordinator while Sol's
separate proof lease remains active.
