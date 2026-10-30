# EFFECT-PERMISSION-NATIVE-INCIDENCE / R42

Status: primary-admitted bounded implementation/proof sprint. This packet addresses only the actual native-term realization of R41's registration-labelled Lambda argument-effect incidence for an exact module definition-use and its FreshUse context.

## Original gate and success evidence

Parent: annotation-effect permission/inflow/subtraction obligation in `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1, 1.1–1.2, with original source domain and quantifiers unchanged. R41 established a finite constructor/capture/FreshUse model and reviewed passive Rust incidence coordinates, but `R41-NATIVE-INCIDENCE-REALIZATION-1` remains OPEN.

Success requires a private, read-only Rust adapter that, for a retained module `FreshRoute`, obtains the actual reconstructed positive Function and argument-effect Terms from the exact `FreshUse.terms` map, checks `TermStore::term_view` reports the Function's `argument_effect` as that exact child Term, preserves its registration label, mapped row and exact definition-use/context identity, and returns no certificate when any component is missing or mismatched. The proof lane models successful extraction and proves that each decoded record has these incidence/use properties, with two different registration labels remaining distinct when row/term images coincide. A fresh reviewer independently traces the Rust fields to `TermView` and the explicit Lean extraction premise.

Before/after evidence: before R42 there is no retained relation from the R41 mapped child node/row through `FreshUse.terms` to the actual native `PositiveFunction.argument_effect` field under the same module use/context. After R42, the private certificate is present only where all actual fields agree; absence remains non-evidence.

## Fixed authority and source snapshot

- Branch `yulang3`; R41 checkpoint `d2a58b791a1a1823f5cea5663d74d572e768be13` is pushed. State-only follow-up commits are described in R41 outcome.
- R41 review: `effect-permission-lambda-incidence-r41-review.md`, SHA-256 `33808a855db179bb7c51cb65f9703a556d05b2dd0445de0b20440ba880d50056`.
- R41 Lean model: `LambdaArgumentEffectIncidenceR41.lean`, SHA-256 `af7c2e3def8762287e95827896dc01d982954059bff09c476d1a94df94c0a79e`.
- Dirty admitted `candidate_scheme.rs` baseline for this sprint: SHA-256 `3cd9dd2d0f55412636dc88bc658d7cfbc23aad6304b90f2ba95247f8d58e1d22`; preserve every pre-existing byte/hunk and all committed R41 code.
- Read-only `term.rs` containing `TermView::PositiveFunction { argument, argument_effect, result_effect, result }` and `TermStore::term_view`: SHA-256 `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`.
- Read-only forwarding/accessor `lib.rs`: SHA-256 `b1dac8bd244e282ff42a2d580e237393153f9b912c6ac0adf110367def5c79ce`.
- Read-only constructor/provenance `candidate_context.rs`: SHA-256 `030fcb4b6571c0db8a670d12d8a67fe8fcf465484502fe5b11b6d057e8026c38`.
- R40 structural FreshUse source characterization and PASS are linked from R41 review/handoff. No broader repository-absence claim is admitted.

## Rust implementation lane

One writer: `/root/r42_rust`, implementer Luna/high, ≤1,200 seconds. Write only:

- `crates/yu-solver/src/candidate_scheme.rs` — private native-incidence extraction from the exact completed module `FreshUse`, and fallible retained-byte accounting if a new owned record is necessary;
- `tasks/agent-loop/inbox/effect-permission-native-incidence-r42-rust.md` — sole handoff.

Read-only inputs are the frozen R41 artifacts and the pinned `term.rs`, `lib.rs`, `candidate_context.rs`. Do not edit `term.rs`, `lib.rs`, `candidate_context.rs`, candidate consumers, tests, fixtures or diagnostics. Preserve existing rows and duplicate registration labels. Do not compare two copied metadata fields as proof: reconstruct the actual Function and child Terms from the exact `FreshUse.terms` coordinates and inspect the native Function through the pinned `TermStore::term_view` accessor. Include the exact `DefinitionUseId` and the same `context_use` owned by that FreshUse/route.

If the extraction is absent, mismatched or unavailable, omit the certificate and leave ordinary routing/inference unchanged. Do not add an equality-only permission consumer, propagation edge, provider arrival, Catch subtraction, new public API, or user-visible semantic rule. Account for retained allocation and fallible failure without exposing partial certificates. No build, tests, Cargo, Lake, formatter, environment, worktree, target, cache or scratch file.

## Constructive Lean lane

One writer: `/root/r42_proof`, registered `lean_prover`, ≤1,200 seconds. Write only:

- `notes/theory/lean/YulangClosure/NativeIncidenceAdapterR42.lean`;
- `tasks/agent-loop/inbox/effect-permission-native-incidence-r42-proof.md`.

Use R41 as an import-free copied/embedded finite dependency in stdin if required; do not edit/import-install or create Lake/cache artifacts. Model exact input coordinates, actual term observation and use/context identity. Prove: successful extraction entails the same registration-labelled R41 child and mapped term; foreign or mismatched use/Function/child observations produce no accepted certificate; shared row or Term images do not merge labels; each accepted module record names the supplied definition-use and context stamp. State Rust source correspondence as explicit extraction premises; do not claim a verified Rust interpreter, provider arrival, Catch subtraction or parent theorem closure.

Run the installed pinned Lean 4.35.0 executable by bounded read-only stdin, retaining complete `#check @` and `#print axioms` for every theorem. No `.olean`, Lake cache, build, tests, scratch or environment. One CPU, 1 GiB, 120 seconds per invocation.

## Independent review and integration

After both writers stop and hashes freeze, one fresh independent reviewer gets ≤900 seconds. Reviewer must inspect the exact source reconstruction and `TermView` comparison, failure/no-certificate behavior, definition-use/context identity, allocation/accounting, proof theorem types/full axiom sets, shared-image/foreign-use falsifiers, exact dirty-baseline isolation and omitted boundaries. Sole review output: `tasks/agent-loop/inbox/effect-permission-native-incidence-r42-review.md`. Luna persists the reviewer receipt if the selected read-only role cannot write. Reviewer must not be an author/coauthor.

Luna ≤900 seconds including adjudication, state update and ≤500 seconds closeout. Total sprint reservation 4,200 seconds: Rust 1,200; Lean 1,200; review 900; primary 900; Astra 0. Existing checkout only. No worktree/environment/cache/target/scratch. At most two active producers plus reviewer/integration reserve.

Stage only the independently reviewed R42 source delta and exact R42 proof/review/state records, preserving all existing dirty bytes. If the R42 delta cannot be isolated safely from the admitted dirty `candidate_scheme.rs` baseline, commit the coherent Lean/research artifacts alone and retain the Rust delta uncommitted. Only Luna may stage, commit and push. Never force-push.

## Explicit non-goals and open owners

No permission consumer or semantic change. No provider-arrival path, Catch/residual selection, subtraction, source-wide hygiene, original Simple-sub A/B closure, whole-language soundness, principality, progress, termination or production promotion. `R42-NATIVE-INCIDENCE-REALIZATION-1` is a bounded extraction interface under explicit field assumptions, not full compiler execution correspondence. If the actual `FreshUse` route cannot preserve definition-use identity at the exact adapter point, stop and report the missing source owner instead of inferring it from row equality.

Next consultation trigger: an actual source-owner mismatch, new required write path/dependency, counterexample, lane blocker, review finding, or this sprint's closeout.
