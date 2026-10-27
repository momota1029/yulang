# Formal permission projection r2: source boundary receipt

Status: INCOMPLETE; conditional source derivation only; investigation and writes STOPPED after this handoff. No source-qualified counterexample, unconditional endpoint-image theorem, Lean result, semantic change, permission activation or promotion.

## Objective, method and pinned dependencies

Trace the original constructor-selected effect endpoint through shape capture, retained negative roots, permission export and its first permitted consumer. Method: static inspection of the four admitted Rust owners; no executable experiment. The parent gate remains OPEN. This is complementary source research, not the main constructive theorem obligation or independent review.

Baseline supplied by the primary: `4faceaf572c7c7f35f31d31a37c30d4afa51ec1d`; not independently resolved through Git because Git was prohibited. Contract SHA-256: `34cd037c944d067b94b3ab89aadbf7cdeb2153bb3afcd48fbd2d497f58ef0877`.

Observed SHA-256 values match the contract:

| Dependency | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `tools/inference-playground/src/scheme.rs` | `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |

Governing semantic sections are the pinned policy's §§1, 1.1, 1.2 and 4: composed polarity; negative concrete annotation grants local permission without a closed input bound; permission, actual inflow and residual remain distinct; row equality does not confer annotation authority. §6 withdraws its example result. None of these meanings is reconsidered here. Root instructions and `rules/research-lab.md`, `rules/design-authority.md`, `rules/git-concurrency.md` were read. The research-loop skill is primary-only and authorizes no worker delegation.

## First missing source premise and stopping point

Let `r` be the fresh port selected at `candidate_effect.rs:1502` for a concrete negative permission. The first unproved equation in a forward source derivation is the read-back law

```
term_view(live_effect_term(p, r))
  = LiveVariable(kind = Effect, polarity = p, ordinal = r).
```

The call at `candidate_effect.rs:1544` supplies both signs, but none of the four allowed files defines `live_effect_term`. Successful capture only checks the term view it receives; it does not prove this constructor's original-row read-back equation. The responsible API owner is `InferenceSession::live_effect_term` together with the term store's `term_view`; its implementation path/hash is UNKNOWN within this admitted read set. No unlisted source was opened to locate it.

The next required laws are read-back of `positive_function_term(an, qan, qrp, rp)` and `negative_function_term(ap, qap, qrn, rn)` into exactly those four fields, and tuple constructor read-back in original element order. Calls occur at `candidate_effect.rs:1486` and `1454–1455`; their implementation laws are also not established by these files. Do not replace these equations with an assumed desired endpoint-image invariant. A successful query with a well-kinded but wrong original port would not establish original-port identity.

Investigation stopped at this ownership boundary. The remaining text records only visible source structure and an explicitly conditional derivation; it is not a request to reinterpret language meaning or add a certificate.

## Source facts and conditional derivation

1. **Constructor metadata and shared port.** `FormalPermission` stores parameter index, original occurrence, annotation owner/scope, full path, source row and cloned concrete operands (`candidate_effect.rs:237–245`). The negative concrete branch allocates one fresh row `r` (`1501–1502`), copies path and operands (`1508–1513`), then records occurrence/owner/scope/source row separately (`1522–1530`). It returns positive and negative live terms from that same local `port` (`1544`). The record does not retain `r` or either term. Therefore the shared original port is a fact about constructor arguments, not an independently stored endpoint certificate.

2. **Path and polarity bookkeeping.** Formal construction starts at negative variance (`1658–1660`). Tuple elements preserve variance and append their exact index (`1433–1455`); empty tuples and immediate element effect rows are rejected (`1434`). Function recursion reverses variance for Argument and preserves it for Result (`1461–1485`). A permission is generated only for a nonempty concrete, variable-free row at negative variance (`1501`). The returned pairs use `(an, qan, qrp, rp)` and `(ap, qap, qrn, rn)` (`1486`). Thus, conditional on constructor read-back, starting at the negative root and following the retained Function/Tuple path selects the original row's negative term at every permission endpoint. Argument/Result spelling alone does not determine that sign; composed variance does.

3. **Publication and root retention.** On the successful visible branch, the paired annotation is linked to the parameter (`1672–1677`), permissions are drained into the algebra, and the returned `negative` term is stored under the parameter (`1687–1692`). This establishes what this publication writes. It does not establish absence of subsequent replacement/retirement before a later export. Capture retains only actual negative Function/Tuple domains whose exact endpoint key is already present in `capture.endpoints` (`candidate_scheme.rs:2783–2799`). It does not unconditionally seed every permission domain. The pending-node loop expands queued endpoints (`2670–2676`); separate retained demand roots can also be seeded (`2684–2687`).

4. **Capture's represented image.** `intern_shape` canonicalizes the value/effect endpoint, records shape effect rows, then calls `intern`, which canonicalizes again and reuses an existing endpoint index or allocates a new one (`candidate_scheme.rs:1713–1737`). This is merging by the endpoint keys actually returned by those calls. No injectivity, canonical idempotence or equality of raw row identifiers is inferred. Effect-row expansion uses `row(RowKey::Effect(i))` (`1939–1941`); `row` obtains an intrusion representative and reuses the represented row (`1739–1764`). These are separate node interning and represented-row operations.

5. **Shape expansion.** Function expansion reads the term's four fields (`1973–1999`), checks its expected polarity (`2001–2007`), uses kinds `[Value, Effect, Effect, Value]` and polarities `[opposite, opposite, p, p]`, then stores exactly their `intern_shape(term_endpoint(...))` indices (`2013–2027`). `term_endpoint` checks Effect live-variable kind and sign and uses its ordinal (`1797–1827`). Tuple expansion checks arity and preserves element order and polarity (`2068–2083`). The field/element read-back premises in the preceding section are needed to connect these read terms to the original constructor arguments.

6. **Export lookup and identity.** `formal_effect_permissions` filters retained permission records by their original definition owner (`shadow_apply.rs:2643–2649`); it looks up the current parameter domain and then the exact retained root (`2651–2652`). Each Element selects the indexed tuple child (`2658–2663`). Argument selects value/effect children `[0]/[1]`; Result selects `[3]/[2]` (`2665–2678`). The final effect child must be a Row whose represented kind is Effect (`2680–2686`). Export borrows the original occurrence, source row and concrete operands, copies the same path steps and constructs the returned node with that graph's exact `port_index` (`2688–2693`). Its identity is this returned handle's state/graph/index, not a display coordinate or an effect family. No deduction from canonical row equality to annotation authority is used.

7. **First permitted consumer.** `CandidatePublicScheme::project` assigns node IDs to graph handles (`tools/inference-playground/src/scheme.rs:104–113`), requests the permission list (`185–188`), rejects an empty path, requires the exported handle in the node map, and resolves that very handle to an Effect row (`190–196`, with `effect_tail` at `95–100`). It retains `Permission { source, tail }`. Rows may be coalesced according to graph row keys with kind/locality checks (`79–94`); `coordinate` is a display coordinate (`18–21`). Row coalescing is not a proof that two original permission endpoints or occurrences are identical. This consumer observes a scheme projection; no subtraction activation follows.

**Conditional conclusion.** Assume (A) the missing live-term, Function and Tuple read-back laws; (B) the relevant algebra record/domain and original terms remain applicable across construction, capture and export; (C) the capture endpoint canonicalization/store operations preserve the successful structural associations used above; and (D) capture and `formal_effect_permissions` both succeed. Structural induction on the constructor's retained path then yields exactly the same node index as applying capture's actual shape-interning operation to the original selected Effect endpoint with composed polarity Negative. Tuple steps preserve the induction relation; Function steps choose the same ordered value/effect fields; final export returns that stored effect child index. This is a conditional source derivation, not establishment of A–C. In particular A is the first missing premise. No Lean file was read and no claim about the frozen Lean model or its axioms is made.

## Missing-root semantics and falsification limits

A negative domain absent from `capture.endpoints` is silently omitted from `negative_formal_roots` (`candidate_scheme.rs:2796–2799`). A later owner-matching permission then fails root lookup with `ArtifactMismatch` (`shadow_apply.rs:2652`), and the first consumer translates it to `candidate scheme permission projection unavailable` (`scheme.rs:187–188`). Missing domain, empty path, invalid shape/index, terminal tuple step, non-Row final port, wrong component kind and allocation failures likewise return errors before a successful list is published (`shadow_apply.rs:2646–2686`). A local partially accumulated vector is not returned on those branches.

That behavior is projection unavailability, not a successful counterexample. No end-to-end successful construct/capture/export witness returning a node outside the original captured image was established. No claim of absence of such witnesses follows from this inspection. Root coverage is not needed as an unconditional theorem for the successful-export invariant, but original-port read-back and lifecycle correspondence still are.

## Checks, coverage and STOP receipt

Commands: `sha256sum` on the contract and five pinned dependencies; bounded `rg -n` searches and `nl -ba ... | sed -n ...` reads of the four Rust owners; `cat` of the pinned policy and required operating instructions. Every admitted dependency hash matched. Some broad combined command output was truncated; specific constructor/capture/export/consumer passages used above were reread in bounded output. This is not an exhaustive review of each file.

Oracle independence: no Oracle was executed or inspected separately. The policy's Oracle mapping is accepted contextual evidence, not an independently reproduced result. No checker was authored; no assumed transition machine was presented as proof of source rules. Shared assumptions A–C remain explicit. Seeds/ranges/mutations: none; this was static source inspection. Coverage: the visible formal Function/Tuple constructor, capture representation, root lookup, export walk and playground projection only. Omitted: helper implementations, canonicalization/representative implementation, term store implementation, other consumers, full source admission, intervening lifecycle/rollback/replay, Lean model and native/executor correspondence.

No Cargo, Lean/Lake, tests, compiler probes, network, Git commands or descendants. One leased Markdown output; no compiler, test, runtime, shared-state or other worker file changed. No parallel heavyweight process was run. Actual CPU usage, peak RSS, elapsed wall time and model/effort observations: UNKNOWN; no resource measurement was performed. The task's limit was 200 seconds, one CPU, 1 GiB RSS; this receipt does not invent measured compliance values. Research stopped because a required source fact is not derivable from the admitted owners. Artifact is frozen upon submission; review status is UNREVIEWED, producer-authored.

Recommended next action: primary admit a bounded source-owner packet for `live_effect_term`, the Function/Tuple constructors and `term_view`, with exact paths/hashes, to establish or refute the original-argument read-back equations before any new Lean bridge. Keep the existing semantics and parent gate OPEN.

## Commit packet

- Exact leased path: `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r2.md`.
- Baseline SHA: `4faceaf572c7c7f35f31d31a37c30d4afa51ec1d` (primary-supplied).
- Dependency hashes changed: none observed; all five matched the admitted hashes above. No final rehash was performed after the STOP boundary.
- Review: UNREVIEWED; frozen at submission; no independent review claimed.
- Checks already run: dependency/contract SHA-256 matching and bounded static source inspection only; no executable checks.
- Proposed commit message: `research: record formal permission projection read-back boundary`.
- Shared-record deltas left for primary/curator: record r2 as INCOMPLETE source evidence; record the original live-effect/shape read-back owner gap; retain r1 and all parent/production gates OPEN; appoint a fresh reviewer only for an admitted reviewable claim. No shared record was edited.
