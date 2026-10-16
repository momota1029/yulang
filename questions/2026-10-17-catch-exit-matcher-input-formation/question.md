# Catch outside matcher: complete typed input and entry formation

Question ID: `catch-exit-matcher-input-formation`
Question revision: `q1`
Predecessor/history: none; follows the reviewed research records listed below
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): working baseline `e0fa94e509d28eea9aa7d5884b5fa2b060363ca4`; source-design locators and immutable content hashes below
Task/thread locator: unavailable; the active conversation exposes no stable message/thread locator
Governing source/section: `notes/design/2026-10-02-typed-source-owner-realization.md` §6; `rules/design-authority.md` (“Design status” and “Approval and implementation gate”); `notes/design/2026-10-11-yulang-inference-top-level-principles.md`

## Requested scoped decision

For `CATCH-EXIT-INPUT-1`, identify the authority route for the complete typed operand telescope and entry judgment of the existing ordered `MatchRequest_H` relation at actual outside configuration `C_out`:

1. If an independently selected source clause already defines that complete telescope and entry judgment, identify its exact file, section and owning source-definition process so proof can derive the actual typed port incidence from the original yielded-request and exit derivations.
2. If no such selected clause exists, decide whether Luna should prepare a narrow source-definition proposal for independent review and later explicit user approval. Preparing a proposal would not adopt it, close the gate, or authorize compiler implementation.
3. Otherwise, keep this dependent gate blocked until a source-definition decision is available.

This question selects no matcher semantics and introduces no source rule. It asks which authority route governs the missing definition.

## Background and current premises

- The selected outside equation in `notes/design/2026-10-02-typed-source-owner-realization.md` §6 is:

  ```text
  H[Request(q,k)] = MatchRequest_H(q,k) >>= Finish_H(q,k)
  ```

  when `q` is eligible at the handler's boundary. `MatchRequest_H` is described as the existing ordered `BindPat` / continuation-binding / guard relation, ending in `Accepted` or `NoArm`. The same section says pending matching runs as ordinary bind outside the candidate handler and retains the original request and raw continuation. This document's header limits its selected authority to charter §§13–14 transport/lifetime and outside-selector extent; full source realization remains open.
- The section does not locate the complete independently typed operand telescope or entry judgment for `MatchRequest_H` at actual `C_out`, including raw-use, receipt, current-world and owner dependencies.
- `notes/design/2026-10-01-coupled-effect-interface-core-draft.md` is explicitly non-authoritative. It describes pattern binding and guard sequencing but leaves the source typing/elaboration boundary open.
- The CLEAN proof packet `notes/theory/2026-10-17-catch-matcher-input-constructor.md` (SHA-256 `ea0b96693114f9cbe9c8e6306b4dcff6fd522baef2c9076277de1a33801a2936`) builds a meta-level archival record with tagged embeddings and erases to the existing clause. It does not derive the matcher operand's typed domain at `C_out`; it counts no `CATCH-EXIT-INPUT-1` or F1 progress.
- The proof keeps historical eligibility indexed at yielded configuration `C_y`; after the actual exit, the handler's live incidence is false at `C_out`. It does not cast historical facts into current-world validity, create a new observation/admission, or assume a destination map/profile.
- The exact 138-byte research example now has a reviewed one-to-one relation between three retained `LocalSource::Apply` occurrences and three `CandidateSourceCall` records. Its reviewed run receipt remains partial HIR and preserves `UnsupportedItem` and `UnsupportedExpression`; it establishes no accepted source, full typing, handler adequacy, or matcher-input formation.
- `notes/design/2026-10-02-typed-source-owner-realization.md` SHA-256: `5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa`.
- `notes/design/2026-10-01-coupled-effect-interface-core-draft.md` SHA-256: `9eca7e45d1f0927397763481b0280bf54182408bd3c562aa2f6e80454f57ba3d`.

The user's current wording authorizes continuing proof and implementation in the existing goal; it does not select new source typing semantics. Interpretation: a new durable source rule still needs the normal independent review and explicit approval process.

## Options and consequences

### A. Point to an already selected source judgment

Identify the complete matcher-input telescope and entry judgment in an existing in-scope selected source clause, with its exact owner. The next proof may use only that clause's actual premises and must derive incidence at the original ports. No new rule or implementation authority is created. If the clause does not type the yielded/exit operands, the gate remains open at that exact missing derivation.

### B. Authorize preparation of a source-definition proposal

No existing clause is treated as sufficient. Luna prepares a narrowly scoped candidate definition for the ordered matcher operand telescope and its entry judgment at `C_out`, preserving the original `q`, raw continuation/future interface, historical eligibility index, current configuration, provider, receipt and owner dependencies. The proposal must retain `NoArm`, suspended matching and false/mismatching guards, and may not define its domain by successful matching. Independent design review and explicit user approval are still required before the proposal becomes authority; no compiler implementation follows from permission to draft.

### C. Keep this gate blocked

No selected clause is identified and no proposal is authorized. `CATCH-EXIT-INPUT-1` and dependent F1 work remain OPEN/BLOCKED; unrelated approved work can continue.

## Affected work

Blocked scope: deriving the Catch outside-matcher typed input, applying `theta_k` at this seam, source/native matcher-entry correspondence, and dependent F1 production claims.

Independent authorized work: none in the ended Catch sprint. The proof record, reviewed example and run receipt remain frozen; no further observational rerun is useful for this definition gap.

Required answer: select A, B, or C. For A, provide the exact authority locator and owner. For B, authorize only preparation of a proposal subject to independent review and later explicit approval. No choice closes any proof gate by itself.

Pending publication: this question directory remains unstaged and uncommitted. A separate answering conversation must prepare and display an identified answer draft for explicit approval; the questioning primary validates any finalized local answer and owns integration. Posting this question does not restart the stopped sprint or launch workers.
