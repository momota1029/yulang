# Question: adopt the bounded source-owned registry API for `invoke`

Question ID: `source-owned-registry-adoption`
Question revision: `q1`
Predecessor/history: the adopted construction-design gate in `call-reify-registry-construction/q3`; no prior adoption question
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `18049fc9af145ebf558fa189503df07d5c2b9191`; reviewed candidate integrated at `fdda52fd8`, frozen artifact SHA-256 `9bc209159fee600ed7bc3e389ceef54aeaaa72c7e9f67235e4fc9e2a5c26cfbb`
Task/thread locator: current user task; no stable external identifier available
Governing source/section: `notes/design/2026-10-10-source-owned-registry-design-gate.md`; `notes/design/2026-10-10-original-registry-constructor-adoption-proposal.md` §§1–4; `notes/design/2026-10-11-yulang-inference-top-level-principles.md`

## Requested scoped decision

The current source rules give an unannotated formal `f` its ordinary Value role and `Desc`, but the original `Entry-Value` rule consumes a `ParameterOrigin` plus received-carrier, entry, receipt, Force and rebind ports. No selected constructor supplies their complete original introduction signature and ordered application at `my invoke f = f 1`. The reviewed source-owned registry candidate constructs a complete pre-Call spine in a new API, but does not prove that API is the existing original registry interpretation. The user-approved q3 gate authorized design and review only; it withheld adoption.

Choose whether to adopt the exact six bounded source-owned registry/API choices in `notes/design/2026-10-10-original-registry-constructor-adoption-proposal.md` §§1–2 for the resolved nonrecursive formal/Name/Int pre-Call fragment. The complete Call contract stays fixed. Adoption would select this candidate representation for that fragment; it would not claim equivalence to a separately fixed registry or complete Call, and would authorize no implementation, `f 1` acceptance, solving, publication, principality closure or F5 cutover.

## Background and current premises

- The reviewed candidate `notes/theory/2026-10-10-source-owned-original-registry-construction.md` constructs the formal owner, typed ports, registry, lookup/decoder, formal entry, callee Name/Result and literal Data/Result in its own interfaces. The construction uses finite source/schema syntax and preserves ordered dependent fields, aliases, absence and full consumer interfaces.
- Its mathematical and specification delta reviews passed. It is explicitly research-only and unadopted. The review records in `notes/progress/2026-10-10-original-registry-construction-review.md` distinguish candidate theorems from conformance to the existing original API.
- The constructive audit of `my invoke f = f 1` found the missing original formal introduction first; granting that registration moves the next cut to the old `P_old` key/payload/lookup/decoder and consumer-closure correspondence. The fixed complete Call still requires whole-argument compatibility at the same returned provider, complete emission/admission, solving, generalization and principality.
- The approved q2 Reify direction remains adopted as a bounded construction direction. The unadopted `RuleCall_L`/`CertCall_L` extension is not part of this question.
- User's current task asks for correct, natural and efficient Simple-sub inference, while also saying not to change approved designs without authorization. This question asks only about adopting the exact reviewed registry representation candidate; it does not change Simple-sub constraint generation or solving policy.

## Options and consequences

1. **Adopt the exact bounded candidate API.** Select its six choices for the stated pre-Call fragment and continue source-constructor conformance against actual Parameter/entry/Force/rebind, Int, Return/Prefix, scope/reference/world declarations. This supplies an explicit source-owned representation to test, but does not establish that the old fixed API or any complete Call consumer agrees with it.
2. **Keep the existing original API fixed.** Do not adopt the candidate. Continue looking for an already selected original formal-origin/port introduction and exact registry representation evidence. If none exists, `invoke` remains blocked at the complete-Call source bridge.
3. **Defer this Call path.** Preserve the candidate as reviewed research and continue only inference gates independent of formal-origin/registry conformance. `invoke` remains unavailable on the complete-contract path.

## Affected work

Blocked scope: adoption or rejection of the reviewed source-owned original registry/API candidate for the stated pre-Call fragment.

Independent authorized work: the private `my bridge x = 1 1` conflict regression and independent solver/type-inference work whose source domain does not depend on this registry choice. The conflict-to-public-acceptance boundary and F5 replacement remain open.

Required answer: select Option 1, 2 or 3, or give another bounded direction. No compiler change, `f 1` acceptance, complete Call closure or F5 cutover follows from this decision alone.

Pending publication: keep this entire question directory unstaged and uncommitted until the questioning primary discovers and validates an explicitly approved local answer and commits the matching question/draft/answer together. The answering primary never mutates Git. Posting does not pause the goal; dependent work waits while independent work continues on disjoint owned paths.
