# R18 primary adjudication — variant type-argument correspondence blocker

Sprint: `FULL-PAPER-TYPE-SUBSTITUTION-20261025/r18`, contract r1 SHA-256
`d7c0e9b060687dd60aab5ded32f256f4675f71d1a2117df621c998266a9b69ac`.
Baseline: `e6ff152a983129edbdf3e4d3529d446a50844e38`.

## Disposition

R18 is **STOPPED_AUTHORITY_BLOCKER**. No variant typing or inversion constructor
was added. No mathematical counterexample was found or claimed. The variant
introduction/inversion gate and original full-paper simultaneous type-substitution
parent remain OPEN. R18's stop is local to the unresolved variant raw-syntax
correspondence; independently justified represented rules may continue in a new
bounded packet.

The worker stopped before proof construction under the contract's explicit stop
condition. The source-only handoff identifies the mismatch between manuscript
`t(\bar v)` at `docs/yulang-operational-type-safety-ja.tex:150–155` and rule
`t(\bar v) : <t_j(\bar A_j)>` at line 219, versus Lean
`Value.variant constructor typeArguments payload`. Neither that rule nor
`VariantFormed` defines the extra raw field's role. The two raw-object examples
in the handoff are discriminators of missing authority only; they do not assert
typing or rejection. No metadata, equality, declaration-instance or empty-list
semantics is adopted.

## Frozen evidence and review

- Worker handoff `tasks/agent-loop/inbox/paper-typing-subst-r18.md`, SHA-256
  `a54a797f1b9fecb658a21e7c10df48fb40dd718c5d18f75f7906b9cc7740382f`.
- Fresh independent source-only review
  `tasks/agent-loop/inbox/paper-typing-subst-r18-review.md`, SHA-256
  `66a36426649ee6b3000ca8703caeab620e714e23158411c7d23b6c120dcaa5a5`.
  Result: no blocking or major findings; reviewer confirms correct non-counterexample
  classification, preserved mappings, matching input hashes, and no overclaim.
- Both leased source modules match the frozen R18 input hashes. No scratch audit
  file or cache output was created.
- Lean/Lake calls: **0**. Checker seconds: **0**. R18's unspent call envelope
  does not transfer to another packet.
- Worker cessation receipt: no active processes or descendants; all writes
  stopped. Primary freezes the four exact worker paths after confirming source
  bytes, handoff and absence of generated scratch output.

## Remaining premise and next work

`R18-VARIANT-TYPEARG-CORRESPONDENCE-1` remains an OPEN Luna-owned premise: an
authoritative source must define how the raw variant `typeArguments` field
corresponds to the manuscript variant term and ordered row payload types, while
preserving the original supported source scope and its substitution action.
Until then, R18 cannot add a faithful variant constructor or claim transport for
it.

At sprint end the dispatcher recommended a new independent R19 candidate for
paper `wrap` introduction, inversion and wrapped-Call typing/transport. That
candidate does not resolve or consume the R18 premise. R19 requires its own
contract, exact leases, baseline/dependency verification and resource envelope
before any worker or checker invocation.
