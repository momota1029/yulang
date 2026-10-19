# R109 compiler/source review

Verdict: **CLEAN within R109's frozen scope.** No blocking, major or minor
compiler/source findings.

The reviewer checked current constructor, receiving, handler and request paths
directly before using producer explanations. R109 authorizes a finite
observation; it does not claim to repair or discharge R101's missing static
source-entry proof.

- All 16 current input pins match the contract. Current `program.rs` SHA-256 is
  `7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a`.
- Historical reconstruction succeeds without Git: remove the appended
  `#[cfg(test)] mod tests` beginning at `program.rs:978` and its separating
  blank line, retaining the original final LF. The SHA-256 becomes exactly
  `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11`. This
  verifies byte equivalence of the retained production prefix; commit
  attribution was not inspected.
- `program.rs:414–566`, `local_source.rs:596–652,818–844,894–938,1091–1186`
  support the conditional formal ownership, ordered arms, distinct operation
  identities, grouped argument and retained Apply-site construction.
- `primitive.rs:31–37` rejects constructed Lambdas, so these cells require
  positive receiving grants.
- `machine.rs:1531–1705` compares exact operation identities and commits
  shallow selection by popping the delimiter before evaluating its arm. The
  fresh arm request follows the ordinary operation/result-consumer path.
- `machine.rs:1719–1760` restores invocation ownership and ends execution views
  during forwarding. `receiving.rs:227–334` authenticates historical
  observations and joins the candidate's receipt of the **same view**, while
  requiring that candidate invocation to remain active. This supports the
  outer grant after inner-owner unwind without invented inherited image
  coverage.
- `machine.rs:1789–1803,1924–1957,1763–1775` preserves the request Apply
  SourceSite through carrier creation, event creation and outward forwarding.
- The unchanged test is type/source plausible. It checks integers 11/23 and
  outward tick identity, payload 11 and `::tick 11` range. It does not directly
  establish event inequality or full SourceSite root/occurrence identity;
  R109 preserves that distinction.

Reviewed output hashes:

| Artifact | SHA-256 |
|---|---|
| Contract | `834bf38f690b9fa9fc617a57e40e1c09bbce996949176aafdf5f6e995bc8eb43` |
| Proof note | `bf540b6e44f4c490f08c7afd83b276b0105b4d6d70ef156f4786625d28e0b8c6` |
| Proof handoff | `bb1c3da475fdcda98b83e3fd7bc3c0c1328be796502b1edf14d337974b27059b` |
| Implementation inventory | `32094364786d9700bd449dfb4a8992c68d33cc23d5bf0a27c0710ccd5d0ae24e` |

R101/R102 remain `NOT_RUN`; `R101-ENTRY-1` remains `OPEN`. No stale
historical pin was treated as current.

Reviewer: `/root/r109_compiler_review`, independent read-only compiler/source
review. No files written; no tests, builds, compiler/runtime, formatter, Git or
CLI execution. Luna recorded the complete receipt returned by the reviewer.
