# Declaration retention R295: independent review and collision

The producer constructed a conditional declaration insertion/reference graph
and applied existing contribution consumers. Its original frozen module
`SourceDeclarationRetentionR295.lean` SHA-256
`deea4e7f8128ab9ad2caf7192bc4cb5b2ae16cc4c5682e01e85e7f13b1d92a1c` and
handoff `source-declaration-retention-r295.md` SHA-256
`04265891b5336538111b6b40dd8451b75a3395f0f3747601d7dcb76bd2a5c9bb`
passed isolated Lean 4.35.0 and independent 15-theorem/18-definition audits.
The handoff retains complete theorem types and axiom lists.

**Not source-safe or semantically equivalent as a general construction.**
Independent reviewer `/root/declaration_bridge_review` found that new forwarding
relations can also license an existing node sharing its root/declaration
identifiers. The producer confirmed that the current interface has no owning
node/route discriminator and that actual source freshness has not been proved.
No repair by assumption or source-domain restriction was adopted.

The reviewer then formalized the collision in
`SourceDeclarationCollisionR295.lean`, SHA-256
`f6adeff0b77f8b4fde72f4bb06e4176320911cc071b89d5ef65aba17e94bebc3`;
its handoff SHA-256 is
`b317ebc8c2a9f0a21b4bfa1d5224ec39466090d1f014b591291e2b69b356bf38`.
Six theorem audits passed Lean 4.35.0, each with `propext`. Independent
`/root/declaration_parent_audit` checked the example and all recorded hashes:
the same unchanged old node has no old contribution but gains one after the
relation extension, with the same packet and joint row. This refutes generic
reflection, not old-witness inclusion or authentic source semantics. The
example uses an arbitrary graph and does not establish a source-language defect.

`retainContribution` preserves witnesses only within the installed graph; it
does not transport all old graph-indexed operator evidence. Complete source
scope/substitution legality, original declaration authentication, staged EI,
and a valid noninterference proof remain open. R159 checking/admission and
all other premises remain independent; parent delta is zero.

`/root/r295_viewlogic_review` separately accepted the bounded stop report
`computed-call-viewlogic-r295.md` (SHA-256
`0b5cbc638eab26a46f6109ba25b689c4e661701aa9415feef8b75fb62cea7f5a`).
It checked the recorded existing theorem audits and confirmed that no authentic
EI payload or arm inventory was constructed. No new semantic decision,
source/native correspondence or production permission follows. All workers and
reviewers stopped; the reviewers did not write repository files or perform Git.
