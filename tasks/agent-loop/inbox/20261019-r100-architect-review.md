# Post-R99 architecture/source-law audit

Reviewer: `/root/r100_architect` (read-only; no tests, edits or Git).

## Receiver replay

No safe R100 production correction that creates authentic receiving authority for fresh owner `uI′` is established. The inspected path is:

- `machine.rs:980–1009`: ordinary Computation entry calls `Receiving::enter` and records the original formal receipt.
- `machine.rs:1719–1759`: propagation retires original inner owner `uI`.
- `machine.rs:1309–1378`: capture retains owner, ForwardHandler, historical View and original local suffix.
- `machine.rs:1403–1436`: replay mints fresh executable owner `uI′` from original call/provider descriptor.
- `machine.rs:1439–1467`: replay installs the handler at `uI′` but replays the old view/receipt.
- `receiving.rs:230–325`: Grant requires active exact owner, that owner's boundary/schema, authentic same-view receipt and reachable image; boundary lookup fails for `uI′`.
- `machine.rs:1580–1598`: absent positive evidence produces HandlerEvidence.

The raw-resume correspondence `notes/theory/2026-10-16-runtime-resume-template-correspondence.md` §5 and its table explicitly prohibit fabricating `Receive(new owner, old view)`; a saved View packet is not a newly executed Name. The R99 suffix supplies local publication, local read and an operation Call, but no new computation-formal entry. A new Name receipt alone would still lack a reachable image for `uI′`.

A possible research constructor would preserve the exact original boundary/schema, authenticate the original view/receipt and its owner/image, then mint fresh receiver-specific view/receipt/execution with original schema/slot/formal/value and historical ancestry. This is unverified source-law research, not implementation authority. Copying schema only, reactivating `uI`, borrowing sibling evidence, or reexecuting closure entry are rejected. The R99 negative changes operation mismatch before Grant and cannot test sibling permission; an additional hypothetical control would use inner `[] int` and outer `[io] int`, with preparation/outcome unobserved.

## Method/role source evidence

The independent next lane is authentic implementation-member body/formal source correspondence for exact source:

```yu
role SecondInt { my second: int -> int -> int }
impl int: SecondInt { my second self selected = selected }
my answer = SecondInt::second 1 2
```

R95 proves only declaration/association identity. R85's P2/P3 remain open, R85 remains Draft/unadopted, and no executable member-root/admission decision follows from this audit. A structural source-member proof can advance immediately without selecting lookup, typing or dispatch law. Actual result `2` still depends on P1/P3/P4 and R85 adoption.

No parent theorem or production gate closes. No edits, tests, build, CLI, Git or descendants.
