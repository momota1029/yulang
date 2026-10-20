# R183 sample-path readiness — Luna-owned prospective packet

Status: candidate; no compiler edit, execution or semantic choice authorized.
Full goal remains proof-backed inference/evaluator implementation and broad
unchanged Yulang2 Web-sample compatibility.

## R147 braced-if path

Reviewed decision inputs:

- `notes/design/2026-10-20-braced-if-compatibility-r147.md`, SHA-256
  `2dbbf05c2c74810c4684a71d81933d4b6b4a9be2067dcc60b943bb090ff64f12`.
- `tasks/agent-loop/sprints/braced-if-approval-packet-20261020-r147-rev2.md`,
  SHA-256 `87ec019b57a2e885bff6aab5e7cf16929526ebb07df593646f495442184ff281`.

The unchanged 388-byte `web/playground/examples/yulang2-ordinary-islands.yu`
contains braced `if` and `else` arms and expects `countdown_result -> 8`.
Option A covers one non-record expression and rejects other shapes. Option B
covers ordinary non-record expression lists, explicit record forms and at most
one operand-bearing record spread, while explicitly rejecting malformed,
duplicate-spread and mixed non-record-spread cases. The decision recommends B
for breadth, but no exact option/revision is approved. The next required action
is to obtain the user's exact semantic option before a separate reviewed
implementation contract; no code is authorized here.

The post-decision owner envelope must cover parser/CST recovery and dedicated
braced-arm ownership, HIR arm-list representation and source identity, inference
sequence/record consumers, ordered runtime semantics, CLI selection, WASM API,
Web sample selection, unchanged sample and expected output, focused tests and
preserved smoke expectations. The authorized decision packet already lists
the direct owners and its pin set; a follow-on contract must revalidate the
baseline and owner hashes and ensure the complete chain is leased atomically.

## Independent sample barriers and sequencing

- R167 note `notes/theory/2026-10-20-r167-module-schedule-proof.md`, SHA-256
  `f24e69f293d7f56c663a6e3ebdb64b41b7eee9bf94ceda710ab942d82e8ccb8a`, leaves
  Case initializer classification `R167-CASE-FETCH-1` open. This blocks its
  dependent public whole-module entry, not R147's selected-definition path.
- R149 rev10 contract SHA-256
  `31214917352b673c7467873b60d5db8e470e4d16c8370d882c266a7fcef5b3e9` targets
  Types/Console and retains authentic imports, role prerequisites, tuples,
  primitive type construction, source-order initialization and host publication
  obligations. It is a separate broader sample route; R183 supplies no closure.
- The R147 unchanged countdown route is the nearest sample increment with a
  concrete expected output and a reviewed end-to-end owner map. It can proceed
  after exact semantic approval and a fresh implementation contract; it does
  not depend on silently classifying Case or completing Types/Console.

No Yulang2 executable or dirty oracle checkout is needed for this readiness
result. R147/R167/R149 artifacts are the pinned evidence. No source inspection,
test, build, CLI, WASM, browser, evaluator or compiler execution is authorized.

## Result and next boundary

No sample path is activated by this packet. Preserve R147's recommendation as
the concrete decision requested from the user after the readiness packet and
its review are frozen. Upon exact approval, Luna should dispatch a separate
complete implementation contract covering parser through Web and the unchanged
fixture, while the original proof goal continues independently. R167 and R149
remain open on their own lanes.
