# R111 rev1 pre-edit spec review

Verdict: **MAJOR**. Rev1 is blocked; no producer or command is authorized.

Reviewer: `/root/r111_pre_spec`, independent read-only review. No edits,
tests, builds, runtime execution or descendants.

- **Incorrect exact-source provenance.** Target: rev1 contract lines 11–22,
  with repeated claims at lines 11–13 and 52–57. Cell A omits
  `my forward (pending:[signal] bool) = receive pending`, which is
  unconditionally present in the pinned source at
  `tools/inference-playground/tests/runtime_receiving.rs:342`, including when
  `forwarded == false` (lines 338–339). Authority: contract lines 11–13
  require unchanged existing recipes; `rules/design-authority.md`, “Authority
  order” and “Test contracts,” prohibit replacing confirmed evidence with
  implementation convenience. This is a contract/source-correspondence defect,
  not an approved semantic change.
- **Closure required:** issue a versioned contract preserving the exact
  direct-receive Bool recipe, update its source byte length/hash, and obtain a
  fresh pre-edit review before any producer starts.
- Actual existing Cell A: **255 bytes**, SHA-256
  `04d30eddc08b8ec472b2f969a947876cf235fb15a9576de574833fa673504cd5`, no
  final LF. Rev1's proposed 202-byte source/hash was internally correct but
  described a different recipe. Cell B matches the existing literal at
  `runtime_receiving.rs:353`: 224 bytes, hash
  `cdb662794420240f96490ff26a3ad29ee5f0726c3adca2936a7e7a730cd0a3e7`, no
  final LF.

Other checks: all 13 frozen input hashes match; existing runtime assertions
support the finite expected final Bool `false`; B distinguishes Int operation
response `23` from final Bool. CLI routes support `false\n` and empty stderr.
The command, one-shot/no-repair rule, test-only leases, R99 exclusion, preserved
R109 failure, finite limits, breadth and resource arithmetic are explicit.
No existing expectation, diagnostic or semantic test name is to be changed.

Revision reviewed: `tasks/agent-loop/sprints/cli-raw-resume-20261019-r111-rev1.md`,
SHA-256 `71501d99556c25faac8d42afe82e195e583b4146f913e17b97740cada3459318`.
Luna records this complete receipt. Rev1 remains frozen as failed contract
evidence; this review confers no implementation authority.
