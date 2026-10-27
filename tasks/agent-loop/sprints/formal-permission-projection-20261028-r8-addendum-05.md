# Sprint FORMAL-PERMISSION-PROJECTION-20261028/r8 amendment 05

This is the final bounded attempt at the unchanged outer-H1 objective after the
contract-incomplete r8-r5 stop. It admits no new source owner and preserves
every previous frozen artifact and open gate.

## Stop provenance and mandatory authentication boundary

The prior contract-incomplete receipt is
`tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8-r5.md`,
SHA-256 `f3ad25273afd2626a4c7821651e534cd096ad78e5e3412dfbdfa04be6426c381`.
It supplies no H1 evidence. It records that two source excerpts were read
before authentication because `python` was unavailable; a later `python3`
check matched the pins. Preserve this process deviation and do not reuse its
source excerpts as evidence.

Before this amendment was admitted, Luna ran a standalone `python3` SHA-256
preflight over the 30-file effective manifest below; all 30 matched. The new
worker must repeat this manifest in a **standalone successful `python3` tool
call**, with all files checked and an explicit successful exit, before issuing
any source-body read. Do not combine authentication and excerpts in a shell
command that could continue after authentication failure. If the runtime does
not expose a separate successful authentication result, stop without reading
source bodies. Record each match and the execution order in the handoff.

## Effective pinned manifest

| Input | SHA-256 |
|---|---|
| `tasks/agent-loop/sprints/formal-permission-projection-20261028-r8.md` | `99835a8d22b3b61c90500706245fd5e28aeee238905cca1eb217d8c2f274cd46` |
| `tasks/agent-loop/sprints/formal-permission-projection-20261028-r8-addendum-01.md` | `3c2782ff6e375b4f22278ead3d7f5834b4d2d291f83ab6b9b7b68624c2b040d1` |
| `tasks/agent-loop/sprints/formal-permission-projection-20261028-r8-addendum-02.md` | `c50bb1d2f500f6604eab456de1ea8c157415ed608518c5ff3be54e675aa3f7fc` |
| `tasks/agent-loop/sprints/formal-permission-projection-20261028-r8-addendum-03.md` | `d8c9ef2120ee2f25396c4dbb54b26370a116f917848dbe316cff06533ab5c03a` |
| `tasks/agent-loop/sprints/formal-permission-projection-20261028-r8-addendum-04.md` | `c56f4a6eb8dcb68cf50309789640b4749943e12fbd11f47a1bbea2969c57c605` |
| `tasks/agent-loop/history/formal-permission-projection-20261028-r8-addendum-03-outcome.md` | `76657cf7e8bfa7fd6e5af8beb8337063f82826ea51e4bb0222b7e3cb5434271e` |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8-r5.md` | `f3ad25273afd2626a4c7821651e534cd096ad78e5e3412dfbdfa04be6426c381` |
| `tasks/agent-loop/sprints/formal-permission-projection-20261028-r7.md` | `40035df185bb2266f395264a137babf9b433e875922ff86f453836fba278a767` |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r7.md` | `98cf92059d11ea1efd875c7af9d84c86be236f9c52b7b07acadfcac082c8b79d` |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-review-r7.md` | `635e94a1eec04348fdd87b7c1802101bca10a6fa8631e3e82d0eb39f26a12c7c` |
| `tasks/agent-loop/history/formal-permission-projection-20261028-r7-outcome.md` | `7fab9c3f7bbe4c6072702b30973e44c705122aa244877addd1ff4d2a9a65eef8` |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8.md` | `e9926aaf56c8ea35b1227b7c27693f7c14eb872a46b8b6826ca6cda46951a4c8` |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8-r2.md` | `19bffa5c2fdfdd38d8205dc1368b61b475811acaf2d00073cccbda0f6fecb8c9` |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-review-r8-r2.md` | `6ff6c8e8a9c343c93aaf673903b69acce4633f0df52a035844b1af6f9870f99a` |
| `tasks/agent-loop/history/formal-permission-projection-20261028-r8-outcome.md` | `c69858fa3119d304d5990b8f520855becfe9e81d5f4ab6feba21c119727ade54` |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8-r3.md` | `aafd543e2dc727d8999342ff0d76b8419730befd48cbf9a2d8cd6116a0771148` |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-review-r8-r3.md` | `19aabd5cee2cd4c92f1bdc7559b60c66022a20403792d70da97a9931538e86f6` |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8-r4.md` | `3171fdaec7fe72fa02fd467785a3b4506af0e2c54fbfea34e4e3c7a503d71b94` |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-review-r8-r4.md` | `893203e14c57d2a6467f1ee0c085a2a772db07df463e6418cedcd74953c8d45f` |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `tools/inference-playground/src/scheme.rs` | `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |

## Fixed outer-H1 outcome

Start at `lib.rs:16669` (`record_incoming_bound_capacity_growth`) and trace only
the remaining reservation/accounting/resource composition in this admitted
owner union. Reuse the reviewed context-core frame at
`tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8-r4.md`;
do not re-audit it.

Establish or precisely delimit whether every reachable successful merge
interval preserves, until the final link: (a) both whole parent vectors and
their identities/lifetimes; (b) selected roots as distinct in-range
self-roots; and (c) active intrusion Undo identity and its forest-inverse
sequence, except for the prospective `(copy,from)` entry. Distinguish writes
to accounting fields from writes to `Undo::forests`. Cover successful returns
and error propagation without requiring general abnormal-path restoration.
Use concrete fields and callees. A signature, direct-write scan or receiver
borrow is not a transitive effect summary.

Success is accepted conditional source evidence for complete H1 composed with
the reviewed context frame and corrected H0/H1/H2 implication. Otherwise name
the first exact unsupported callee/effect equation and leave full H1 OPEN. A
reachable outer operation mutating either forest, its lifetime or relevant
checkpoint association falsifies H1. Successful wrong-image export remains a
separate stronger permission counterexample.

Keep H0/H2, B, D, reachable forest/lifetime, r1 Lean, original parent A/B,
source/native, full inference/executor and production gates OPEN unless their
separate obligations are independently established. No source owner, compiler
edit, semantic change or theorem/production authority is added. This is the
last automatic source packet; no renewal follows.

## Output, review and resources

- Sole output: `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8-r6.md`.
- One read-only researcher, one CPU, 1 GiB RSS; no descendants/Astra, tests,
  builds, probes, Cargo, Lean/Lake, compiler edits, Git, network or quarantined
  paths.
- Source cap 120 seconds. Stop on authentication failure, another owner,
  unsupported equation, reachable falsifier or cap; freeze within the grant and
  record any observed overrun. Do not use source evidence from the contract-
  incomplete r8-r5 attempt.
- Fresh non-author review only if the handoff makes a substantive coherent H1
  claim; at most 90 seconds, read-only. Do not spend review time certifying a
  process-stop receipt.
- Reserve 300 seconds: source 120, review 90, primary 60, dispatcher 30.
  Starting from 6,725 / 7,200, the total becomes **7,025 / 7,200**, leaving
  **175 seconds**. Preserve full prior charges including the r8-r4 45-second
  overrun and unused r8-r5 review reserve. No further automatic packet follows.
