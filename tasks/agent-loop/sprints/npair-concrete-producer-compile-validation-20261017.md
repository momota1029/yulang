# Sprint: compile validation of the approved concrete NPAIR producer

ID: `npair-concrete-producer-compile-validation-20261017`.
Status: READY after Luna revalidated the applied producer and workspace build pins.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN.
Primary and sole Git integrator: Luna/high.
Baseline: `f2f95913cdcff78c4482b3556830483614c06e87`.

## Fixed outcome

Perform exactly one compile-only verification of the already approved and
integrated concrete Permission producer, including test-target compilation:

```sh
timeout 120s env CARGO_BUILD_JOBS=1 cargo check -p yu-solver --features shadow-apply-candidate --tests
```

A successful result establishes only that these targets compile at the frozen
baseline. It runs no tests and establishes no runtime behavior, resource-boundary
behavior, source admission, `At`, transport, receive consumption or parent
closure. A failure is recorded exactly; no retry or repair is authorized.

The original proof lane is WAITING for an independently justified Operation/
Call contribution clause at its actual declaration/reference supplying both
`eta_op` (same complete `w` at the exact source port and predecessor context)
and `realization_op` (correspondence to the native Operation instance, emission
and admission). This compile sprint does not grant a proof/source lease and does
not repeat the source census.

## Revalidated pins

| Input | SHA-256 |
|---|---|
| Approved design `notes/design/2026-10-17-npair-native-port-code-contract.md` | `a6b6f37218408b334922c19ff6065bd8bd607294201ec2b371f1376e800c41ce` |
| Approval receipt `notes/progress/2026-10-17-npair-concrete-producer-approval.md` | `cd81ea1385b1304da283ef8ee15cdd626b98d1759cf79aa372f672e53c5bab67` |
| Applied `crates/yu-solver/src/candidate_effect.rs` | `11a1477ff2c35c03dccb70bdc6121d89d3ced9fadb1921cb8cf8cd5c093b07fb` |
| Applied implementation handoff `tasks/agent-loop/inbox/20261017-npair-concrete-producer-implementation.md` | `f24ba90278a70edbf4a601818755b7c43ee67ec34aa67bf0456ebbf359287cb5` |
| Accounting-repair contract | `755aed57c162f46f2d3688bc07ef8ce078fb63da868c697e9b646de9ec4bfb21` |
| Corrected accounting source receipt | `ef9cd5e8e16cfcc6fc300cf43523ff18170311f34745798c810c8e5fbe23ef47` |
| Corrected accounting handoff | `5cc00163e67e3129b4fc57d59c89575644ea6c6258be39ec0f5988f7dc90a68f` |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `crates/yu-solver/src/candidate_context.rs` | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| `crates/yu-solver/src/lib.rs` | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |
| root `Cargo.toml` | `d61446115ce45d7010898090bce323fe1134b1cca53471ac9416e441d45865d9` |
| `Cargo.lock` | `2055b82e7c2c68df727940d7053da0490368a99217bd3587866a7003177484e6` |
| `crates/yu-solver/Cargo.toml` | `7a599e95800c67ca4688b0f91917609345a252aae6d2ea6cd0f413eb1c07893c` |

The `f1b…` source hash in the repair record is the preserved failed pre-repair
snapshot. The corrected integrated source is `11a…`, matching the commit at the
revalidated baseline. The only dirty tracked path is the unrelated quarantined
`tasks/agent-loop/sprints/authentic-source-and-forward-handler-20261017.json`;
it is not a Cargo build input and remains untouched.

## Lanes, permissions and stop

- Proof: WAIT, no writer/lease until Luna receives the exact missing constructor
  contribution clause and independently validates its authority.
- Implementation validation: Luna/high, one primary invocation only; no source
  edits, auto-fix, retry, tests execution, example/probe or semantic change.
- Exact primary outputs: `notes/progress/2026-10-17-npair-concrete-producer-compile-validation.md`
  and `tasks/agent-loop/inbox/20261017-npair-concrete-producer-compile-validation.md`.
- Generated build output: workspace Cargo `target/`; raw combined command output:
  `/tmp/yulang-npair-concrete-producer-check-20261017.log`.
- Heavy build cap 120s, one process, `CARGO_BUILD_JOBS=1`; no concurrent build.
  One fresh independent compiler-referee receipt review, maximum 90s.
- Fresh envelope 300s: command 120s, review 90s, coordination 30s, reserve
  60s. Unused time is retired. Observed runtime/model data remain UNKNOWN unless
  directly measured.

Review freezes the receipt and input hashes, checks that the exact command ran
once and that no test target executed, and rejects any inference beyond
compilation. The next material consultation is a compile failure, arrival of the
exact original constructor input, or a separately qualified approved path.
