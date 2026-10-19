# Sprint Yulang2 demo ordinary islands — R132 rev2

Status: **REPAIR AUTHORIZED; candidate blocked pending delta review**.
Branch: `research/simple-sub-intrusion`; implementation baseline remains
`9fab033a27390ac12f7553a9d6af11a82ad66e1b`.
Parent contract: `tasks/agent-loop/sprints/yulang2-demo-ordinary-islands-20261020-r132-rev1.md`, SHA-256
`5335bbb4e6d0bdcd1f0e46e947990d1e61cdde1e23e53045abbe8e0760e5efe6`.

## Adjudicated rev1 finding

The independent compiler/source and regression reviews both found the same
BLOCKING browser transition bug: the initial Run definition is
`int_identity`, but changing examples updates only the source. Selecting any
previous example then asks the selected-definition API for a missing
`int_identity` instead of that example's `main`. The old example options and
smoke source/oracles are otherwise present. Keep both rev1 BLOCKING receipts
as permanent history; do not treat the candidate as CLEAN.

## Exact repair and unchanged authority

Only `web/playground/src/main.ts` is reopened for the repair. On example
selection, update both the source and selected definition: use `int_identity`
for `yulang2_ordinary_islands`, and `main` for every previous example and the
existing fallback. Keep the field editable after selection. Do not change the
fixture, outputs, WASM/API, language semantics or any proof/production gate.

The minimal fix is equivalent to:

```ts
source.value = examples[selected] ?? examples.ordinary;
definition.value = selected === "yulang2_ordinary_islands" ? "int_identity" : "main";
```

Success requires both the initial new-example selection and transitions to
each existing option to retain a valid default, then switching back to the new
fixture. The two fresh rev2 reviewers must inspect that path and confirm the
editable field remains respected. Existing selected-definition behavior stays
unchanged for all old examples. No expected-value change or new source fragment
is authorized.

## Leases and gate order

Repair author: prior implementation worker `/root/r132_web_impl`, exact write
lease only `web/playground/src/main.ts` and a new revision-2 implementation
handoff at `tasks/agent-loop/inbox/20261020-r132-implementation.md`.
Maximum repair allocation: 60 seconds. No test, build, formatter, compiler,
CLI or Git command during repair.

After STOP, freeze and hash both outputs and the unchanged direct dependencies.
Return the delta to the same independent compiler/source and regression
reviewers, maximum 120 seconds combined, using their leased review receipts.
Both must report CLEAN on the revised candidate before the one still-unrun
command from rev1:

```sh
timeout 240s npm --prefix web/playground run check
```

Run once; stop on failure. This check builds the browser/WASM package and runs
the smoke; review of the source transition covers its browser selection path.
No retry or additional command is authorized.

## Resource accounting

Preserve the original implementation's full 360-second reservation because its
elapsed runtime is UNKNOWN. Preserve the original final-review allocation of
240 seconds; do not refund it. Reallocate only unused proof/source budget:

- prior charged: inventory 120, prospective review 120, proof 279, source audit
  184 seconds;
- prior implementation reserved: 360 seconds, unchanged pending reconciliation;
- prior final-review allocation: 240 seconds, retained;
- repair and handoff: 60 seconds;
- rev2 delta reviews: 120 seconds;
- verification: 240 seconds;
- closeout: 60 seconds.

Charged or reserved total: **1,783 seconds**; 17 seconds remain unallocated
within the original 1,800-second envelope. R114's separate unreconciled 360
seconds remain unavailable. No budget reset or transfer is authorized.

All original Simple-sub/evaluator A/B, source/native, adoption and production
gates remain OPEN. This revision repairs an experimental UI regression and
does not claim execution success until the authorized check passes.
