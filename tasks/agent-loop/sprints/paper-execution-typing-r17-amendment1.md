# R17.1 amendment — invocation accounting and continuation procedure

This primary amendment revises only the R17 invocation accounting/procedure. It preserves R17's objective, six judgments, value-only forall rule, shared-context freshness, dependencies, exact source lease, total budgets, and admission time. It does not retroactively authorize the version queries below. Original R17 contract SHA-256: `510823d707f36c8cc33601d7d1ab78e2732015010ca705f74e1ed48c28fa69b3`.

## Frozen incident and charged invocations

The worker's first construction shell ran two version queries that R17 had disallowed. Count every literal Lean/Lake process, even when several are launched in one shell. The queries are incident evidence only and are not construction proof. The exact retained receipt is:

Working directory for every invocation: `/tmp/yulang-r17-forall/notes/theory/lean`. Native binary: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.

1. `[lake, '--version']`, exit 0, 0.415s: `Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)`.
2. `[lake, 'env', 'lean', '--version']`, exit 0, 0.083s: `Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`.
3. `[lake, 'build', '+YulangClosure.PaperExecutionSyntax', '+YulangClosure.PaperExecutionBinderLaws', '+YulangClosure.PaperExecutionTypingSubstitution']`, exit 1, 24.568s; the new typing theorem was missing the final σ application.
4. `[lake, 'build', '+YulangClosure.PaperExecutionTypingSubstitution']`, exit 1, 3.006s; continuation implicit inference/example layout failed.
5. Same focused typing build, exit 0, 0.737s. This establishes only that current candidate modules build; exact theorem types and axiom audits remain pending.

The worker confirmed no command, process, descendant, scratch/source/handoff write occurred after the primary pause; exact cessation and artifact hashes must be recorded before resumption. Preserve all five charges. The original R17 maximum remains 12 serial Lean/Lake invocations, including failed builds, audits and cleanup. Construction invocations 6–10 remain (5); primary final build/audit invocations 11–12 remain reserved. No invocation can transfer from R16. The original 1800 active-second cap, checker-second cap and R17 admission origin are unchanged.

Primary verified the stopped snapshot without invoking Lean/Lake: `PaperExecutionSyntax.lean` SHA-256 `8f4a32fd1c013ae78a161dadd52bed57cc7c99af5ae30fd30ba133de2c3f74a4`; `PaperExecutionTypingSubstitution.lean` SHA-256 `b2975d38fccbf5c908741c3714b2b513b4b8706d80f3c009125c815d1b944d89`; handoff SHA-256 `635969c5c863335dc8ccc8c7b39da81b947c30b7e5c1b98ea84d53ed77ae3686`. `.lake/R17Audit.lean` does not exist yet. Original read-only dependencies retain the frozen R17 hashes.

## One continuation envelope

After a confirmed STOPPED receipt, this amendment admits one followup to the same proof owner only. It may continue the already leased R17 source files, create/use its already leased `.lake/R17Audit.lean`, and finish the handoff. First command after resumption is invocation 6 and must be checked against the shared ledger. Count each literal Lean/Lake process separately, including any command hidden in a shell wrapper. Do not rerun either version query. Keep invocations serial and use `-j1 -M1024`.

All R17 claim/authority/source/proof requirements, exact paths, stop conditions, and OPEN parent gates remain exactly as in the original contract. No new worker/reviewer, source path, dependency, assumption, semantic change, budget or time is granted. Full diagnostics from invocations 1–5 and the stopped source/scratch hashes belong in the existing assigned handoff before further construction.
