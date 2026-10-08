# Question: owner of the authentic initial JointWF context

Question ID: `l4-initial-jointwf-owner`
Question revision: `q1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): current source branch HEAD `1d593506b94a73a26f3d050f9302dd220464a98f`; bounded production-entrypoint audit baseline `d86ae2dd30c85f6828742ec5be9d959ab8dbc94e`; selected source proof `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` SHA-256 `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`; frozen L4 trace `notes/progress/2026-10-08-l4-id-anchor-source-constructor-trace.md` SHA-256 `f9b6d30855f26d9e87cd9f64aa23c46957c74ff042c2a9d0bbddb48f98a501f5`
Task/thread locator: unavailable; the active objective is supplied in the conversation context, with no exposed stable thread identifier
Governing source/section: `rules/design-authority.md`, “Authority order” and “Approval and implementation gate”; `notes/design/2026-10-08-source-generalize-definition.md` §§2–3; `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §2 L4 and §3

## Requested scoped decision

Choose who owns the genuine initial `JointWF` registry/scope/authority/incidence context required before the selected source constructors form `U_g` and its publication anchor:

1. The compilation caller supplies an authentic context with its complete evidence and dependencies.
2. A Yulang-owned initial-context constructor produces that context under independently specified original-world rules.

An explicitly scoped alternative may name another existing authentic owner and explain its evidence source. This question does not select a concrete Rust type/signature, placement/failure policy, source rule meaning, public export representation, checker architecture, or F5 cutover.

## Background and current premises

The user's active objective is 「型推論部分を完成させ，yulang3ブランチのF5実装と置き換える」. That authorizes continued inference work; it is not approval of either context-owner architecture.

The Authoritative source contract keeps genuine initial-world evidence as L4 (`source-generalize-definition-and-proof.md` §2, lines 92–97). Its §3 fixes an actual initialization event and original environment/world as inputs. The selected native constructors do produce downstream outputs: Lambda formation constructs `U_g`/`IF0`, and the literal rule constructs `J_0`. The selected rules do not construct the initial jointly valid registry/scope/authority/incidence world from either `my id x=x` or `my z=0; my pick y=z`.

The frozen source trace establishes that the Empty environment-telescope case is conditional on the joint world; it does not bootstrap `JointWF`. Current production entrypoints do not supply this context: `yu-hir::SemanticImports` is empty/ignored, `ConstraintBatch::collect` accepts HIR, and `SolvedModule::solve` has no context input. The inspected default core/backend crates have no runtime world supplier. This is bounded evidence, not a repository-wide absence theorem.

## Options and consequences

1. **Caller-owned authentic context.** Require the compilation host to provide the actual initial world and complete JointWF evidence; the compiler validates and retains it through source formation/publication. Consequence: current compile/solve entrypoints need a context seam, and standalone compilation cannot fabricate a default world. A caller's opaque `valid` flag is insufficient; it must carry or reference the actual constructors, registrations, scopes and dependent evidence.

2. **Yulang-owned initial-context constructor.** Define and implement a compiler/runtime-owned constructor for the initial world and registrations using independently fixed original-world rules. Consequence: one-call compilation can own setup, but this adds a new constructor/law boundary that the current language/runtime does not provide. It cannot be implemented as an empty-world tag merely because imports or captures are empty; the constructor must establish the genuine registry, authority, scope, incidence and lifetime premises.

Both choices preserve the selected L4 requirement and selected Lambda/literal meanings. Neither by itself supplies the remaining source/HIR correspondence, Parameter telescope, complete local-law registry, public extraction/decode/Direct integration, principality, resource/failure policy, or F5 replacement. No choice here authorizes compiler implementation; the selected owner contract still needs its own reviewed durable design before implementation.

## Affected work

Blocked scope: assigning the initial-context producer, adding its production API/factory, and freezing SourceBuild metadata that depends on authentic JointWF evidence.

Independent authorized work: current F5 crosswalk, selected source/projection theorem work that treats L4 as an input, open recursive/effect/principality gates, and the separate pending Direct-consumer and Application-owner questions.

Required answer: select option 1 or 2, or name a scoped existing owner with its authentic evidence path. Silence, this question's publication, or the broad inference objective is not approval.

Pending publication: keep this entire question directory unstaged and uncommitted until the questioning primary discovers and validates an explicitly approved local answer and commits the matching question/draft/answer together. The answering primary never mutates Git. Posting does not pause the goal; dependent work waits while independent work continues on disjoint paths.
