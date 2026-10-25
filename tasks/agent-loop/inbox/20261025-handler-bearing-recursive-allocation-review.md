# Independent allocation and composition review

Verdict: PARTIAL; no mathematical defect found in Lane B or the revised quantified joint results. NOT CLEAN for completion of COMBINED-RECURSIVE-INTERACTION-THEORY-20261025/r1: its mandatory joined concrete trace is absent. Neither the sprint nor the full paper/native/original A/B goal is closed.

Reviewer: `/root/allocation_join_review_astra_r1`, nonauthor of the reviewed sources. Requested model/effort: gpt-6-astra/medium; observed runtime model/effort: UNKNOWN. Sole write lease: this report. No source edits, Lean/build/tests, Git operations, descendants, background processes, or other file writes. Review used read-only source and hash inspection and existing primary verification receipts. The yulang-proofs skill informed the distinction between local theorem validity and parent closure; no delegation was made by this child.

## Frozen snapshot

| Artifact | SHA-256 |
| --- | --- |
| HandlerGraphRecAllocation.lean | `5563163a5fe2741dc4cb1968329e5ec417a170099448978b653dc487cd136dfd` |
| HandlerGraphRecInteraction.lean | `13e1350e19036ec7e6dbceb272ff3278a0ef1c9422416e6c6c773268a4309153` |
| Primary composition note | `cd025bb0046618e1f0016148a32c4e16445689952c56e4c548cc478ab1814be0` |
| HandlerGraphTransport.lean | `a869e61005910dba00cf9cfa57065a45afeac08413974e343d9bcc16821f629d` |
| HandlerGraphInteraction.lean | `a5094f70dc2ec2843a431cfb24f0111166fbc9172b7e6df08d0d8c800a8ce018` |
| Sprint contract | `16364e08bf9352ecf3d81ff20f672b5c1b0c1a15026511c63253f4111b2b8687` |
| Verification JSONL at review | `b1d99d67e332eebae2963d456547fd41d2db021d23bd0022183b7798a4684a0a` |

The parent explicitly confirmed the current note hash after its dispatch message initially supplied the older note hash. Review paused during primary source repair and resumed on the new frozen source above. No review of the superseded contents-response theorem is transferred silently.

## Mathematical findings

1. Six-sort closure is structurally complete over the actual accepted HandlerGraph grammar. `closeNames*` maps references/recursive names without changing local indices; `inject*` eliminates the Empty recursive sort; `split*` uses the existing lifted simultaneous local substitution. `sourceContext` puts exactly n recursive slots before the outer environment. `sourceClose*` closes those slots to fresh references and substitutes separately old-typed captures. This derives fresh-node and body typing from source RHS derivations, rather than assuming fresh node typing.

2. Binder ordering agrees with the owning syntax and typing definitions. Operation arms bind payload at 0 and original K at 1 and lift twice. Request K and waitOperation K lift once; wait attempts retain their outer context. Lambda body and its separate adapter consumer receive the appropriate separate lifts; adapter input, value arms, bind and union branches lift once. The explicit original-K example retains the expected indices after an outer capture bind and response bind. The continuation mapping equations distinguish shallow K from forwarded HK.

3. Allocation is immutable and simultaneous. Old references map via inl, fresh names via inr, and old node syntax is exactly mapped, with old types preserved. Shared captures remain the same mapped reference. Old nodes cannot gain fresh transparent edges. `sourceFresh_typed` derives every allocated RHS type from its own source derivation and `CapturesTyped`, and `source_rec_allocation` uses the same closure for the actual source body. Quantification includes arbitrary R and finite n, including zero.

4. The guard criterion applies to the actual closed RHS projection. `project_allocation` connects it to the accepted constructive finite guard result; `freshGraph` considers precisely fresh-to-fresh transparent edges. Fresh-to-old edges cannot return into the fresh set, and use the independently supplied old guard. No fresh rank is assumed. The iff proves necessity as well as sufficiency. Lambda/delay and true introductions stop the frontier; evidence/view/wrap traverse it. Direct, top-wrapped and callable-wrapped self aliases are rejected. This establishes observation progress, not termination of recursive computation.

5. The quantified join is an actual application. `mapOld_agrees` establishes the node equation needed by `sourceEmbedding`; `run_source_extension` uses B's actual source allocation in A's Run.extension, preserving the entire mapped arena. Saved typing is extracted from the actual initial-run invariant rather than imposed on the saved entry. The revised `run_source_answer_old` answers with `.ref (.inr slot)`, not the RHS contents. Its reference typing follows from `joinTy` and `responseType`; the allocated graph's well-typedness is independently derived from source RHSs through the extension. Full operation matching is supplied by `.matched ... saved.operation rfl`. Final prefix safety uses the actual constructed guard. The unused local `allocatedTyped` is redundant proof text, not a missing premise: `extended` already carries the same graph-typing supplier.

## Required remaining work

The contract explicitly requires one actual run from an empty arena that publishes the original root request, receives a fresh recursive handler-bearing callback, executes to and publishes a later root request, performs a second source allocation, and reuses the original saved entry. No such joined concrete theorem exists in the reviewed module. B's attempt trace and A's separate interaction example do not supply that composition. A general implication quantified over Prefix does not witness that specific nontrivial trace. This is a completion-blocking omission, accurately admitted in the note, not a counterexample to the local theorems.

The next packet must construct that exact run and all endpoint/binder equations using the actual sourceFresh/allocate construction, preserve the original arena member through both extensions, and apply the quantified safety theorem to the resulting trace. Any changed source needs primary kernel receipts and fresh independent review. Full-paper omitted forms and native correspondence remain separately OPEN; no production promotion follows.

Minor wording advisory: the final composition-note sentence says CLEAN review of the partial packet “is not a prerequisite for claiming” the original theorem complete. That can read as waiving independent review. It should say CLEAN review of the local results would not suffice to close the original theorem. The immediately surrounding OPEN statements and exact contract prevent interpreting this as authority to close anything.

## Existing verification evidence

Primary receipt call24 records exit0, no warning, for the revised joint source hash above. Its only mismatch against current inputs is the subsequently edited composition note. Call25 records exit0/no warning for the explicit declaration query, with all164 recorded input hashes matching current files at review, including all four new source modules and the current note. Inspected query output includes the revised fresh-reference theorem and reports only propext/Quot.sound for its closure. No independent Lean execution was performed by this reviewer. Source inspection found no sorry, new axiom, Classical, native_decide, unsafe, or admit in the two reviewed modules. These are receipt/hash observations, distinct from mathematical review and from a fresh full checker run.

## Runtime and STOP

Conservative accounting start: 2026-10-25T08:26:00+00:00 (earlier than the first sampled clock at08:26:56; includes initial reads). Budget600 seconds, no reset on the repair pause. All tools launched by this reviewer completed; no live process or descendant remains. STOP is the final report write timestamp below; no further mutation is authorized by this report.

STOP_UTC: 2026-10-25T08:29:27.714448+00:00
Conservatively charged seconds: 207.714448 / 600.

## Authorized prose-only delta review

Primary requested inspection only of the final review-boundary paragraph. Current composition-note SHA-256 is `47d61f569f9f350f23a763d3fcdcd4244f82ebacbf3a8117a5cbc08ca9d06c22`. The corrected sentence says CLEAN review of this partial packet would be insufficient to claim the original parent theorem complete, which remains OPEN. This resolves the wording advisory and no longer suggests a review bypass. Source remains at the previously reviewed hash by primary declaration; no source reinspection or tests were performed for this prose-only delta. PARTIAL verdict and mandatory joined-trace omission are unchanged. Previous receipt correspondence applies to its recorded snapshot, not this later note hash.

Final STOP_UTC: 2026-10-25T08:29:45.007759+00:00
Conservative cumulative elapsed charge from08:26:00UTC: 225.007759 / 600 seconds. No live process or descendant.
