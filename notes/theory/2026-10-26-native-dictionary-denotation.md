# Native dictionary DAG denotation and the source binding correspondence

Date: 2026-10-26. Supplied baseline: `37ec9da2aaca2d7b806887d06d9bbd8b0fc5439c`.
Producer: `/root/source_membership_r4`, bounded `lean_prover` leaf.
Status: **checked mathematical construction of the playground runtime's dictionary action; original Function membership remains open**. Independent review is required. This note does not assert that a static dispatch table is the original decorated source dictionary.

## 1. What is constructed

[NativeDictionaryDenotation.lean](lean/YulangClosure/NativeDictionaryDenotation.lean) interprets the actual chronological Word/Substitution arenas in [dispatch.rs](../../tools/inference-playground/src/runtime/dispatch.rs). Its central result is `YulangClosure.NativeDictionaryDenotation.name_checked_dictionary_denotation`.

For arbitrary complete step payloads, raw word/substitution arenas, raw initializer defaults, value and caller substitutions, current and future input contexts, a member site, a fixed dictionary and one fixed witness parameter, the theorem derives the following equation from the raw constructor inputs:

```text
lookup after checked native Name construction
  = lookup after the explicitly ordered decoded Name action.
```

The decoded action is exactly

```text
value substitution;
optional [initializer cell := raw caller context followed by the Name step];
caller substitution.
```

The same raw default map, complete dictionary, witness parameter and member site occur on both sides. Every finite default-chain unfolding is retained. A missing/default-cycle result or missing dictionary key can still yield `none`. The theorem neither assumes nor concludes successful body execution, final-world validity, semantic Function membership, or a source typing derivation.

The original requested conclusion remains `ValueMem_F†(W,r,e)` for the actual returned identity, with full `PhiW`, `P_F`, phase, descriptor, annotation, history and `SourceT` obligations. Here `C` remains the delayed computation that constructs `W`; no later source Call of `W` is invented. This packet supplies the concrete dictionary action that the earlier [receiving construction](2026-10-26-source-function-membership-construction.md) had left explicit. It does not replace the original membership definition with this action.

## 2. The actual native owners

The relevant implementation is `tools/inference-playground/src/runtime`, not a `crates/yu-eval` module. It is the decorated playground executor. Its dispatch table consumes candidate-selected member information; proving its algebra does not prove solver-native inference soundness.

| Native owner | Determined operation represented here |
| --- | --- |
| `dispatch.rs`, `Word`, `join_words`, `append` | A Step stores its exact payload after the previous word. A Join denotes ordered concatenation. Optional handles use the empty word. Fresh handles are the old arena length. |
| `dispatch.rs`, `Substitution`, `then` | `Then(a,b)` executes `a` before `b`. The native stack pushes `[b,a]` so that popping realizes this order. An absent substitution is the identity. |
| `dispatch.rs::apply_bounded` | Assign acts only when the current base is its exact initializer scope. It replaces the base and prefixes the replacement word to the current word. A nonmatching assignment does nothing. |
| `dispatch.rs::initializer` | Store the **raw** parent context as the default and inherit the parent's substitution separately. Duplicate insertion updates the map and then reports the native error. |
| `dispatch.rs::name` | Check the default's presence for an instantiated cell; append the Name step to the **raw** caller context; allocate Assign; compose value, Assign and caller in order. |
| `dispatch.rs::word` | First apply the state substitution; while a base remains, fetch its raw default, apply that same substitution to the default, and prefix its word. Flatten Step/Join left to right. |
| `machine.rs::dispatch_name`, near line 2618 | The instantiated-site test is membership in `program.dictionary_names`. Only `ReceivedValue.dispatch` is updated; the actual value handle, interface and receiving view remain the existing packet fields. |
| `machine.rs::substitute_environment`, near line 2606 | Append the incoming substitution after the environment's old substitution. `with_dispatch` creates a parent-linked environment node without a binder. |
| `machine.rs::dispatch_environment`, near line 2612 | Append the exact Operator/Member step to the environment's context. |
| `machine.rs::Instruction::FieldTail`, near line 747 | Resolve the whole dispatch word, look up `(word, exact site)` in the fixed dictionary, and then append the Member step for the selected body's environment. Missing lookup reports `UnsupportedFieldTail`. |
| `program.rs`, near lines 392–415 and 1242–1253 | Form keys from candidate instantiation steps, preserving every owner and occurrence; map Definition/Local to Name and retain Operator/Member kinds. Conflicting selected member identities at the same key are rejected. The dictionary maps the key to the corresponding registered member-body label. |

The `Step` parameter in Lean is arbitrary. It stands for the **whole** native `(Kind, SourceRootId, HirOccurrenceId)` payload. There is no quotient by kind, word length, displayed identifier, receiver type or source spelling. Source scope identities are represented by exact natural-number indices; this is the mathematical embedding of successful finite native allocations, not a license to wrap or identify native machine indices.

Group and Ascription lower to `Instruction::Forward` in the particular bounded `LocalSource` constructor at `program.rs` near line 815. `Forward` evaluates the child under the same environment at `machine.rs` near line 775. That constructor explicitly relies on the absence of applicable registered effect-upcast adapters in its envelope. This packet does not turn that bounded implementation fact into a general erasure theorem for the original annotation language.

## 3. Interpretation and constructive proof

### 3.1 Word and substitution arenas

`WordArena` and `SubArena` are chronological append arenas. The interpretation of a node uses only its preceding arena for backward children. Thus a self-reference or forward reference cannot acquire a meaning by circular unfolding. `wordAt_bound` and `subAt_bound` prove that every successfully interpreted handle is below the arena size.

Word denotation is a list of whole steps. A context is its optional initializer base together with that whole list. The checked append and join equations are

```text
append(s,w,item) = (s,w ++ [item])
join(w1,w2)      = w1 ++ w2.
```

An assignment `(cell,replacement)` has the exact native action

```text
if input.base = Some(cell)
then (replacement.base, replacement.word ++ input.word)
else input.
```

`action` folds assignments from left to right. `then_denotes` derives concatenation of the decoded assignment lists from the actual arena construction; `then_action` derives the corresponding ordered function composition. Neither commutativity nor idempotence is assumed.

Old handles keep their meanings when a new Word or Substitution node is appended. `subAt_word_transport` also proves that extending the word arena preserves every already meaningful substitution, including all its stored replacement contexts. The preservation statement concerns successful old meanings: an invalid future handle is not asserted to stay invalid after the arena grows.

### 3.2 Raw application, not an assumed action law

`assignRaw` performs the real matching-base join in a raw context. `assignRaw_denotes` proves its decoded assignment equation, and `assignRaw_keeps_old` retains every old word meaning.

`applyDag` applies the actual raw substitution DAG by backward-child recursion in the same first-then-second order as the native pending stack. `applyDag_denotes` constructs **one resulting arena/context pair** and proves all of the following together:

1. the raw mathematical application returns that pair;
2. its decoded context is the ordered action of the decoded substitution;
3. every existing word handle keeps its whole meaning in that same resulting arena.

The proof is induction on the actual chronological substitution arena. In the Then case, the first result's arena preservation transports the second child's stored replacement contexts before the second induction application. There is no separately chosen output world for the two branches and no assumption that a desired final result already exists.

### 3.3 Name, raw defaults and the dictionary equation

`name` follows the native allocation-success branch exactly. `nameChecked` additionally exposes the actual default-presence guard. `name_denotes` constructs the decoded result by transporting the old value/caller substitutions through the new Word node and Assign node, then applying the two real Then operations. `name_checked_denotes` derives that result through the guard; its `ready` premise is precisely “an instantiated cell has a default”, not a typing or body-success premise.

`initializer` retains the raw parent context and its separate inherited substitution. `initialize_fresh` checks the fresh-cell result. `DefaultsValid` means only that every stored raw default has an actual word denotation; it contains no descriptor, safety or source-typing predicate. The empty map satisfies it, and `initializer_defaults_valid` derives it after an actual insertion from the parent context's denotation. `name_defaults_unchanged` proves that the entire old raw default map has the same pointwise meaning after Name's word allocation.

`resolve` interprets any finite default-chain unfolding. At a nonempty base it applies the same decoded substitution to the default, then prefixes its word to the existing suffix. `dispatchMeaning` combines the initial substitution action and this resolution. `name_raw_dictionary_denotation` transports the exact raw defaults through Name and obtains the lookup equation for every fixed dictionary and witness. `name_checked_dictionary_denotation` combines that equation with the native entry guard in one theorem.

The arbitrary `World`/`witness` parameter permits a later typed interpretation to carry the whole correlated source tuple without projecting it. Its occurrence is the identical parameter on both sides. This universal algebraic fact does **not** itself construct the original `nu,K,D` telescope or prove that the native labels realize its source certificates.

### 3.4 A native distinction that the interpretation must retain

The native regression sequence `[1 := empty; 0 := 1]` sends base `0` to base `1` on one application and to `empty` on two applications. `caller_action_not_idempotent` proves those two exact results. `name_applies_caller_once` derives the actual instantiated Name result with its appended step. Consequently, preapplying the caller substitution to the replacement and applying it again at the final Then is not a valid simplification of this implementation.

`cyclic_default_fails` proves failure for every finite unfolding budget on the explicit self-cycle. This is a failure of that default chain, not a source-qualified counterexample to original Function membership.

## 4. Runtime resource and correspondence limits

`dispatch.rs` charges a shared native counter for substitution traversal, default unfolding and word flattening and rejects work above `32_768`. Allocation can also fail. The raw algebra above describes the mathematical allocation-success branches. It does **not** prove that every denotable DAG fits that runtime work budget or available memory. `resolve` fuel counts default unfoldings; it is not relabeled as the native combined counter. Compact sharing can still yield a word whose expansion exceeds the native limit.

The implementation-to-definition correspondence is a source-level, constructor-by-constructor inspection recorded in §2. Lean checks the mathematical functions and theorems; it does not execute or verify the Rust binary. In particular, no theorem here equates all error-path mutation states, proves the native iterative implementation's resource accounting, or rules out runtime unavailability from a merely algebraically meaningful input.

Decoding a substitution requires the stored replacement words to have meanings. An arbitrary malformed unused replacement may be skipped by native `apply_bounded` without being read. The theorem does not claim equivalence on that malformed state. Its structural premises are explicit, and its valid constructors establish the relevant meanings. This does not remove any source constructor or shrink the original independently admitted context domain.

No Rust tests or source-generation files were changed or used as live proof dependencies. No default root import was edited. The accepted receiving artifact remains byte-frozen.

## 5. Applying the result to the original binding obligation

The original source requirements are more than equality of dispatch keys.

* [Call semantic input realization](2026-10-08-call-semantic-input-realization.md) §2 fixes one original `xi=(nu,K,D)`, scope tree and assignment `eta0`; the live event supplies the actual current configuration and joint witness. §4.1 gives each immutable binding its retained provider/root and hereditary certificate. §4.2 reads that **same binding projection** and keeps the current world and witness.
* [Source Generalize](../design/2026-10-08-source-generalize-definition.md) §2 retains the actual binding object, shared initializer evidence and full dependencies. Its selected [construction](2026-10-08-source-generalize-definition-and-proof.md) §3.3 says that `Specialize(q,mechanism,sigma,Delta)` exists only when the actual source dictionary/template rule supplies it. The same section fixes an installed monomorphic dictionary/contract as `Established`/`OneShot`; §6 requires a delayed method choice to use its actual retained specialization mechanism.
* The [dot-selection manuscript](../../docs/yulang-dot-selection-safety-ja.tex), sections “scheme を一つの packet として具体化する”, “dictionary の具体的表現”, and “role の有限証拠”, supplies a concrete **typed** dictionary construction. `Dict_R` is a nominal record with exact member schemes; one capture-avoiding instance applies to the whole Function/graph/binder/capture packet; shared captures remain the same values. Hyp/Impl/Assoc form a finite evidence DAG with one shared instance and all original obligations. The M/R/F construction obtains an actual member instance or projects its typed dictionary field and retains direct argument/result adapters. The manuscript expressly distinguishes this finite-evidence construction from proving that every compiler-selected result supplies such evidence; its opening also retains the corrected-machine/source correspondence limits.

The playground's `HashMap<(Vec<Step>, Site), Label>` and that typed `Dict_R` record are different representations. Calling both “dictionary” does not identify them. The native program builder retains exact path/site/member-label association, but the inspected construction does not define a projection from each such table entry to the **entire original** whole-packet instance, captured evidence values, adapters, descriptor interpretation, current-event restriction and field telescope.

The next concrete application must construct the following map from the original source derivation and its actual selected-use evidence:

```text
(original shared nu,K,D, eta0, current event,
 source binding/reference and actual specialization event,
 full member/role evidence packet)
    ↦
(exact native instantiation word/site key, registered body label,
 its actual captures and argument/result adaptation plan).
```

Its equations must show that the native Name-site test represents the actual source instantiation or monomorphic alias; that one whole instance is used across all ports, fields and captures; and that the selected body's source certificate restricts to the same current event. This is a finite source-to-runtime construction obligation at the selected-use/body-template owners. It is not supplied by an equality of labels or by assuming a completed body is safe.

Once that map is constructed, the checked theorem removes the runtime-DAG algebra from the application: it gives the identical mapped dictionary observation after the actual ordered Name action, at the same supplied source tuple. The raw default map and current caller substitution cannot be erased or normalized by idempotence along the way.

No contradiction in the original source definitions was found. The result is therefore **not** an original source counterexample and does not justify changing any accepted semantics. It also does not discharge the remaining full descriptor/context embedding, all `PhiW` fields, the original `P_F` phase envelope, annotation realization, `ValueMem_F†`, or `SourceT`. Arbitrary pre-Return carrier interactions, divergence, pending continuations and future demands retain their original obligations and quantifiers. No success hypothesis on those computations is introduced here.

## 6. Check and review receipt

The assigned isolated project is `/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project`; its toolchain, Lake file and empty dependency manifest are copied unchanged from the pinned project. The exact command, source snapshots, failed attempts, complete theorem inventory, all printed types, transitive axiom results, resource receipts and input/output hashes are preserved in the [handoff](../../tasks/agent-loop/inbox/20261026-native-dictionary-denotation-r4.md) and task-owned scratch tree.

The final helper accepts **37 authored theorem roots**; the originating-module census checks **131 theorem constants**, including every private/generated theorem present in that imported module. The complete census reports 90 with no axioms, 24 using only `propext`, and 17 using `propext` and `Quot.sound`; none uses `Classical.choice`. Eleven of twelve authorized focused checker calls were used, including four preserved repair failures and two originating censuses. The final module build/root audit and final census both exit zero.

The module has no project axioms, proof holes, native-evaluation axiom, or checker bypass. It imports only `Init`. Standard axiom dependencies are reported individually in the complete originating-module audit, including private/generated declarations; a clean build is not represented as independent review or original source closure. The primary owns fresh independent review, continuation, Git integration and pushes.
