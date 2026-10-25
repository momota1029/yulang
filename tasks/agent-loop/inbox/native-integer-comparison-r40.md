# R40 native integer comparison — construction handoff

Assignment r1; sprint `NATIVE-INTEGER-COMPARISON-ORDER-20261026/r40`, contract
`c67b3f0a916bfc47a3bd01ce2ce7d406595e4011ab8a3248e732a03d8cd4dec9`;
baseline `ddeed3d91df9293827628e29c48d32fd90a9d279`.
Worker `/root/r40_lean_decimal_comparison`; requested/observed model and effort
UNKNOWN; worker session not exposed. No descendants, nested CLI or Git actions.
Only leased paths are this handoff and
`notes/theory/lean/YulangClosure/NativeIntegerComparison.lean`.

## Original claim and authority

The actual manuscript `docs/yulang-operational-type-safety-ja.tex:901–902`
defines the five integer relations as Boolean observations of mathematical
integers; `:923–942` states primitive type preservation. Its opening correction
notice leaves source correspondence open. Corrected-core note CV1 §3/V3 retains
the same integer relation meanings; the corrected-machine simulation is a
candidate observation construction, not a new scalar semantic authority.
The accepted byte readback amendment uses exact UTF8 bytes, not String.toList.
Research draft claims are not treated as production authority.

Direct frozen inputs, SHA-256:

- manuscript: `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`;
- NativeLiteralReadback.lean: `53a745397fed4b319225541b8e764a32cdc72032ca4e8be48d9d4a23d3901c54`;
- decimal.rs: `83ba443036c7da05f9d72d4bbba98b05c4cab2135062743ffe8e3f05250d1cae`;
- machine.rs: `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e`;
- source_annotation.rs: `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f`;
- lean-toolchain: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`;
- lakefile.toml: `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`;
- lake-manifest.json: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.

All source hashes were recomputed and matched the contract; project hashes above record the read-only environment snapshot. Root AGENTS.md/base instructions,
goal-driven sprint rules, selected contract/current state, Lean skill and its
source/execution references, project pin/config/manifest, existing readback
module, prior readback outcome/producer/byte notes and actual source sections
were read before construction.

## Source-to-Lean map and exact scope

Namespace is `YulangClosure.NativeIntegerComparison` throughout.
`parseBytes` reuses NativeLiteral.splitSign and its nonempty Digits test;
`parts` observes exact `String.toUTF8.data.toList`. `trimZeros` removes initial
byte 48; `normalize` turns all-zero words into `(false,[48])`. This represents
Rust decimal.rs:6–11, preserving every grammar spelling rather than assuming
canonical input. `lexCompare` compares unsigned byte values from left to right.
`magnitude` first compares normalized lengths and only then lexicographic order;
`compareParts` implements exactly the four sign arms, swapping right/left
magnitudes for two negatives. `compare` propagates either parser failure.
This represents decimal.rs:14–27 without a machine integer bound.

Independent proof-only `value` is positional base-10 expansion, related by
`fold_expansion` to existing NativeLiteral.decimalFold. Comparison never calls
`value`, mathematicalValue or decodeInteger. `value_bound`, `value_lower`,
`block_lt`, `lex_value`, `shorter_value` and `magnitude_value` establish the
length/ASCII-order argument. `normalize_spec` preserves signed positional value
and ensures every normalized negative has strictly positive magnitude.

`intEq/intLt/intLe/intGt/intGe` exactly map the final Ordering by isEq/isLT/
!isGT/isGT/!isLT, corresponding to machine.rs:2785–2805 and the five exact
PinnedPrimitiveOp identities in source_annotation.rs:82–105.
Source byte/str order correspondence and existing native producer grammar
remain source-read evidence; Lean does not execute Rust.

## Exact declaration inventory

All 23 source signatures follow, under the shown namespace and open declaration.
The signature text is extracted from the frozen source, not represented as
independently printed checker output. Luna owns the matching #check/#print axioms
receipt. `Ord.compare` specialized to Int is Lean's mathematical integer
comparison (the phrase Int.compare in the contract). Every helper assumption is
discharged inside `compare_decode`; its only hypotheses are the two successful
readbacks, with one shared pair a/b retained by all five projections.

```lean
namespace YulangClosure.NativeIntegerComparison
open YulangClosure.NativeLiteral
theorem fold_expansion (ds : List UInt8) (acc : Nat) :
    decimalFold acc ds = acc * 10 ^ ds.length + value ds

theorem fold_zero (ds : List UInt8) : decimalFold 0 ds = value ds

theorem parseBytes_success_iff (bytes : List UInt8) :
    (∃ p, parseBytes bytes = some p) ↔
      (splitSign bytes).2 ≠ [] ∧ Digits (splitSign bytes).2

theorem parts_success_iff (text : String) :
    (∃ p, parts text = some p) ↔ Grammar text

theorem parts_reject_iff (text : String) :
    parts text = none ↔ ¬ Grammar text

theorem trim_spec {ds : List UInt8} (hd : Digits ds) :
    Digits (trimZeros ds) ∧ value (trimZeros ds) = value ds ∧
      (trimZeros ds = [] ∨ ∃ c cs, trimZeros ds = c :: cs ∧ 48 < c.toNat)

theorem normalize_spec (negative : Bool) {ds : List UInt8} (hd : Digits ds) :
    Digits (normalize negative ds).2 ∧ Canonical (normalize negative ds).2 ∧
    signedValue (normalize negative ds).1 (value (normalize negative ds).2) =
      signedValue negative (value ds) ∧
    ((normalize negative ds).1 = true → 0 < value (normalize negative ds).2)

theorem value_bound {ds : List UInt8} (hd : Digits ds) :
    value ds < 10 ^ ds.length

theorem value_lower {c : UInt8} {cs : List UInt8} (hp : 48 < c.toNat) :
    10 ^ cs.length ≤ value (c :: cs)

theorem block_lt {a b p x y : Nat} (hab : a < b) (hx : x < p) :
    a * p + x < b * p + y

theorem compare_add_prefix (pre x y : Nat) :
    Ord.compare (pre + x) (pre + y) = Ord.compare x y

theorem lex_value {left right : List UInt8}
    (hl : Digits left) (hr : Digits right) (hlen : left.length = right.length) :
    lexCompare left right = Ord.compare (value left) (value right)

theorem shorter_value {left right : List UInt8}
    (hl : Digits left) (hr : Digits right)
    (cl : Canonical left) (cr : Canonical right)
    (hlen : left.length < right.length) : value left < value right

theorem magnitude_value {left right : List UInt8}
    (hl : Digits left) (hr : Digits right)
    (cl : Canonical left) (cr : Canonical right) :
    magnitude left right = Ord.compare (value left) (value right)

theorem compareParts_value {left right : Bool × List UInt8}
    (hl : Digits left.2) (hr : Digits right.2)
    (cl : Canonical left.2) (cr : Canonical right.2)
    (nl : left.1 = true → 0 < value left.2)
    (nr : right.1 = true → 0 < value right.2) :
    compareParts left right =
      Ord.compare (signedValue left.1 (value left.2))
        (signedValue right.1 (value right.2))

theorem parts_spec {text : String} {p : Bool × List UInt8}
    (hp : parts text = some p) :
    Grammar text ∧ Digits p.2 ∧ Canonical p.2 ∧
      signedValue p.1 (value p.2) = mathematicalValue text ∧
      (p.1 = true → 0 < value p.2)

theorem compare_decode {left right : String} {a b : Int}
    (ha : decodeInteger left = some a) (hb : decodeInteger right = some b) :
    compare left right = some (Ord.compare a b)

theorem boolean_projections {left right : String} {a b : Int}
    (ha : decodeInteger left = some a) (hb : decodeInteger right = some b) :
    intEq left right = some (decide (a = b)) ∧
    intLt left right = some (decide (a < b)) ∧
    intLe left right = some (decide (a ≤ b)) ∧
    intGt left right = some (decide (a > b)) ∧
    intGe left right = some (decide (a ≥ b))

theorem intEq_decode {left right : String} {a b : Int}
    (ha : decodeInteger left = some a) (hb : decodeInteger right = some b) :
    intEq left right = some (decide (a = b))

theorem intLt_decode {left right : String} {a b : Int}
    (ha : decodeInteger left = some a) (hb : decodeInteger right = some b) :
    intLt left right = some (decide (a < b))

theorem intLe_decode {left right : String} {a b : Int}
    (ha : decodeInteger left = some a) (hb : decodeInteger right = some b) :
    intLe left right = some (decide (a ≤ b))

theorem intGt_decode {left right : String} {a b : Int}
    (ha : decodeInteger left = some a) (hb : decodeInteger right = some b) :
    intGt left right = some (decide (a > b))

theorem intGe_decode {left right : String} {a b : Int}
    (ha : decodeInteger left = some a) (hb : decodeInteger right = some b) :
    intGe left right = some (decide (a ≥ b))
end YulangClosure.NativeIntegerComparison
```

All 22 reduction examples are constructed with `by decide`, covering -0/000,
leading zeroes, differently spelled equal positive/negative magnitudes,
negative order reversal, mixed signs, unequal lengths, equal-length lexicographic
order, 30-digit positive and negative values, empty/minus-only/plus/double-minus/
fullwidth digit words, and invalid left/right operands. Five examples exercise
the concrete Boolean projections. The primary compiled them with r7; final r8
whole-module verification remains with the primary.

## Evidence and remaining obligations

No checker, build, Lean evaluation, Cargo, benchmark or test command was run by
this worker; `.lake` and generated outputs belong solely to Luna. Read-only
`elan which lean` exited 0 and resolved
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`.
Pin is `leanprover/lean4:v4.35.0`, project `-j1 -M1024`, packages empty.
Actual owner-run evidence is preserved in
`tasks/agent-loop/inbox/native-integer-comparison-r40-primary-verification.txt`.
It records Lean 4.35.0 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`,
Lake `5.0.0-src+eb6cafb`, and the actual signatures/complete axiom outputs.
These are Luna's executions; this worker did not execute Lean. Consulted pinned sources:
Init/Data/{Nat,Int}/Compare.lean, Init/Data/Nat/{Basic,Lemmas}.lean,
Init/Data/Int/Order.lean, Init/Data/Ord/Basic.lean, Init/Data/Bool/Basic.lean.
No package/toolchain/default changes. The primary owns all actual Lean runs.
Material failed snapshots are retained in its verification receipt:

- r1 `d0ef6b9552f174202fb75b23106b1de2bb4bca32b902bf0698c3a62ae24c7304`:
  primary reports Lean 4.35.0, `lake build +YulangClosure.NativeIntegerComparison`,
  7.531 s wall, exit 1. Diagnoses: nonexistent Nat.compare/Int.compare expression
  names (the API is Ord.compare with Nat/Int theorem namespaces), reserved binder
  `prefix`, simplification turning a reflexive equality into True, pow lower-bound
  conversion, length successor inequality, mixed-sign inequalities and downstream
  Boolean goals. Complete material diagnostics are primary-owned evidence.
- r2 `2942ad637589247773b858b2342e67d0f84c71c79a885dc2fa4b0144745fbf70`:
  primary reports exit 1, 3.505 s wall, failure only on the two mixed-sign equality
  orientations and the final isLE/isGE conjunction. Exact remaining goals included
  `Ordering.gt = Ord.compare (↑(value ld)) (-↑(value rd))`, its lt counterpart,
  and the two isLE/isGE equations.
- r3 `91824cc00bb0ff3fe8fe22b525bbbdac337b87298b5b408b5d288b911114fce2`:
  primary reports helper exit 0, 3.535 s wall, module and 17 theorem checks
  accepted. The strict sprint axiom gate rejected Classical.choice in lex_value
  and its dependent chain, despite the helper's broader whitelist.
- r4 `b57ab2cec8b2cf4068a03acb771d97f41718345dd414bffb6cc46f0192540d11`:
  primary reports exit 0, 1.862 s wall, but the same forbidden axiom remained
  after replacing lex comparator simp by explicit specialized compare rewrites.
- r5 `0bde821d390a05738dbf03ff0420a2cb4f772f387c2e9f8962c48c4e83bc0852`:
  primary reports exit 0, 1.758 s wall, but the same forbidden axiom remained.
  Proof-term inspection had identified the local arithmetic omega calls; their
  first replacement Nat.sub_lt_sub_iff_right itself imported Classical.choice.
  Owner audit showed directional Nat.sub_lt_sub_right uses only propext.
- r6 `d337ca6a61aaf1ec2eddfe6ef83a34064dbc35e41981a178a288382cc756e597`:
  uses directional Nat.sub_lt_sub_right twice and le_antisymm/le_of_not_lt for
  digit equality, preserving every statement, parser and comparison definition.
  Primary reports exit 0, 1.858 s wall, but strict axiom audit still rejected
  lex_value. Focused branch checks isolated the remaining choice dependency to
  the nil/cons `simp at hlen` contradiction; cons/cons was clean.
- r7 `59264fe03a6b95960d2e5ee71957c7878d4e61be99ba44e528a03a1fd75ff2e3`:
  both impossible list-width branches now use only List.length_nil/length_cons
  and Nat.noConfusion. No omega or broad simp remains inside lex_value. All
  23 theorem statements and 22 examples remain unchanged. Primary reports the
  core order chain (lex_value, magnitude_value, compareParts_value, compare_decode)
  now meets the strict axiom gate. Only boolean_projections and its five separate
  consumer corollaries retained Classical.choice, isolated to the equality Bool
  bridge's broad simp. The other four bridges were independently isolated clean.
- Final r8 `2352602b7047611e9f9722d788ed1acdf9f4960d178c48f6a08b1a7054f93e79`:
  replaces only that equality bridge with explicit Iff composition:
  `Bool.eq_iff_iff.mpr (Ordering.isEq_iff_eq_eq.trans
    (Int.compare_eq_eq.trans decide_eq_true_iff.symm))`.
  Luna reports this exact bridge typechecked in owned scratch and audited only
  `[propext, Quot.sound]`. Final whole-module/all-23 audit is the next owner step;
  the isolated scratch result is not presented as a final artifact receipt.

No worker execution or axioms receipt is invented for any of these snapshots.

Outcome is CANDIDATE r8: prior full-module candidates compiled; core order
correspondence passed the strict axiom audit in r7; the final equality bridge
passed Luna's isolated scratch audit; complete final-r8 audit remains with Luna.
Independent source/math review and primary acceptance are not supplied here. Parent application, if these statements check and the source
map is accepted: the five current integer comparison consumers return the
mathematical Boolean relation on the two existing decoded values. This closes
only the scalar comparison/readback slice. First remaining premise is final-r8 complete kernel/signature/axiom audit
(Luna verification owner), including the six additional helpers omitted from the
first 17-declaration selection. Then fresh source/math review belongs to the
primary-appointed nonauthor. No mathematical assumption was added to repair the
proof, and no accepted input spelling or Boolean consumer was removed. Source-native trace realization, producer
correctness beyond the separately accepted invariant, all other primitives,
whole executor/inference A/B and production remain OPEN with their prior owners.

Finite worker ceiling 900 active seconds, conservatively charged in full;
worker Lean/checker calls 0 and checker time 0. No descendant processes, extra
scratch paths, generated outputs, nested CLI, compiler/test writes or background
processes exist. All synchronous shell/read/edit commands returned. Source and
contract dependency hashes were revalidated unchanged at 19:49:15 UTC. Proof r6
was superseded by the noConfusion repair and the explicit Bool equality bridge.
Final proof r8 froze at 19:52:47 UTC. This handoff freezes at the immediately
following SHA-256 receipt. Worker status STOPPED; all writes stopped, no owned
live process or descendant, no unresolved descendant lease. Both exact leases
are ready for primary-directed handoff. No further mutation is authorized by
this frozen receipt. Pending review/integration; not self-certified or
production-authorized.
