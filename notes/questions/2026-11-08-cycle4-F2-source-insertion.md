# F2: source expected-type insertion is still a separate bridge

spec 5.5c fixes the explicit conversion judgment and forbids adding it to arrow
subtyping. The new `CommonArgumentEffectCast.ArgumentCast` and
`ArgumentEffectCastRuntime.ResolvedCast` implement that decision without changing
`Common.common_arrow_iff`. Their preservation statements quantify over all rows,
shapes and resolved request trees. They do not select a source insertion policy.

Example (schematic Yulang):

```yulang
our plain(x: int): int = x
our higher(f: int [ping] -> [ping] int) = f(ping::get())
higher plain
```

The audit found old Y2 check acceptance but specialization failure for this kind
of explicit higher-order annotation. We do not import that mismatch. The new
resolved semantic theorem accepts any valid consumer expecting the converted
arrow, but does not prove how `Core.infer` inserts that cast in `higher plain`.

Choices, delayed first:

1. Keep expected-type insertion separate and do not label full X25 PROVED until
   the source elaborator has a fixed insertion judgment and proof. The current
   general conversion/strictApp boundary is independently usable.
2. Insert only where a source annotation supplies the exact converted target
   arrow; this would require specifying interaction with other casts and
   ambiguity/priority.
3. Permit a broader bidirectional expected-type insertion rule, again requiring
   a decision about interaction with user casts and chains.

No choice is made here. This is not asking whether to keep conversion out of
subtyping: that is already fixed and has been followed.


## Source omission is not an empty row

The source `'a -> ['e] 'b` accepts arbitrary incoming rows by spec 5.5c. The
new kernel lemmas have an explicit `rowEmpty` source premise because the existing
strict lowering passes an evaluated pure value. They **do not** identify omission
with an empty row, nor prove that the source notation elaborates to that kernel
arrow. The full source-to-kernel bridge remains missing.

For example, `plain(ping::get())` must not be rejected on the theory that omitted
input row means `[]`. Our semantic adapter accepts the effectful argument and
retains its request tree, conditional on a value-only kernel function, but the
compiler must still establish how the omitted source arrow denotes that uniformly
applicable interface. Defer the source elaboration model first; possible models
include a distinguished source omission marker elaborated through this adapter,
or an explicit row-polymorphic source scheme. These are model choices to be
justified, not changes made by this patch.


## 回答（ユーザー, 2026-11-09）

**選択肢 3**: 型が求められたとき、変換を自動で入れる（需要駆動。注釈の有無によらない。`labeled` の cast と同じ流儀）。`spec/05-effects.md` 5.5c に反映。X25 は、この挿入の判断を通して PROVED にする。ユーザーの `cast` 宣言との優先順位は `labeled` と同じ扱い。「ソースの省略された引数の行」は空の行ではなく全能、という点は、ソースから核の矢印への橋として別に必要（上の「Source omission is not an empty row」）。
