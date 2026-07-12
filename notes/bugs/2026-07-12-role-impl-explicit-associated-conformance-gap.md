# role impl の explicit associated type が method 実装と照合されない

日付: 2026-07-12。発見: Codex（canonical cache interface の candidate
normalization 調査中）。
状態: **open / type-soundness blocker**。Option 1 の cache 機構とは独立した既存問題。

## 症状

role impl が associated type を明示しても、その宣言と method body の実型が一致するかを
`check` が検証しない。

```yu
type box 'a with:
    struct self:
        item: 'a

role Index 'container 'key:
    type value
    pub container.index: 'key -> value

impl Index (box 'a) int:
    type value = bool
    our c.index i = c.item
```

`c.item` は `'a` だが、candidate table は `value = bool` を公開する。

```bash
target/debug/yulang --no-prelude --no-cache check /tmp/associated.yu
```

観測結果:

```text
missing schemes: 0
lowering errors: 0
```

method を concrete に使用すると、source-level diagnostic ではなく specialize の内部 slot
競合まで遅れて失敗する。

```yu
my boxed = box { item: 42 }
boxed.index 0
```

```text
conflicting type candidates for slot 0: bool vs int
```

## 根本原因

`crates/infer/src/lowering/body/impl_decl.rs::register_role_impl_candidate` は associated type を
二つの独立した surface として lower する。

- `candidate_associated_anns`: `type value = bool` を保持し、`RoleImplCandidate.associated`へ入る。
- `requirement_associated_anns`: role method requirement の `value` を置換する別の fresh
  annotation variable。

`lower_role_impl_associated_vars` は後者の variable を確保するだけで、前者の explicit
annotation とは subtype / invariant / unification のどれでも接続しない。
`RoleImplLoweringContext.associated_signatures` も後者から作られるため、
`connect_impl_method_requirement` が検査する method signature には explicit `bool` が現れない。

単に requirement signature を `candidate_associated_anns` から作るだけでも十分ではない。
調査中にこの配線を試すと、concrete な不一致さえ error にならず、method scheme が次へ変形した。

```text
box(int <: int & bool) -> int -> int
```

generic impl の head binder は本来すべての `'a` に対して成立すべき universal binder だが、
現行 solver では普通の flexible inference variable として `bool` へ狭められる。
したがって本修正には explicit associated の配線だけでなく、generic impl conformance の
proof boundary が必要になる。

## 実害

- 壊れた impl を `check` が受理する。
- 未使用なら壊れた candidate が diagnostic 無しで compiled surface 候補へ残る。
- 使用時の失敗は impl 宣言位置ではなく specialize の `slot 0` となり、原因位置を失う。
- evidence-vm へ到達する前に specialize が止めるため、この最小例で memory unsafety は
  観測していない。ただし downstream の偶然の拒否は source type checking の代替にならない。

## 境界

- explicit associated type を持つすべての role impl が対象で、`Index` 固有ではない。
- associated type を省略する既存経路は、candidate と method requirement が同じ inferred
  variable を共有し、既存テストでは body return から正しく clamp される。
- role method requirement 自体の shape / concrete check は存在する。欠落は explicit
  associated assignment と universal impl binder の conformance である。

## 関連

- `crates/infer/src/lowering/body/impl_decl.rs`
- `crates/infer/src/lowering/expr/method_body.rs`
- `crates/infer/src/lowering/signature_match.rs`
- `crates/infer/src/role_solve/`
- `notes/design/2026-07-12-generic-role-impl-conformance-spec.md`

