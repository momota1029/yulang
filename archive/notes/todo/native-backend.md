# Native Backend TODO Archive

この TODO は active queue ではない。Cranelift/MMTk native backend は 2026-05-25 に
active workspace から外れ、current CLI からも `yulang run --native` / `yulang native` /
`yulang run --mmtk` は消えた。

現在の user-facing 実行面は VM:

```bash
yulang run program.yu
yulang run --print-roots program.yu
```

## Archive References

- `docs/native-backend.md` — public-facing archive summary。
- `docs/native-experimental-release.md` — 2026-05-18 の archived release-gate note。
- `tasks/done/2026-05-14-native-backend-history.md` — archived backend の節目。
- `archive/notes/refactors/finalized-vm-handoff-2026-05-25.md` — active workspace から外した整理。

## Future Restart Conditions

将来 execution backend を再開する場合、この TODO をそのまま active に戻さない。
次を満たしてから、新しい track として切り直す。

- VM/runtime semantics が current oracle として安定している。
- monomorphize / runtime type surface audit が strict に通る。
- compiled-unit cache が std 専用特例ではなく dependency surface として説明できる。
- user-facing diagnostics が internal monomorphize/runtime error を直接漏らさない。
- backend が std path / fixture 名に依存せず、structured IR / evidence / constraint を見る。

## Useful Leftover Ideas

古い native work から残す価値がある知見:

- VM を behavioral oracle にして、別 execution path は小さい compare で広げる。
- control-heavy benchmark では runtime `Expr` clone と continuation/frame payload が支配的になりうる。
- effect-aware CPS IR は handler / resumption / thunk boundary / local return を明示化するには有効。
- optimized CPS から direct-style / SSA island を切り出す発想は、将来の backend でも使える。
- compact `YValue` / object-header / trace-slot design は、VM 直下の runtime layout を見直す材料になる。

## Do Not Carry Forward Blindly

- native 専用の言語仕様。
- VM と違う handler semantics。
- 名前や std path 文字列に依存した lowering 特例。
- runtime type surface が strict でない状態での広い codegen backend。
- performance gate を満たさないまま user-facing backend として維持すること。
