# F1 の関数型変換を Lean carrier へ接続する位置（配置は解決済み）

**cycle3更新: 最新 `spec/05-effects.md` §5.5c は、F1を標準矢印部分型と分けた独立の明示cast判断に置くと確定した。以下のcycle1/2の選択肢は履歴であり、現在の未決定事項ではない。同じ設計判断を再質問しない。**

監査cycle1。新spec §5.5cの意味論は変更しない。Y2にはstructural subtypeのpure-argument passthrough分岐があるが、現行Common.common_arrow_iffは独立の反変row条件で、strictAppの効果合流とは別である。

例:
```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our higher(f) = f(ping::get())
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    v -> v
handle(higher plain)
```
Y2のno-prelude実行は7。fに`[ping] int -> [ping] int`を明示した変種はcheck成功/run時`conflicting type candidates: [ping] vs []`だった。後者のY2不具合を新仕様に採用しない。

選択肢（決定していない）:
1. **遅延**: 現行Commonの定理はそのモデルの結果として保存し、F1関数型変換のcarrier接続を未完と明示する。まずsurface judgmentsで普通の関数・効果付き引数・高階期待型・castの関係を独立に書く。
2. F1の変換を通常subtypeと区別する明示的なcoercion judgmentとしてモデル化し、起動時の効果伝播と意味保存を証明する。これは通常arrow orderを保存できるが、specでのcast/subtypeの位置づけの確認が要る。
3. Y2に近いpassthroughをarrow orderへ組み込み、新carrierに対する推移性・finite producer/solver exactnessを再証明する。現行Commonのiffとは違うrelationとなり、既存定理をそのまま新意味論の完成として扱えない。

監査では選ばない。確定した意味論に合わせるための形式化境界の質問であり、F1を撤回する提案ではない。

## cycle2追加観測（2026-11-08、決定はしない）

`notes/audit/f1-cycle-2-boundaries.md` の12入力matrixを追加した。両row明示版のconflictはdump --mono / --runtime-irでも再現し、runtime以前のspecialization境界。引数rowだけなら7、wildarg直接版はunhandledだがeta版は7。直接適用/pipe/推論高階の成功だけで全F1完了とはできない。既存の遅延案と未決定点はそのまま。

また `notes/audit/default-effect-boundary-cycle-2.md` にdefaultのeffectが関数の表示行から落ち、外側明示handlerではunhandledとなる例を記録した。直接catchでは7になるため、任意defaultの不可処理と一般化しない。新specはeffectful defaultを認めており、これを旧失敗へ戻す提案ではない。source→carrier→実行入口が同じeffectを保持することを、まだ完成と呼ばない。

## cycle3: 配置の決定を反映、実装の相違は別に残す

`Common.common_arrow_iff` の標準関係は現在の決定と整合する。そこにF1の特例を足す提案は取り下げ、独立cast/source接続の検証と区別する。`notes/audit/y2-claims-f1-cycle-3.md` に普通のunused argumentがdirectでは起動し、高階経由では起動しない対照を追加した。これは旧処理系の観測で、起動時放出という新仕様を変更する理由にしない。動的solver provenanceと修正は未実施。
