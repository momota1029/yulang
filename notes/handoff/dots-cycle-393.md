# Yulang cycle 393

この周に閉じた補題: なし（I-69: 元 body からの event 生成・kinded where 参照を検証、分割なし）

I-69 の不足は C392 と同じ (a)。実選択が元の宣言と head/where 捕捉からその場所の literal RHS を生成する source rule が要る。S13bbba のみを調べ、retention の S13bbbb は変更していない。

## 実装したもの

- [source event module](https://github.com/momota1029/yulang/blob/916101e5b2e3daaa28fa2f9d09033dc1d8260641/lean/Yulang/GeneralDeclarativeI65OriginalBodyEvent393.lean)、[独立 audit](https://github.com/momota1029/yulang/blob/916101e5b2e3daaa28fa2f9d09033dc1d8260641/lean/Audit/Cycle393OriginalBodyEvent.lean)。現 registry の実宣言 ordinal と visible の根拠・元 logical where placement・head capture の frame から、既存 `sourceNames` を使い where の demand/capture と全出力を**新しく組み立てる**。前の event や receipt が一致するという仮定を立てず、各元 output ordinal の actual `Supplies` と body derivation から、元の順で `LiteralLocalEvent` を作る。array でなく `Fin` と `List.ofFn` で位置を保つ。普通の compound translation と C392 bare/tagged native を同じ output 列で混ぜられる。explicit capture と role default の位置は別。
- `generated_where_binder_at_original_output393` は原 clause/where output equation ordinal を探し、その同じ emitted child の固定出力を親 authentic body slot として読む。 `generated_where_binder_kinded_rhs393` では、**実際の native 引数の独立な source proof** の `ValueBind`/`RowBind` を、その時につくられた同じ point で得る。slot 数値だけから種別を判定しない。
- [exact Body と compound 限界の設計/証明](https://github.com/momota1029/yulang/blob/62b39b00b16cef9d66048d4e68c47f4ba994bce0/notes/design/dots-cycle-393-authored-body-event.md)。元 nth receipt が持つ **同じ Body・target・書いた RHS** の導出を直接得ることを検証した。現 declared mode の nominal が record/join 等に直に入ると普通の translate に fallback できず、root が record/join の場合は現在の native app/tagged app rule にもないことを一般形で証明した。これは現在の型付き RHS 表現/規則の不足で、言語の拒否や新しい意味論の判断ではない。別の実験では、localRule を定義的に変えない scoped な `BodyReplayJudgment393` の actual addressed ledger の全 node を、元の source proof に結べた。これを任意の `Classifies` や noncovered compound の証明にせず、global には登録しない。

## 検証

Lean 4.35.0 と exact `lakefile.toml`。 `lake env lean --trust=0 -DwarningAsError=true` で module を scoped build し、別 import audit を単独実行。GitHub から immutable source/audit を取得し直し blobs を照合、別の output で再ビルドと別 audit、ともに exit 0。六宣言の依存公理は `[propext, Classical.choice, Quot.sound]`。設計の exact Lean bytes も `--stdin --trust=0 -DwarningAsError=true` で再実行、六検証 exit 0、同じ標準公理のみ。既存 source manifest 7,356 件と focused dependency 3,806 件は source hash 照合（全件再コンパイルではない）。full build、Rust、checker は未実施。

## 残り

S13bbba は全称では未完。**一般の実選択から**、この frame の actual head/where placement と kinded binder source proof/全 output の body derivation を生成すること、native を含む一般 record/join で exact literal RHS を表す規則が残る。C384 の key/kids や C386 の任意 `eventAt` だけから推定しない。受理条件をこの scoped rule に制限していない。spec 未決の挙動・順序を見つけたわけではなく、質問ノートなし。

**14 = 未証明 3（S01・S10・S13bbba）+ 一部 11（S02–S09・S11–S12・S13bbbb）。** 固定した文、上段、checklist、S13bbbb は同一。Step 1 は未完、Step 2・3 は未着手、C は後回し。fixture、停止性、旧 Local/C334、意味/受理条件は触っていない。

`work/dots-main` expected-head non-force のみ。新規 Lean module/独立 audit・barrel 一行・設計・心拍・報告の 6 パス。凍結2件は blob ID のみ。使用枠は不明。
- 最終照合開始 `2026-11-24T13:20:54.819Z`（50 分経過）。
