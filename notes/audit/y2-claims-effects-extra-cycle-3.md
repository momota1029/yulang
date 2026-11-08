# Cycle 3 extra effect boundaries

Y2 d4c8bc8fc。新spec/Lean 816ed8f1d。過去 `y2-claims-effects-types.md`、`y2-claims-hygiene-boundaries-cycle-2.md`、全claimsのcopy/shallow/residual検索を実施。EFF005/006はfamily別名性/private helper、EFF007/008とHYG01–03はshallow再開と多重shot。今回は残余別family、**public copied helper内のoperation再束縛**、**operation arm自身の効果**という未掲載の具体境界を追加。copy-isolatedは既存EFF005の追加対照であり新規主張数に数えない。

共通コマンド: `/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache {check|dump --poly|dump --mono|run --print-roots|run --interpreter --print-roots} /tmp/audit3/extra-NAME.yu`。全入力と全stdout/stderr・時刻・終了値は `runtime-cycle-3-effect-extra-final.md` / JSON。Leanは読取のみ。

| ID | 出典 | 規則 | 例 | 実機の結果 | 新 spec | Lean | 分類 | 備考 |
|---|---|---|---|---|---|---|---|---|
| C3-EFF-RES-01 | 旧 effects.md「handlerを重ねる」63–96; effect-variable-subtractable.md「目的」 | handlerは対象familyを消費しても別familyの残余を外に保存し、その別familyのhandlerと重ねられる。 | `seven: one: my first=ping::get(); pong::get()`。oneはpingを1で再開、sevenはpongを7で再開。全コードraw residual | 共通5コマンド全exit0。oneのpoly `int [ping; 'a] -> ['a] int`。両run `run roots [7]` | 05 §5.2:残り行は外側へ伝播 | Effects.residual / mem_residual / unhandled_operation_retains_family / Computation.shallowHandle | 一致 | 有限の異family合成例と部品定義が一致。任意source loweringとの接続証明ではない。既存shallow同family二重handlerとは別対照。 |
| C3-EFF-COPY-01 | 旧 effects.md99–114 copy先operation・public companion継承; 実機poly参照先 | public member内のsource operation呼出も、copy先のoperationへ再束縛される。 | `act original: our get:()->int; our twice()= my first=get(); get(); act local=original; handle(local::twice())` | copy-callの5コマンド全exit0、両run3。poly original.twiceは[original]でoriginal.get参照、local.twiceは[local]でlocal.get参照。copy-isolated対照check/poly/mono0、両run1 `unhandled effect request original::get` | 05 §5.6:copy先helperのoperationもcopy先へ付替え | copy source elaboration/再束縛定理は今回未同定 | 一致 | public helperの再束縛を具体的に確認。private helper同伴は旧実装で既知の相違なので今回の成功をprivateに拡張しない。 |
| C3-EFF-ARM-01 | 旧 notes/design/handler-row-subtraction.md:710–728 `result_eff = residual + arms_eff`; effects.md handler節 | handlerの結果効果には元computationの残余だけでなく、operation arm自身が発生させる効果も残る。 | `inner(action:[ping]int)=catch action: ping::get(),k -> pong::get(); value->value` をpongの非再開outerで包む | arm-outsideの5コマンド全exit0。poly inner `int [ping; 'a] -> [pong, 'a] int`。両run99 | 05 §5.2 handler/伝播、§5.3 shallow。arm効果の結合式の直接記述は今回未同定 | Effects.Computation.shallowHandle はcapturable枝でonOperation結果をそのまま返す。shallowHandle_boundedのarm側仮定も参照 | 一致 | 別familyを使いouterが元pingを直接奪った可能性を排除。May13文書は旧solver設計メモで、式と今回実測の一致のみ。旧shift/peel全体を現行規則に復元しない。 |

## 探索・制限

最初の `runtime-cycle-3-effect-extra.md` では no-preludeなのに `+` を用いたためresidual/copy-callがunresolved #op:infix:+で失敗。算術不要の逐次形に直した。初回はcacheがread-onlyの警告もあり、後続は--no-cacheで再実行。失敗raw/JSONを保存した。中間 `runtime-cycle-3-effect-extra-fixed.md` のarm-outsideは同familyだったためouterが元の要求を奪った可能性を除けず、最終版ではping→pongの別familyに直した。最終版の成功だけを判定に用いる。

60 CLI実行(初回・中間・最終各20)、各timeout30秒だが全て通常終了。repoソースの編集・cargo/lake build・公開は行っていない。新規の規則を決めたりspec追記案に格上げしたりしていない。
