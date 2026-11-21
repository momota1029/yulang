# Yulang C328: 端点しか見えない実中心の射影と、選ばれた子・出力の検算

2026-11-21 19:30 UTC 枠（実開始 19:30:19 UTC）。基準は C327 の固定版 e53f11afe3fe80f4ab90980c39040f93730e5592。開始時の integration/m1-final (9d2bf08526fe8bf2f6e4d616b52268b01c304d36) から standing orders / inbox を再読し、I-56 の宣言的健全性を優先した。I-57 の凍結二ファイルは本文を読み書きせず blob ID だけ照合した。公開先は private work/dots-main のみ。

## 証明済み

1. **端点を実中心に置き換えずに、共変成分を読める。** OpaqueChannel328.probe_step / OpaquePair328.reconstruction は、任意の正則型が二つの pair 型の間にあれば、その実値から二成分を射影して同値な pair を再構成する。観測の深さ・負位置ランク・環境を固定しない。元の実型はリテラルの pair でなくてもよく、結び・交わり・mask を通す。観測チャネルが無いことは top と違い、内側の自明な観測も通さない。同じタグの variant には OpaqueVariant328.reconstruction、単項不変 nominal には既存の支持された実パラメータを使う OpaqueNominal328.retains がある。
2. **支持された端点から任意の有限混成木を構成する。** OpaquePlan328.extract / OpaqueNested328.build は実際の支持付き下・上 trace を読み、pair・variant・単項不変 nominal・捕捉の再帰混成で実中心の通常行、順序付き捕捉、各区間を構成する。型が同値なだけで行の出所を追加しない。すべての旧モデルは同じ旧名と指定した固定名のまま拡張でき、拡張モデルは旧状態に制限できる。OpaqueShared328.complete は、同じ binder の各実値が全モデルで一致する独立な根拠があれば、反復の下限を join・上限を meet で合流し、通常の head バッチと全捕捉区間を導く。OpaqueRepeatCut328.exact_cut は、同じ下端 3・上端 4 が二箇所の実際の支持付き端点 trace に現れても、一つの実値で両成分を説明できない具体モデルを確認した。これは端点だけからの推論の反例で、承認済み安定選定がその反復宣言を受理した反例ではない。
3. **同じ現在状態で実際の子リストと普通の出力を照合する。** OpaqueSingle328.compiler_head は任意の checked な一引数宣言で、上記の実形状・非反復の場合に、実際の source name table を使う head 義務と捕捉区間を与える。OpaqueBatch328.accepted は実 where コンパイラと提案された子需要の役割・捕捉三名・要求先・順序を照合し、独立に計算した出力行が同じ現在状態に実在すれば、通常の Result / Compiles と全現モデルでの局所 Meaning、子需要の Declared を導く。一つの実配置の照合であり、すべての合法配置のリテラル名が一意とはしない。出力行が選定時点に無い場合にそれを仮定したり、固定出力先を別名に変更したりしない。
4. **選定済みの二つの実例。** 純粋 pair 実例は初期状態に center の行も別 host からの中心導出も無く、端点から実 (3,7,4)・(3,8,4) を命名し、左右を入れ替えた二つの非点モデルで両端点と異なることと選定済み辞書を確認。混成実例は pair の内部に variant 4 と不変 nominal 0 のある checked な宣言で、(3,17,4) と (9,9,9) を読み、要求先 5 を持つ子を実際に選ぶ。固定の親出力 6 = 5、子出力 5 = 17 を持ち、任意の最終モデルで親子を同じモデルの再帰 Evidence として検証した。NestedBatch328.compiles / full は子を実コンパイラから照合し、同じ状態の行から全バッチと Meaning を独立に導いた。誤った出力先と、二需要を逆順に並べる独立な負例を拒否する。variant の実 payload が int ∪ bool の具体モデルで中心は両端点のどちらとも同値でない。元の未命名状態ですでに同じ子が選定されたとはしていない。
5. **モデル保全と K2 検査を切り分けた。** 新しい pair 行だけでは旧支持や K2 は増えない（OpaqueAuthority328.exactly_old_support / OpaqueGraph328.cycles）。射影の区間も普通の制約に書くと、旧状態で明示されなかった端点間の有向 bound が現れ得る。OpaqueDiagnostic328.separates は元・拡張とも実際の正則型モデルを持ち、全旧モデルを保つのに raw K2 グラフにサイクルを生じる例。OpaqueCompress328.bound_exact / alias_exact は旧名・保護名に限れば変化が二つの端点間の有向橋だけで正確に表現されること、すでにその橋があれば旧名の alias は保存されることを証明。OpaqueAuditGraph328.no_cycle は、診断用に新成分名をその下端名に写すグラフの一方向安全検査。下端名で実値を置換できるとも、検査失敗で安定ルールが K2 を返すとも主張しない。

## 残り

- **(4) 一般辞書健全性: 1本。** 任意の承認済み安定 Local.selected から、支持付きの実際の head・共有捕捉と、同じ現状態に実在する普通の write／実際の順序付き子リストの一致を導く。今回は opaque な実中心の pair・variant・単項不変 nominal の任意混成と、実子・出力への明示した一般片を閉じた。反復の実値一致や支持・診断の保存は端点や全モデルの同値だけでは出ない。任意の形・mode と実際の安定選定に一般化するのが残る。支持不足と K2 が重なる場合の優先順位は変えていない。
- **(2) 成功停止を条件にした部分正当性: 2本。** 到達済み停止成功を安定した宣言的フレームに射影すること、その診断木・全要求出力を照合すること。変更なし。停止性、物理 solver/journal、Rust、言語の受理条件変更は対象外。

## 検証

Lean 4.35.0。追加モジュールに対する scoped Lake warning-as-error、各追加ソース・独立監査の trust zero と warning-as-error、I-57 に従った差分検査・同一変更の import、scoped axiom gate、宣言的依存検査、固定ソース再実行を notes/verification/cycle328/ に保存。全体の Lake ビルド・Rust は実行していない。

focused build 1,193 jobs、追加ソース 35、独立監査 9、宣言の明示チェック 224、固定 proof pin から取得した独立監査 3 件のバイト一致と再実行はすべて PASS。scoped gate は 63,044 宣言、宣言的依存検査は今回の 747 定数と 5,857 個の推移的な型・値の依存を照合し、対象の物理 API / Step / journal / 旧 resolve に依存しない。新規公理、証明の穴、kernel 判定の迂回はない。
