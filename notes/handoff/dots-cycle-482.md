# C482: 元の型付け記録と実調査位置を保つ K2 終点検査

道具: Lean 4.35.0・GitHub、モデル名不明; 委譲: 1 回、task /root/yulang302_resume、モデル名不明。

## 結果

- 著者由来の旧 C331 の全 `Read`（引数、field、閉レコード末尾を含む）に、有限の検査データがあれば元の判断が成り立ち、逆に同じ著者表に正しく付着した任意の元の判断ならそのデータがある。保存済みの旧照合列は元の順序・raw と著者の両 ordinal・先頭選択・同じ型付けの capture を照合する。
- 元の実 field の最小型商での K2 の正負を、同じ要求の全引数での root safety と実際に選んだ経路につなぐ。旧座標・元の Pose・decl ordinal・同じ状態の Fit を維持。完了出力側は元の produced ordinal、owner、先に記録された同一完成、現行 native grant/stamp を照合した箇所でのみ保証。旧版・保留・出所違い・違う source report の対照を実行した。
- 実出力のない既存の C479 適格入力と同じ Fit で、記録済み型付け列と、選んだ深い raw ordinal が一致しない例を示した。重複する等しい行に加え、別の既存 raw 行が未開放である例でも、正しく認証した著者 row と実際の geometry の終点を両方残し、既存の有限 bisimulation で終点の K2 判定だけを移す。未開放行を source や active release として採用しない。先へ読み進める許可にはしない。

G04Producer の C480 範囲の存在は変わらない。G04 全体は未完、残り 20 / 24。任意の内部選択経路の逆方向、および全ての native 由来の経路が同じ exact source authority を持つことは証明していないので、平坦入口の全体タグへは入れていない。開始時は I-97 段階1が未採用だったが、終了時に同じ権威の inbox のまま C481 だけが採用された。今回の削除はゼロ。G05 は開始せず、旧ソースの変更・削除なし。次回は実 path の ordinal を同相の型付き出所とどこまで正確に突き合わせられるかから。

## 検証と反映

開始 2026-11-28T05:31:54.000Z。権威 `e36a04e087f691695e79f1deb930048bcf8c4d24` および I-97 を確認、work は C481 成果を保持。+10 `02d41a43cba76e60d13013caa24ae78ff1707d3e`、+20 `ef7ea46417d069e9b2dd407be93872e2b633acc5`、+30 `ce12fee422440058a1476d1a4ef243bcc3255d16`、+40 `e61d4774562a6bd1454205036fd1a8d8e1342dff`。+30 で Lean 固定 `7d19ec32eb128a3f102b5b4c0a1035114cae671a`。新規 18 source、23 standalone Audit、旧集約への import 18 行だけ。対象 41 ソースの `lean --trust=0 -DwarningAsError=true` とそれらだけの集約の終了コード 0、70 checks は標準公理の範囲。実行回帰 16、I-94 違反ゼロ。全体の `lake build` と `verify-lean.sh` は dot では未実行。Yulang2 実機再実行なし（Graph I-93 の挙動の旧実機一致を主張しない）。開幕時の yulang3 の差は検証スクリプトのみ。終了時の同期は本サイクルの反映に含めない。設計と必須残差は `notes/design/dots-cycle-482-authored-quotient.md`。使用量は不明。

報告確認時の経過 53 分。最終書込み前に integration が C481 終了 `425a452e143146a874d8d9de7cf951922aef5662` へ前進したことを確認。C482 はこの祖先上にあり、凍結した Lean は変更せず、報告と heartbeat だけを書いた。
