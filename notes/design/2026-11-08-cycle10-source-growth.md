# Cycle 10: source occurrence表の保守的拡張

## B4主定理への位置

`Main.B4Statement`の一般exactnessを達成したとは主張しない。cycle9のTy値による割当では別sourceのunknownを同一視する。今回は独立source IDの任意の有限表について、表を拡張しても旧普通状態の解を失わない橋を実際のsolverまで閉じた。source IDを実childから生成する規則はこの定理の入力であり、推論できたとはしていない。

最短の今回の連鎖:
1. `restrict_grow`: 旧Comp値を型・effectとも文字通り保存。
2. `grow_factors`/`grow_coherent`: 新occurrenceは同じsourceの既存意味にfactorする。旧表に無いsourceは任意のfallback値で埋める。
3. `extension_exact`: coherentな旧モデルとcoherentな拡張の存在が同値。
4. `growState`: 旧普通atomをretainでrenameし、拡張表の実identity atomを追加。
5. `growState_models_exact`: 新stateのモデルは旧制約と新source coherenceの連言。
6. `solver_growth_exact`: 実ordinary solverのacceptanceが元のidentity拡張stateと同値。

## 範囲

全table/extra/旧stateを量化する。extraには既存IDも重複IDも許す。旧effectを共有等式で潰さない。fallbackは任意のCompである。新しいordinary constraintの追加や矛盾を無害と主張するものではない。

監査のx-oracleをread-onlyで確認したが、現在Y2の構造区間構文の制限から、この一般allocator定理をY2の実測で検証したとは言えない。Y2を正しさの基準にしていない。意味論の未決事項を新しく決めていない。

## 残る主要な橋: 5つ

1. 実producer child/captureと独立source originの対応（今はtableが入力）。
2. endpoint narrowing/materialization後も閉じる有限仕事領域。
3. 普通制約更新・候補再生成と結合した単調飽和、停止。
4. 安定状態の四方向分類と子結果を保持する診断tree。
5. 正規順dictionaryとB4のsoundness/completeness/principalityを一体化する接続。

次回は1の生成関係を明示し、今回growStateに接続する。単なるTy equalityをsource identityに置き換えたと偽らない。
