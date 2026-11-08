# F1/strict application のLean既存境界の読取（cycle 3）

読取基点 `816ed8f1d`。このノートは定理のstatementを確認したもので、今回Leanを再buildした結果ではない。

`CommonCoreStrictRuntime.eval_forceApplication` は、任意のKey（DecidableEq）、有限のresolved shape context Γ、shape a/b、function : Expr Γ (arrow a b)、argument : Expr Γ a、runtime : Env (Tree ...) Γについて、pair captureによるforceApplicationの評価が「functionを評価→argumentを評価→得られたfにpure valueを渡す」というComputationのbind列と等しいと述べる。効果の集合だけでなくrequest treeの等式であり、payload/continuationを含む。`eval_agrees_with_two_lets` は既存の2-let strict loweringとの評価一致。

`infer_forceApplication` は、function推論がarrow input outputとfunctionRowを返し、argument推論がactualを返し、pure actual.valueがinputにCLeで入るという前提の下、loweringの推論結果がoutput.valueと `functionRow ++ (actual.row ++ output.row)` になると述べる。前提付きのresolved checker結果であり、任意sourceのshape推論成功を保証しない。

`source_erasure` と `operational_erasure` は実際のcommon loweringとresolved loweringが同じCore constructor形にeraseすることを示す。これを全表面言語parserからの一般的意味保存と読み替えない。

`Core.CommonSyntax.Typing` の `app` は従来のcomputation引数適用で、引数の行を別に合流しない。`strictApp` はpure引数値との適合を前提としてactualの行を戻りに合流する。両者は別constructorであり、旧Y2の高階関数をどちらにelaborateすべきかが自動的に決まったことにはならない。

F1は最新spec§5.5cとplan F2で独立castと確定済み。ordinary unused-argumentの起動、高階consumer型が要求される位置でのcast挿入、旧Y2 specializerの再特殊化を、strictApp単体の評価等式から一括で完成扱いしない。今回のdirect11/high22/eta11の実機対照は、その接続に必要な回帰候補である。既存定理は変更・弱化しない。
