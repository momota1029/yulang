# C338: 支持された入れ子のレコードを、選定と実コンパイラへ接続

## 範囲

2026-11-22 05:30 UTC 枠。開始 05:28:20 UTC、最終報告の準備時刻 `2026-11-22T06:18:25Z`。開始時の `integration/m1-final` は `102feb777b54b614656068bbc29cf1754d6f9d66`。C337 を統合した差以外で新しい owner 指示はなく、standing orders / inbox I-61 / spec §4.3, §6.5 の支持付き端点、既存 K2・I-58 に従った。C337 開始 pin `cdfca81e37ee0b502b4b7bdf00a56720dbc2ba5b`。C338 の検証済み証明 pin: `ac9fb5040adf67ec68fd3460741f4816363a2b33`。書き込みは `work/dots-main` のみ、expected-head/nonforce。

## 今回 Lean で確かめたこと

- **正規化から名前付けまで。** `CompoundPattern338.normalized_labels` は本物の pattern 正規化で record spine の可視ラベルが重複しないことを証明。任意の状態と実 capture に対し、両端点の本物の支持付き spine と可視性から、要求順の正確な `Read` と実 compiler job を構成する。投影した field の左右の spine は、異なる支持付き alias を通ってもよい。端点を中心にしたり、元中心の RHS を補ってはいない。
- **独立な source から深さ任意の有限 record へ。** `CompoundSources338.compile` はモデル・名前・job・receipt を含まない `Source`（両端の実 syntax・由来）から、実行 route と実 capture を作る。 `CompoundReadback338` が各子に渡した RHS は元端点の該当ラベルの実 operand、末尾は正規化済みの真の standalone 差分。 `CompoundTree338.tree_exact` は全 binder をソースの深さ優先順に並べ、繰り返しを落とさず、対象の実 triple、旧・新 receipt、旧モデル割当を保守的に保持する。field の中継用 triple は I-58 の binder に数えない。
- **同じ source が元の照合にも使える。** `CompoundHeads338.positive` は同じ `Source` から以前の `InlineEndpoint331.Matches` を構成。新しい選定優先順位、未知形の拒否、中心行の追加要求はない。下限の既知性・K2・候補の選定は既存判断のまま。既存普通 input と nested record input を同じ順序つき入力列へ混ぜられる。
- **実 where/出力と全選択木。** `CompoundCompiler338.body_ready` は `compileBody` をそのまま計算し、独立に作った occurrence 順、子の順序、実 table の固定 target を使う。 `selected_sound` は現在 receipt の普通状態と exact sidecar を使い、**選定後だけ** I-58 で各実中心と body が使う binder の中心を同値にする。 `CompoundDictionary338.dictionary_sound` は以前の正の証人と新しい compound 証人が混在した任意の選択木について、一つの同じモデルで再帰 Evidence が得られると示す。raw solver の実停止についての主張ではない。
- **具体回帰。** 元中心 1 には RHS がなく、外・内とも幅の違う上下端で、checked な head `{7:{9:'x, ..'inner}, ..'outer}` を読む。実 capture 順は `[0,4,1]`。実ルートには順に field/RHS と外残余、内 field/RHS と内残余の四つがあり、入力を満たすモデルと実 compiler の target table を確認。実際に元の候補規則で親・子とも選定、子の実 interval **(19,14,20)** と target **5**、親 **6=11** と子 **5=14** の literal compiler 出力を確認。外・内の実残余中心 **11,17** がともに exactEmpty である一つのモデルで、両節点の再帰 Evidence が成立する。

- **真の未知 tail を読む部分も分離。** 両端の支持付き可視 prefix だけから、各選択 field の actual interval と exact standalone 差分の上下端・中心を計算し、旧名と固定 target を保ったまま fresh interval にできる。ordinary へは bounds だけを足し、未知残余の RHS を source には足さない。opaque tail の支持付き閉鎖が本当に無い実例では、尾に隠れた取り除き済みラベルがあり、元の尾をそのまま残すことは exact 削除ではない。この進展は open-prefix の意味と名前付けであり、旧選定への自動編入ではない。

## 未完の橋

- **宣言的 (4)**: 元 I-60 は **0 群**。I-61 追補は **1 群**。任意深さの有限で独立に支持された record/binder の fragment は閉じた。残るのは同じ source 上で record と混ざる非 record の compound head（nominal/variant/join など）、および上で得た未知 tail の値 receipt を実際の選定・再帰 body に統合する橋。既存の positive observer との全域同値や言語の追加 rejection は置いていない。
- **旧 Local**: 全到達状態・全診断との対応は **1 群**。上は元の *positive endpoint* 照合への輸送で、旧 Local 全体の無条件な逆対応ではない。
- **(2)**: 実成功停止だけの部分正当性は **2 群**。(A) 実 raw 成功停止の各 occurrence の current source/output provenance と記録済み／未 install の両 receipt。(B) 得た literal placement・固定 target・全診断木を一つの同じ raw モデルで宣言的結果へ輸送。今回の二節点は宣言的層の実 compiler であり、raw solver の停止結果ではない。停止性と Rust の実行は扱っていない。

## 検証と復旧

18 新規モジュールを対象とする focused Lake --wfail（1277 jobs）、全 source と独立 7 audit を trust=0 / warningAsError、70 定理の個別公理を確認。範囲限定 gate は 65,948 宣言、境界検査は C338 定数 558 件から 5,916 件の型・値依存を確認し、物理 solver 依存なし。別の detached checkout で固定 pin の 18 source・7 audit を exact bytes と照合して直接再検証。公式 diff-only validator と git diff --check も PASS。コマンドとログは [再現ノート](../verification/cycle338/reproduce.md)。

I-57 の `lean/Audit.lean` と `lean/README.md` は読んで書き戻さず、変更前後を blob ID だけで確認。 `lean/Yulang.lean` は全 bytes/hash を照合し、新規 module import だけ追記。起動後、exec-server が複数回切断・再開し、最初は /tmp の toolchain、後から未公開 source の一部を巻き戻した。公式 Lean 4.35.0 の既知配布 SHA-256 を確認して持続する作業場所に復元。中間公開先を優先して exact bytes を復旧し、取り戻せたものだけを再チェックした。全 repository の Lake/Rust build・実行は行わず、利用枠残量は不明。質問ノートなし。

次は、真正に支持された open prefix の exact named receipt を、存在しない RHS を根拠にせず、既存の選定と同じ ordered producer に接続する。次いで nested record に混ざる既承認の nominal/variant 読みを同じ ordered producer に組み込み、(2) の raw current receipt A へ。
