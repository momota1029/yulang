# 次サイクル: 動的飽和から外側分類までの最短の橋

2026-11-08 / I-3 priority 3–4。読取調査による**未証明の作業案**。このノートに書く型名 `SourceProblem`, `Config`, `Generate`, `Step`, `FinalClassify` 等は、特記しない限り今後定義するための仮名であり、既存 Lean 宣言でも証明済み命題でもない。言語意味論を追加・選択しない。T1c、一般 B4、X13–X16 の外側 PROVED は未達のまま。

## 1. 現在の実データと、尺度が届かない箇所

- `CommonRoleOpenProducerAccess.child_step/child_decreases/accessible` は実 `Child (Local declarations)` を `CommonRoleOpenDescent.Step` に埋め込み、`weight q = q.lower.weight + q.upper.weight` の減少を宣言 checker から証明する。ただし前提の `Inspect d.head q.lower (.hit lp)` と upper の対応する Inspect は、**固定した両 endpoint** の照合である。
- `CommonRoleOpenRecursivePass.run` は状態を兄弟へ渡し、最後に兄弟・親を再観察する。しかし再観察で新しく現れた child をさらに再帰して解く driver ではない。`run_exact` は一回 pass の `Runs` と同値。
- `CommonRoleOpenFiniteClosure.closure` と `CommonRoleOpenClosureAllocation.state_children_closed` はその同じ固定 structural producer の child 閉包。ordinary state の更新で materialize し直した新しい request が、この closure に属する証明はない。`allocate` の既定 slot0 に新 request を流して済ませてはならない。
- `CommonRoleIntervalPaterson.every_where_decreases` は実宣言 check、実 requirement、**同じ binding** で具体化した head と child のサイズ減少。narrowing 後の request がその head と対応すること、source identity/slot から得た binding が同じこと、更新前後の request のサイズ関係はこの定理の結論ではない。
- `CommonRoleOrdinaryKnownness.detect_exists` の完全性は明示的な両向き scalar atom に限定される。一般 ordinary 意味論から得られる knownness の完全性ではない。同じ source 名の型同値を `SourceDescent` で示しても、`detect` がその等式鎖をたどって別 occurrence の既知型を発見することは別問題。
- 今回の `StatefulIndexPath.run` は受け手を実状態から再 materialize するが、停止は入力 `outputs` の長さ。`StatefulPathComplete.checked_exact` は任意の旧状態で成功 iff 生成した制約のモデル存在まで閉じたが、path 自体は入力。`NamedPath` は有限名前列から slot と同一性 atoms を計算するが、child graph を source 宣言から生成したわけではない。
- `OpenPassStability.run_semantically_idempotent` の一回安定は固定 structural reachability の `Good` に対するもの。`StatefulIndexPath.expected_idempotent_models` も固定 outputs の方程式集合についてだけ。どちらも動的 request の再生成・再スケジュールを止める尺度には直接ならない。

### K2 は単なる「入力全部が有限木」という仮定へ置き換えない

spec/06-roles.md K2 の最新決定では、根が無名構造再帰型になったとき、または non-variable head pattern がその constructor を調べる必要があるときに拒否する。変数として捕まえるだけの深い μ と名前付き再帰型は一律拒否しない。候補に危険な照合が一つでもあれば選択・曖昧より拒否が先。したがって「全 source 型が再帰型を含まない」という外部前提を追加して一般 B4 と名乗ることはできない。

K2 は危険な展開を禁止し、Paterson は安全に照合済みの head→where 子を小さくする。**同じ親の状態更新後の再訪**は head→where 子ではないため、これだけで単一 Nat サイズが毎回下がるとは言えない。関連型の右辺は head より大きな型を出力し得るので、ordinary 状態の型サイズ総和の減少も仮定しない。宣言時の finite source と各関連型 occurrence の一回の意味的な確定、実際に発生する where の降下、重複仕事の除去を結び付ける必要がある。

## 2. 提案する三つの橋（いずれも未証明）

### 橋 A: 実 child の source 由来と有限仕事領域

目標名案: `generated_work_closed_and_descending`。

量化子: 任意の有限可視宣言集合 D、実 declaration checker の受理証明 checked、現在確定した source 構文の有限入力 P、実 initial(P) から有限の実ステップ列で到達した状態 C、C で実 producer が生成した任意の仕事 e。

前提:
1. checked は既存の正規化・capture を含む Paterson 検査であり、caller 提供の任意 rank ではない。
2. P は具体的に定義する対応済み source carrier の入力。未対応の T13「関連型右辺から別 associated type 参照」は含めないことを carrier/報告に明記する。全言語の定理を仮装しない。
3. C の到達は実 driver の Step の列であり、任意の oracle が用意した state ではない。

結論:
- e の各 source slot は実 allocator で登録済み、または source 宣言中の親 occurrence と where/associated binding の実位置から新規登録される。同じ source 変数の再出現は独立な新変数にならない。
- e が where child なら、可視 d、実 requirement r、実 capture binding σ、親 provenance が存在し、e の引数は `r.instantiate σ`、親の照合済み引数は head の同じ σ に対応する。K2 が禁止した constructor 観察をしていない場合に既存 checked descent が適用できる。
- **実入力から計算した**有限の仕事識別子領域 U(D,P) を構成し、到達状態の全仕事がその領域に埋め込まれる。U を外部から仮定してはならない。一般 carrier で構成が難しければ、その難しさを未達として止める。

ここで仕事識別子は「現在の atom 配列」や「request の現在の具体型」を無条件に同一視しない。source occurrence + 宣言/子位置 + 正当な再生成 provenance の保持が必要。具体的なデータ表現は実装上の選択だが、どの二つを同一の義務とみなせるかは独立意味論の保存定理を伴わせる。

この橋が最大の穴。既存 closure をそのまま U とする証明は成立していない。まず source から実生成する分岐付き where と associated binding の最小断片で、入力有限 path を廃し、次の橋B/Cまで同時に到達させる。部品Aだけを増やして終えない。

### 橋 B: 新しい事実がない再訪を除去した driver の停止と意味的閉包

目標名案: `saturate_terminates_and_closes`。

量化子: 橋Aと同じ全 D,checked,P、および P の ordinary 制約に対応する任意の旧状態 s。初期状態 `init D P s` は実生成で構成する。

外部前提にしないもの: fuel、Acc、成功、Models、固定点存在、任意の finite universe、外部 Allocation、任意の decrease law。

結論案:
- 実 `saturate D checked P s` は有限回で C を返す（実装の well-founded 再帰で停止を保証し、必要なら全実 step trace の有限性も証明）。
- C は更新から再 materialize して現れるすべての where/associated 仕事について閉じる。未 known の仕事は消さず pending として残す。同じ情報しか生まない仕事は繰り返さない。
- 任意の元 source 評価 v について、C の ordinary 制約を満たすこと iff s の制約と P の独立宣言的義務を満たすこと。内部新 slot がある場合は、その拡張評価の存在を両辺で正しく量化する。
- 兄弟順序の任意の置換で、source 上のモデル集合と最終独立義務が同じ。辞書まで含む観察同値は橋Cで要求する。

尺度案は、橋Aで計算した有限仕事領域の「未記録の事実・未処理の通知」を優先し、新規子を展開する部分には既存 Paterson の well-founded 降下を使う複合尺度。ただし**この案は証明ではない**。有限 U だけでは ordinary 制約の意味変化回数は有限にならない。追加され得る事実の有限性、または各 associated occurrence が同じ確定 receiver で同じ方程式しか出さないことを、実 producer のデータから示す必要がある。単に atom を append し続ける実装では重複で止まらない。

また「同じモデル集合なら停止」とだけ定義すると、既存 detect が atom の表現に依存するため operational knownness とのズレを残す。停止キーの正規化が materialize/candidate/K2 観察を保存する補題を同じ橋内で証明する。solver の一つの任意モデルを receiver として採用してはいけない。

### 橋 C: 安定状態から実外側四方向分類・辞書までの iff

目標名案: `source_resolve_exact`（対象 carrier を名前/docstring に限定表示）。

量化子: 同じ全 D,checked,P,s と、任意の language-visible 結果 r（pending / selected / ambiguous / rejected、および selected の有限辞書）。

結論:

```text
resolve D checked P s = r  ↔  FinalClassify D P s r
```

`FinalClassify` は run/saturate/resolve を呼ばず、source identity、ordinary 制約、独立の knownness・候補適合・K2 危険照合・有限辞書の導出から定義する。成功、安定性、Models、外部 frontier exactness、Acc は iff の外部前提にしない。途中の pending/ambiguous をファイル末の final error と取り違えない。K2 拒否の優先順位は既存仕様どおり。

橋Bの閉包を用いて、再生成後の未処理 child がないことを示してから最終化する。選択された有限辞書の全宣言が呼出側 visible に含まれること、兄弟の置換で言語から見える結果と辞書の意味が同じことを結論に含める。辞書のデータ列が where の並びを記録する場合、単なる構文的等号を強制する前に、既存辞書判断と spec の「辞書の中身」の一致を確認する。

次サイクルの終了ゲートは、この入口を使う X13–X16 の少なくとも一つの実例を PROVED にすること。例の入力条件を狭めて別の例にしたものを元の X の PROVED にしない。

## 3. 最短の実行順と止める条件

1. source carrier と実生成器の対応済み範囲を確認し、入力 path を渡さず **宣言の where と associated binding から**仕事を生成する一つの実入口を選ぶ。橋Aの実 capture 対応を最初に試す。
2. 同じ入口に橋Bの worklist を接続し、状態更新で初めて解ける兄弟を再度解く。新規事実・knownness・重複仕事の三点を trace で検査し、終了を有限入力長だけにすり替えない。
3. 同じ入口で橋Cと適合例を閉じる。できなければ missing premise/キャリアの範囲を報告し、一般 B4 は未達のままにする。

T13 の参照生成、ordinary 意味的 knownness、辞書の観察同値について spec と現存 carrier の間に複数の言語的選択肢が残ると確認した場合は、遅延案を先頭に例つき質問ノートを作り、その意味論を決めずに進められる部分だけ続ける。既知の K2 と兄弟順序独立については再質問しない。
