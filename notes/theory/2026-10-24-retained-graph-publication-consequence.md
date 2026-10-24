# 保持したグラフからの資格判定と公開への適用

RETAINED-GRAPH-REPLAY-20261024/r1。著者 primary。ユーザーの指摘「そこはグラフを持ってきてSCCとりだすしかないですよ」を受け、前稿の「所属が未証明」という表現を具体的な graph query に戻す。凍結 r1 は独立査読で記載した条件付き範囲に BLOCKING/MAJOR 指摘なし。査読後の変更はこの状態行と別稿 hash の状態注記のみ。実装変更は行わない。

## 1. 判定に使うグラフと保持記録

対象 source と全 scalar store は[前稿](2026-10-24-birth-level-publication-replay.md)に固定したものを使う。G=(V,Ref) は実 source Value の参照グラフ、b は不変の生成レベルであり、G_k=G[b⁻¹(k)] の SCC 写像を C_k とする。型 bounds や replay の依存辺を Ref に加えない。

保持したデータには、次の別々の接続がある。

1. source checking handle a に対する Value の対 A(a)=(origin,receiver)。
2. extrusion occurrence e が実際に生成した polar pair list P(e)。
3. source association を、その生成・再利用 occurrence に結び付けた記録 I(e,a)。

**RG1（資格の有限計算）。** 有限で正確な G,b,A,I,P を保持すれば、発行すべき親子等置は次の集合として一意に計算できる。

```text
Q(a) ⇔ A(a)=(u,v), b(u)=b(v)=k, C_k(u)=C_k(v)
Eq   = {(copy,parent) | ∃e,a. I(e,a) ∧ Q(a)
                          ∧ (copy,parent,polarity,target) ∈ P(e)}.
```

証明。各誘導グラフの SCC を計算し、各保持 association の両端の成分を比較する。真となった記録について実 P(e) を列挙し、同じ pair の重複を除く。採用規則で資格を持つ実 occurrence の全 pair は必ず列挙される。列挙された pair は、その occurrence の保持 pair であり、資格の比較も成立する。従って過不足がない。e が一つの association だけを持つ通常の表示もこの式に含まれる。共有 group の再利用は別 e として記録し、元の P を参照できる。これは表現上の共有であり、任意の seed と pair を新たに対応付ける規則ではない。□

この I は元規則の実 occurrence 記録を関係として記しただけで、新しい選択方針ではない。与えられた全記録からの SCC 判定に、追加のユーザー判断は要らない。

## 2. 実装の query は既に定まっている

凍結 `candidate_intrusion.rs` は Parent に `(copy,parent,polarity,target,sources,comparison,occurrence)` を保持する。PairGroup は実 parent list の区間、Reuse は別 occurrence と元 group、新しい sources を保持する。`by_output` は実 comparison と実 transformed output の組から group を引く。

この実装記録の I_code は、original では `a ∈ source_events(Parent.sources)`、reuse では `a ∈ source_events(Reuse.sources)` として定義されている。consumer の `any(qualifies)` は、まさに RG1 の存在判定である。従って **実装記録に対する判定が曖昧なわけではない**。元の graph に birth filter を適切に加えた場合の query も、この式で計算できる。現コードに birth field が実装済みという主張はしない。

一方 I_code が source 規則の実 occurrence 接続を全経路で表すことは、source/native 対応の定理である。RG1 の計算からその定理を逆算しない。前稿の未証明箇所はこの対応に属し、SCC を選ぶ新たな意味論判断ではない。

## 3. 伝播のグラフも実際に保持されている

`candidate_context.rs` の `Dependency::Replay` は child だけでなく lower/upper の順序、両親 RelationId、両 BoundKey を保持する。Derived、FunctionPort、Transport も親子を保持する。`BoundAdmissionCause::ExtrusionLink { processing }` は、当該近似リンクを生成した processing RelationId を保持し、BoundEmission は物理的に追加した bound slot と admission を接続する。

従って source set の集合和だけを見て「経路が失われた」と結論するのは誤りである。Parent.comparison 単独は TypedPairKey であって RelationId ではないが、fresh pair 自身のリンクとその emission/admission まで取り出せる。

**RG2（固定した fresh cut での遡及）。** 前稿の fresh T₁ が作られた直後、quotient・rollback・fresh-use transport 前の cut を取る。実 B₂≤T₁ リンクの一意な作成 admission を辿れば、その `ExtrusionLink.processing` から実比較 `Record(B₂)≤C₁` の RelationId を得られる。さらにその Replay.upper_input の R₂≤C₁ リンクの作成 admission を辿れば、元 h-call の comparison に戻れる。

証明。T はこの固定履歴で新たに割り当てられ、作成時の正極性リンクは B≤T の一つである。元の physical emission と、その直前の ExtrusionLink admission は同じ bound を保持する。processing はそのリンクの作成中に実際に処理した relation である。後の replay は lower/upper 入力を区別するので、上側に採用された R≤C を追える。このリンクは元の h-call extrusion が作成した正極性リンクであり、その admission が元 comparison を保持する。ID や現在 level からの推測は不要である。□

この fixed-cut 証明を、複数 admission、quotient 後、rollback 後、freshening 後に無条件で拡張しない。それらでは対応 snapshot と実 reuse group の記録を使う必要がある。元 h-call へ遡及できることと、全 replay ancestry の source handle が新コピーを所有することも同じ命題ではない。

## 4. グラフの結果を公開へ戻す

[graph extraction 稿](2026-10-24-retained-value-graph-replay-attribution.md)、査読対象 SHA-256 `37d4a398f9c867d0b3996495ad34dcd590596ae23b8aed3c61c21073f72de16f`（統合版は査読状態行のみ更新）の RG1/RG2 を本節に適用する。前稿 PR1–PR3 の数学は変更しない。

- 実 source graph における F/F の資格は reflexivity で真である。
- 同稿の隣接表では全成分が singleton であり、F/H と F/L_wrapper は別 SCC なので、両 association の資格は偽である。low target の数値だけで H を復元する必要はなく、RG2 の実経路を用いる。
- この具体的比較の I_code が F/F を含む場合、RG1 の実装 query は T=B を選ぶ。そこへ h-call への遡及経路を併記しても、現在の `any` query の計算結果は変わらない。
- source occurrence が RG2 の境界に対応すると別途導出できれば、その境界の資格と PR1–PR2 を適用する。全 ancestor を所有者とする I_code が正しいと導出できれば、その資格と、公開前消費を前提に PR3 を適用する。結果を有利にする方の対応を任意に選ばない。

ここで新たに構成したのは、保持された source graph・SCC・実 pair/リンク/伝播 graph からの判定と遡及である。グラフの取り出しと component 計算を未完扱いする表現を改める。全 source 導出からこの固定比較が生成されること、全 occurrence の source/native 対応、publication の実消費時点、元の A/B・健全性・停止は、それぞれの元の範囲を保つ。

実抽出はさらに、現 Rust owner walk が FieldTail の receiver を訪問しないことを示した。元の definition-root 規則で必要な P→F と、true が resolved Name なら P→T_bool の辺が、その表示では欠ける。数学的 source graph には必要な辺を含めて上の SCC を計算する。現実装では全 Value の birth も保持されていない。いずれも実装対応の問題であり、この具体例の singleton 証明を妨げず、ユーザーの算法を変更する理由にもならない。

直接入力19件は [契約](../../tasks/agent-loop/sprints/retained-graph-replay-20261024.md)に固定する。凍結稿の適用結果と独立査読は [outcome](../../tasks/agent-loop/sprints/retained-graph-replay-20261024-outcome.md)に記録する。コード・テスト変更、tests/build/probe 実行はない。
