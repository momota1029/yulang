# bound のレベル閉包、一般化、等置と有限使用の可換性

SOURCE-INDEXED-DERIVATION-20261024/r1。著者 primary。独立査読は NL1–NL7 と EC3 への適用を、明記した前提と範囲で受理した。凍結 hash と判定は sprint outcome に記録する。
[契約](../../tasks/agent-loop/sprints/source-indexed-derivation-20261024.md)で元の A/B と入力を固定する。

本稿は原 `Typer.scala` の native Function/Record/Primitive/Variable の
全有限生成履歴を扱う。前稿 EC3 の具体的 store で確認していた
「固定 anchor の下に高い未複写依存がない」を、実 constructor の
不変条件から導く。intrusion を含む source 全体の主型性と同一視しない。
最後に、等置後の有限 store から判定できる条件の下で、任意有限個の
fresh use との可換図式を構成する。

## 1. 状態、辺、レベル

型項は有限の Function/Record/Primitive 木と変数参照からなる。
再帰型は変数の有限 bound graph によって表し、無限木を構成しない。
変数 a の不変 native level を λ(a)、構造項 t の level を ℓ(t) とする。
ℓ はその変数葉の λ と0の最大値。これは native の実定義であり、
source Value の birth と異なる。Σ は各変数の二つの有限 bound list を持つ。

不変条件を

```
L(Σ) : ∀a. ∀t∈Σ.lower(a)∪Σ.upper(a). ℓ(t)≤λ(a)
```

とする。`a↝b` は a のいずれかの bound の有限構造木に b が現れること。
同じ変数・同じ bound の複数 occurrence と list の順序は実状態に残す。
以下の到達性だけはその有限支持グラフを使う。

## 2. 実操作での保存

**NL1（native bound-level invariant）。** L を満たす有限初期 store から、
通常の native allocation、constrain、extrude、および caller level j が
scheme boundary b 以上の freshenAbove を実行する全有限履歴で L が保たれる。
ここでは representative merge や可変 level 低下を操作に追加していない。
失敗・非停止を含む処理の任意の有限実行 prefix にも同じ保存が成り立つ。

証明。実際に bound を書き換える箇所を全て調べる。

1. freshVar は指定 level と空の二 list を作る。
2. constrain の identity/cache return は書き換えない。Function の反変引数と
   共変結果、Record の実際に一致した field は子比較を呼ぶだけである。
   mismatch も bound を書き換えない。
3. lhs-variable branch は guard `ℓ(rhs)≤λ(lhs)` を検査してから rhs を
   upper に入れる。rhs-variable branch は逆側の同じ guard によって lower
   に入れる。続く反対側 replay の一つ一つにも同じ議論を適用する。
   comparison request の発生と cache miss による実 branch は区別する。
4. wrong-level branch は extrude の結果を使って新たな constrain を呼ぶ。
   extrude(t,ε,k) の返却項は level≤k。構造子では子の同じ上界を使い、
   Function argument では極性だけを反転する。許容 level の項はそのまま。
   高い a の memo miss は level k の c を空 list で作り、先に memo に入れる。
   parent へ挿入する link は c なので k<λ(a) を満たす。c の選択側へ
   インストールする各項は、同じ target k での再帰結果なので level≤k。
   memo hit は既に level k で登録した c を返す。途中で反対極性が新しい
   parent link を選択 list に加えても、その link の level は k である。
   返却上界と全書込みの保存を、この memo の型不変条件と同時に示せる。
5. freshenAbove(b,t) は level≤b の項をそのまま返す。高い変数を level j
   の空行へ写し、bounds より先に memo に登録する。再帰結果の各変数葉は
   旧 level≤b の固定葉または新 level j の葉である。b≤j から全返却項の
   level≤j が従い、新行の二 bound list への書込みも L を満たす。
   元の行は書き換えない。

これで全 write site を尽くした。有限実行 step ごとの帰納で主張を得る。
extrude/freshen の登録済み memo は cyclic bound を展開しない。
一回の処理の有限性は有限元 graph と memo から得るが、この保存帰納は
後続の全 inference が停止することを仮定しない。□

**NL2（低い anchor の依存閉包）。** L(Σ) なら a↝b に対して
λ(b)≤λ(a)。従って任意の有限 bound path の level は非増加であり、
λ(a)≤b の anchor から到達する全変数は level≤b である。

証明。λ(b)≤ℓ(t)≤λ(a) を各辺に適用し、道の長さで帰納する。
cycle も同じ有限道の議論で扱う。□

この結論は単なる数値レベルの期待ではない。extrude が選択 bound を
target へ写し、constrain が guard を検査するために成立する。
低い anchor の下に高い依存を隠すことは、L を保つ実操作では起こらない。

## 3. lexical caller の条件と全型項の上界

context を現在 level j で良形と呼ぶ条件は、monomorphic binding の型の
level が j 以下、各 polymorphic binding の boundary が j 以下であること。
scheme の body 自体の level は j 以下でなくてもよい。

**NL3（native source construction）。** 原 builtin context と level0 は
この条件を満たす。良形 context からの typeTerm が返す型は level≤j。
typeTerm/typeLetRhs が実際に呼ぶ全 freshenAbove は boundary≤caller level
を満たす。成功した有限 source 導出について、同じ条件が全子環境に保たれる。

証明。Var の monotype は条件そのもの。scheme は実 instantiate を使い、
NL1 の freshen 返却上界によって level≤j になる。Lambda は j の formal を
追加し、body の帰納結果と Function を作る。App/Sel の新 result は j。
literal は0、Record は子結果の最大値。Let RHS は j+1 で検査するため
既存 context はなお良形。再帰 placeholder も j+1。RHS の scheme は
boundary j を持ち、body は元の j でその scheme を読む。nested scope は
その後 level を増やすだけなので、その scheme の実 lexical use は全て
boundary 以上となる。元の builtins は ground monotype と boundary0 の
if scheme なので初期条件を満たす。各部分で constrain が成功したことは
level 上界を変えない。これは source 構文上の有限帰納である。□

外部 API に caller より高い boundary の arbitrary context を渡す場合は
この命題の前提を満たさない。元の lexical source の領域を狭めた例外ではない。
また NL3 は元 Scala の構文についての結論であり、完全 Yulang Call の
carrier/receipt/effect 判断を生成したという主張ではない。

## 4. 一回の freshening を graph 上で完全に記述する

有限 L-store Σ、公開 root r、boundary b、caller j≥b を固定する。
R は r の変数葉から全 bound 辺を辿って得る変数集合。
`F={a∈R | λ(a)≤b}`、`H={a∈R | λ(a)>b}` とする。
freshenAbove の写像 θ_i は F では恒等、H では一回の使用 i に固有の a_i。
各 a_i の level は j、bounds は θ_i を元の bounds 全体に同時適用したもの。

**NL4（実 freshening の固定部分と複写部分）。** 実 native freshenAbove は
正確に H の各変数につき一つの clone を生成し、F を共有する。
返却 root は θ_i(r)。複写される二 bound list は上の構成と一致し、
一回の traversal は有限である。m 回の使用では各 H_i は互いに fresh、
全使用が同じ F を共有する。m は任意の有限自然数でよい。

証明。native は低い項で traversal を止める。しかし NL2 によりその下には
H が存在しないため、高い変数を見落とさない。逆に H の任意の変数への
到達道は低い変数を経由できず、その道は実 traversal により辿られる。
高い変数を初めて訪問した時に memo を作り、再訪は同じ clone を返す。
従ってちょうど H 個の行を生成する。構造木と両 bound list は実コードの
同じ field/list 順序で写す。有限 R、有限 list、有限構造木と memo により
終了する。別使用は別 memo を作るため clone を共有せず、低い元行を保持する。
使用数に関する帰納で m の主張を得る。□

これは「固定 anchor の下の高い依存を別途仮定する」という残余を、
普通の native 生成について NL1–NL2 で取り除いた結果である。
copy 生成が source Value や birth を新設するとは主張しない。

## 5. 等置後の条件を曖昧にしない

有限全変数上の同値関係から quotient q を作る。各 class c の level は
`λ_q(c)=min{λ(a)|q(a)=c}`。qΣ は各 member の全 lower/upper clause を
同じ極性のまま q で写して合併した store である。旧 clause は落とさない。

**NL5（等置後の閉包の有限判定）。** L(qΣ) は次と同値である。

```
∀a. ∀t∈boundsΣ(a). ∀d∈Var(t).
    λ_q(q(d)) ≤ λ_q(q(a)).
```

証明。qΣ の全 clause はちょうど q(t)、その level は q(d) の level と0の
最大値である。元の level は非負なので、変数葉のない場合も同値が成立する。
有限 graph の各 bound の葉を走査すれば判定できる。□

最小 level を選ぶだけでこの条件が自動成立するわけではない。実 native
で到達可能な小さい状態から、失敗する quotient を示せる。

1. a,b を level2 の空行として作る。
2. `extrude(Record(f:a),+,1)` により c:level1 と a≤c を作る。
3. `constrain(Record(g:b),a)` は a.lower に Record(g:b) を置き、c へ
   replay する。positive extrusion が d:level1、b≤d を作り、c.lower に
   Record(g:d) を置く。全 row/list は L を満たす。
4. q は a と c だけを class c* にし、level1 とする。すると c*.lower に
   元 a の Record(g:b) が残り、b は level2 のままなので L(qΣ) は偽。

ここには actual parent/copy a/c がある。しかし source occurrence の
origin/receiver/SCC は与えていない。従って現行 intrusion の反例ではない。
「任意の親子等置後にも NL2 を無条件に使える」という証明手順の反例である。
他の pair b/d の等置を自動追加して修復したことにもできない。
intrusion の owning proof は、全旧制約を保つ実操作について NL5 を満たすか、
L に依存しない別の publication 対応を構成する必要がある。

## 6. quotient と任意有限個の使用の可換図式

以下は有限に検査できる二条件を明記した一般定理である。

- L(Σ) と L(qΣ) が成立する。
- 上の root-reachable 集合 R は q-class について飽和している：
  `q⁻¹(q(R))=R`。公開 root から到達しなかった member の bound を quotient
  によって公開部分へ持ち込まないための条件である。

qΣ の公開 root は q(r)、boundary は元の b。全 use の caller j_i は b 以上。
元 store に m 個の実 fresh use を加えた全 clause 集合を Pub_m(Σ,r,b) と書く。
元 store はその全体を保持し、各使用は NL4 の reachable clones を追加する。
ここで比較するのは constraint 集合であり、list 順序・重複・event identity の
等式ではない。

**NL6（有限公開の quotient 対応）。** 次の全域写像 q_m が構成できる。

```
元の base row a : q_m(a)=q(a)
使用 i の clone a_i :
  q_m(a_i)=q(a)            if λ_q(q(a))≤b
  q_m(a_i)=q(a)_i          if λ_q(q(a))>b
```

この写像は各 published root を対応する qΣ の実使用 root へ送り、

```
q_m(Pub_m(Σ,r,b)) = Pub_m(qΣ,q(r),b)
```

を clause 集合として満たす。

証明。まず qΣ の reachable 集合は q(R) である。左から右の到達性は
元の各 path を q で写せばよい。逆向きには、q(R) にある class の全 member
が飽和条件で R に属し、その各 bound の葉も R に属する。従って q(R) は
quotient の全辺で閉じており、追加 reachable class はない。

q-class c が高い場合、その全 member a は高い。R にある全 member は
NL4 により各使用で clone される。c_i の全 bound は、元 member の bound
の q 像を全て集めたものなので、q_m による a_i の全 bound の像と一致する。
任意の variable leaf で `q_m(θ_i(t))=θ'_i(q(t))` を確認できる：
元で低い葉の q 像はなお低く固定され、元で高い葉は表示した二場合になる。

c が低い場合、q_m はそこへ送る全 a_i を base の c に送る。
L(qΣ) により、その bound の全葉の q 像も低い。このため cloned clause の
像は base qΣ に既に存在する同じ clause であり、未定義の高い clone を
固定 anchor の下へ入れない。元 base の clause は qΣ の全 clause に全射。
以上により両包含が成立する。root の構造木にも同じ葉の等式を適用する。
使用ごとの fresh identity は異なるので、この証明を m 個について同時に
行ってよい。m=0 も同じ base の等式となる。□

飽和条件は省けない。例えば高い空行 a を root とし、到達しない高い x の
bound に別の高い y がある場合、a=x とすると quotient の公開 root は y に
届く。元 a の freshening には y_i がない。L だけではこの新しい依存の
出現を防がない。ここでも新しい source 制限を設けるのではなく、上の図式に
必要な正確な native 条件を明記している。

**NL7（有限 client の解の引き戻し）。** NL6 の前提の下で、m 個の公開 root と
q が固定する外部座標 E に対する任意の有限 native client constraint K を
取る。quotient 側の Pub_m と K の解 η があれば、`ρ=η∘q_m` は元側の
Pub_m と同じ公開 root から作った K の解である。

証明。Function/Record/Primitive 型項の解釈は変数への同時代入と可換。
NL6 が全 native clause を写し、公開 root と E も一致させるため、各 clause
の成立を η から引き戻せる。cycle は変数 valuation の同時代入で扱う。
元 store の全変数を q_m の定義域に残しているので、未到達座標の解の拡張を
黙って仮定しない。□

NL7 の逆向きは主張しない。別 use の独立な witness を一つの低い class
へ同一化できるとは限らない。interleaved constraint solving、新しい let
一般化、完全 source Call/effect/world を含む client はこの native 命題から
自動的に得られない。

## 7. 元の義務への適用

[EC3 の store](2026-10-24-replay-extrusion-commutation.md)の
q は B/T を t:level1 にする。NL1 は等置直前の L を与える。
変わる B の bound は B≤T だけで t≤t となり、B を含む他行の bound は
葉の level が下がる。元 T の bound は空。従って NL5 の全条件が成立する。
この等置 class の B,T はどちらも root o から到達するため R も飽和している。
他 class は singleton である。NL6–NL7 は EC3–EC4 の任意有限使用についての
結論を再導出し、その特定の行一覧に依存していた理由を一般の条件へ分解する。

before/after は次の通り。

| 元の publication 義務 | 今回得た証拠 | 残る元の責務 |
| --- | --- | --- |
| 固定行の下の高い依存を残さない | NL1–NL4：全 ordinary native 有限履歴から実 freshening partition を導出 | intrusion 後には NL5 等の実対応が必要 |
| 商と複数使用の整合性 | NL5–NL6：有限 graph 条件から任意有限 m の全 clause 対応を構成、EC3 へ実適用 | 全 qualifying source event が条件を満たすか、条件不要の別対応 |
| 全域 valuation の扱い | NL7：base の全変数を含む明示的 pullback | scope を守った逆向き joint strategy、元の required coverage/principality |

source-indexed proof lane には、scalar constraint の level と source interface
の full typed checking を混同しないという境界を返す。source の Application
生成は VIncl/WholeArgCompatible 等の**義務を発行**する。
`source-call-generation-construction` §5 はそれらを独立な decorated semantic
propositions とし、supplied decoration を source generation の結論としない。
従って NL1–NL7 は RG-OWNER や完全 semantic checking の代わりにならない。

本稿は元の whole theorem を縮小せず OPEN とする。今回減らしたのは、
native publication における fixed-anchor 依存閉包と clone partition の
未構成部分である。一般 source-scoped joint lifting、全 Call、効果、共起、
surface 全体、combined inference 停止の残りを閉じたとは報告しない。

## 8. 固定入力と検査

直接根拠は契約に固定した原 `Typer.scala`、元 intrusion source-preservation、
Source-Generalize と EC 稿。reference の constrain/extrude/freshenAbove/型 level
定義の全 write site を静的に照合した。実装、tests、build、compiler、probe は
実行していない。これは文書内の数学的構成であり、機械検証済みの証明ではない。
独立査読の固定 hash と判定は sprint outcome に記録する。
