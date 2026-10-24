# 相関を持つ局所関数の、修正核における具体的な型導出

Revision CHC1。著者 `/root`。独立査読前。対象は既存 discriminator の source 形を保つ**候補核の導出**である。元の CompleteMem/KV・Source-Generalize との橋渡し、実推論器の受理・拒否、元の主型性への反例はこの稿の結論ではない。

## 1. 固定 source と構成する型

元の参照 source を変更しない。

```text
let rec f = lambda x.
  let g = lambda y. (lambda z. y) (f y)
  in {a = succ (g 0), b = g true}
in f
```

`U=Int∨Bool`、`V={a:Int,b:Bool}` と置く。核の値型は C(A,B)、argument carrier は UA とする。ここで先頭の U は既定の delay 型 constructor でも使われるため、以下では carrier を `DelayType(A)` と綴り、上の union 型 U と区別する。

同じ f を `C(U,V)` として一つの再帰環境へ登録する。局所 g に求める scheme は

```text
∀A. (q : A ⇒ U) ⊢ C(A,A)
```

である。q は既存の直接境界を生成する有限 evidence の formal で、勝手な暗黙 subsumption ではない。evidence の解釈は型 A の値から U 型の計算を作る。q が効果を持つ場合はその計算を保持する。この表示だけから g の精密効果を空とはしない。

この scheme が native inference から得られることを先に仮定せず、以下で明示的な型・evidence abstraction の導出を構成する。Int と Bool の二使用には、それぞれ実際の左・右 union injection の直接証拠 qI,qB を用いる。

## 2. g の全 body と二使用

`λv` は Value entry の lambda、`Wrap(f,a,r)` は同じ callable に直接 argument/result adapter を付ける既存の構成とする。`IdV` は V の恒等直接証拠。型 A と q を固定し、f:C(U,V), y:A の下で次を作る。

```text
M_A(q,y) = Call(Wrap(f,q,IdV), Delay(Ret y))
W_A(y)   = λv z:V. Ret y
Body_A(q,y) = Call(W_A(y), Delay(M_A(q,y)))
G_A(q)   = λv y:A. Body_A(q,y)
```

**補題 CH1。** この環境で M_A:V、W_A:C(V,A)、Body_A:A、G_A:C(A,A) の有限型導出が存在する。

**証明。** q と IdV から Wrap(f,q,IdV):C(A,V)。Ret y:A から Delay(Ret y):DelayType(A)、Call 規則で M_A:V。z:V の下でも y:A なので lambda 導入で W_A:C(V,A)。M_A の delay とこの callable に Call 規則を使えば Body_A:A。最後に y の lambda 導入で G_A:C(A,A)。各子へ同じ A,q を使う。元 source の `f y` と、その結果を引数に渡す wrapper の **二つの Call** はどちらも残る。□

g の実 closure 環境の自由変数は f だけで、その型 C(U,V) に A は自由に現れない。q は evidence abstraction の formal、y は Value lambda の formal である。従って A/q をこの順序とスコープを保って抽象化できる。q の code を source Function と取り違えず、D の template/evidence application と同じ行政的構成を使う。

**補題 CH2。** 同じ g と f の下で、`g[Int,qI]` は C(Int,Int)、`g[Bool,qB]` は C(Bool,Bool)。f の graph reference、U、V は両使用で固定される。

**証明。** 有限型・evidence abstraction の除去を二回独立に適用する。qI は Int 値を U の左 injection、qB は Bool 値を右 injection にする型導出である。CH1 の同時代入によりそれぞれの導出を得る。一般化されたのは A/q のみで、閉包の自由 f は同じ reference のまま。型代入は新しい source receipt や f の初期化を発生させない。□

これは二つの異なる f を構成する方法ではない。実 Call の activation/receiver が fresh になりうることと、再帰 closure の identity が一つであることは両立する。

## 3. f の guarded graph を実際に組む

succ は固定参照 source の Int→Int primitive wrapper とする。候補核では `λv n:Int. Prim(IntAdd,n,1)` として同じ値型を構成できる。0:Int と true:Bool は既定の literal constructor である。

f の body を、上の g の非拡張な abstraction を局所 binding し、次の二 field を source 順に構成する計算とする。

```text
a = App(succ, App(g[Int,qI], 0))
b = App(g[Bool,qB], true)
```

ここで App は元 source の完全 Call の展開であり、内側 App の結果を未評価のまま消去しない。

**定理 CH3（同時再帰型導出）。** fresh reference rf:C(U,V) を一つ割り当て、その RHS を `λv x:U. Body_f` とする guarded graph と `Ret rf:C(U,V)` の有限型導出を構成できる。

**証明。** CH2 と二つの literal から inner App の型は Int、Bool。succ の型と第一 App から field a:Int、第二から field b:Bool。ordered record の規則で Body_f:V。g の local abstraction は f にのみ依存し、A を含まない環境の下で CH2 の一般化条件を満たす。x を導入して RHS:C(U,V)。同じ再帰環境 rf:C(U,V) でこの RHS を検査し、全 f 参照を rf に置換する。新たな参照 cycle は RHS の lambda guard を通り、alias-only cycle はない。V1(d) の graph 拡張を適用し、最後の reference/Ret 規則で結論を得る。f の実行が停止することを前提にしない。□

## 4. 完全 Call、pending suffix、効果

**補題 CH4（実際に残る continuation）。** G_A の Value entry が y を受け取った後、Body_A はまず W_A の Call に入り、その Value entry が carrier 内の M_A を force する。M_A は同じ f の Call であり、その途中の request が外へ出れば、typed continuation は少なくとも f の残り suffix と W_A の argument force/body の suffix を順序どおり保持する。

**証明。** W_A は lambda 値なので callee 評価は Ret。Value entry は指定された Delay(M_A) を受領し force する。M_A の Wrap は y の delay に q を内側で適用して同じ f の entry へ渡す。f の正常結果 V は IdV を通って W_A の formal z:V に入り、そこから Ret y:A になる。途中の各 request は V4 の bind/scope/View 等の七 frame 切出しでこの残りを K に保持する。q 自身の request も同じ規則による。外部応答後の再開は保存した計画を使い、完了済みの entry を初めから再実行しない。□

型付きなのはこの保存計画の全体であり、`f y` が発散すると推測して body を `Ret y` に置換したものではない。反復 resume にも V6 を適用できる。

**補題 CH5（event 発生源の被覆）。** CH3 の初期 `Ret rf` は body を実行しない。実際の f 呼出しでは、引数 carrier が持つ computation の event は完全 Call の規則に残る。その force が正常終了した後、この閉じた body が内部で使う qI/qB、literal、record、lambda、IntAdd は request を新規発行する constructor を含まない。

**証明。** CH3 の最外は guarded lambda allocation と Ret。呼出しの Value entry は x を force するので、引数 computation の event を無視できない。以後の構文を列挙すると、perform/host invocation はなく、qI/qB は injection のみ。再帰呼出しが f を再使用しても同じ有限 body 集合に戻り、内部から渡す carrier は Ret y または記載された有限 body である。各有限 prefix の長さに帰納すれば、既存 request の輸送・再開を除く新たな request はこれらの body から生じない。metadata の保護・receiver・route の生成は effect の発行そのものではない。□

従って「全ての incoming carrier が pure」という仮定をこの callable の全型へ黙って追加しない。一般の入力 carrier の効果と、内部に固有の event 発生源がないことを分ける。精密な Φ の生成・証明書は G/I の元の検査条件に従う。

## 5. 元の推論問題への正確な意味

CH1–CH5 は、この source 形について、g の二使用、同じ再帰 f、捨てられる結果、完全 Call と継続を持つ **明示的な候補核の型導出**を与える。この点では単に自由な B0=Int、B1=Bool を選んだ scalar assignment より強い。

ただし、元の侵入保存定理は独立の source member・world・CompleteMem/KV・Source-Generalize の意味を持つ。今回の核の型導出をそこへ写すには、同じ recursive raw closure と world、全ての challenge/future conjunct、active f を捕捉する g の publication を保つ構成が必要である。その橋渡しは別稿 [original member の構成](2026-10-24-correlated-helper-original-member.md)の対象である。

この橋渡しなしに、既存の native shared-C/int-bool failure と CH3 を並べて「元の Yulang の主型性を反証した」とは結論しない。また、C に別の source binder を発明したり、元の使用 map を都合よく変更したりしない。

依存は [sprint 契約](../../tasks/agent-loop/sprints/original-member-bridge-20261024.md)に固定した V/G/I と元の source/native discriminator。D の固定 hash は `47b7fcec1f501e7c326ab9859885e329aab2730066806ea79212e825ebb32b0b`。source や compiler の変更、tests/builds/実行なし。紙上の有限型導出と frame の場合分けのみ。
