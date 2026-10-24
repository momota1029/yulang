# 同じ外部 h と再帰 f に対する Int / Bool の二使用

PUBLICATION-TWO-USE-20261024/r1。著者 `/root`。状態: TU1–TU4 は元の独立入力を保つ明記した範囲で独立査読受理。全体命題は OPEN。

## 1. 対象と元の独立入力

元の再帰 body は `f=λx.λy.{first=h x,next=f {a=y}}` のままである。[NR1–NR2](2026-10-24-name-call-recursive-closure-membership.md) の一つの actual f root と全 actual inner closure family の証明を、同じ h の下で Int と Bool の両入力を扱える形へ拡張する。native の二使用に別々の都合のよい h を置く方法は使わない。

用いる checking は [source checking §3.2](2026-10-08-source-generalize-definition-and-proof.md) の同じ decorated value 上の Union injection、Record depth、whole computation inclusion である。U=Int|Bool、A=Record(a:U) を固定する。Union は membership の実 alternative を証拠に保持する。実整数を Bool に変換したり、新しい runtime tag を付けたりしない。

元の independent kernel、raw allocator/transitions、whole carrier/challenge domain、joint world/guards、licensed formation、independent arms、future restriction laws を NR と同じ意味で入力に保つ。独立 primitive inputs に、実 literal 0 の Int certificate、元 immutable builtin true の Bool certificateを含める。これは primitive の原契約であり、新しい f/G の安全性を仮定するものではない。未知の foreign State や独立 arm の law はここから作らない。

## 2. ground data についての有限構成

本節の ground data grammar は Int、Bool、有限 Record、有限 Union とする。新しい F/G の descriptor をこの grammar に入れない。

### 補題 TU1（新しい recursive candidate に依存しないデータ証拠）

ground data X の original membership/formation 証拠は、F/G の declared-value holes を追加する前後で同じ actual value/root/world projections を保つ。Int/Bool の本物の証拠から、同じ値の U 証拠、Record(a:その値) の A 証拠を構成できる。

証明。data の有限構造に帰納する。Primitive case は元の独立証拠。Union introduction は実 branch の証拠を元の injection に入れ、restriction 時もその branch と同じ tuple を運ぶ。Union elimination が必要な場合は各 actual branch に同じ後続関数を適用する。Record は同じ current world の field certificates を元の Record constructor に入れる。latent field を Force しない。いずれも新しい F/G membership の参照を持たない。world の全 background fields は捨てず、NR の relative construction が扱う同じ fields として保持する。従って「ground」は全 world が既に妥当という意味ではなく、追加 holes に関する非依存性である。□

同じ argument code による pure computation inclusion も得られる。例えば actual 0 の Return は TU1 により U へ、actual `{a=0}` の Return は A へ入る。未完了 prefix、元 provider、current world、原 future/latent fields は元 Return/Delay constructor のものをそのまま用いる。int/bool という返却型の名前だけから full carrier checking を推定していない。

## 3. 同じ一つの h の供給

外部 actual callable として `h₀=λz.0` を取る。entry は元 ValueEntry(I_A,z)、I_A の designated endpoint は A、body descriptor は actual `PureReturn(0:Int)`。complete descriptor H₀ は selected Strict の receipt、Force、actual rebind、body、invocation return、全 pending/future を含む。body が pure であることから arbitrary carrier の invocation を pure に置換しない。

### 補題 TU2（共通の genuine h₀）

元の独立入力の下で、この actual closure/root r_h は H₀ の complete membership と hereditary certificate を持つ。

証明。selected Strict introduction を元 raw Lambda に適用する。任意の独立 challenge について actual entry と I_A は同じ interface なので admission はその元入力から得る。receipt/Force の全 prefix は原則通り、Request は `rebind z; return 0; invocation return` の未実行 suffix を残す。Force が actual typed Return を持つ場合だけ fresh z を入れ、literal 0 の独立証拠をその current world に restrict して Return する。z を使わないことを理由に Force を省略しない。Return/future は同じ実 0/provider と元 restriction law。非再帰の一つの closure の導入なので、F/G の membership、candidate の admission、source-image に限定した challenge を使わない。独立 arm clauses は元の full law により満たす。□

これを元 top の actual h-entry Return として渡した後の local suffix を考える。以後 h の binding と provider は常に同じ r_h であり、その membership は完成した imported evidence である。top 自身の未指定の外側 descriptor やその推論成功をこの補題だけで主張しない。

## 4. NR の U への uniform な再構成

元 NR の有限 descriptor graph の I_Int を I_U、A を Record(a:U)、h を H₀、h-result endpoint を Int にする。

```
R_h = ReadInvoke(H₀,D_h,IF_h)
Q_U = Record(first:Int,next:G_U)
R_body = Bind(R_h,u,Bind(ReadInvoke(F_U,D_f,IF_fcall),v,
                       PureReturn(Record(first:u,next:v):Q_U)))
G_U = Strict(I_U,y:U,R_body,IF_g)
F_U = Strict(I_A,x:A,PureReturn(G_U),IF_f)
```

これらは complete descriptors であり、表示された関数の scalar domain/codomain だけではない。元 NF/NG の raw source は変更しない。I_U/I_A の全 compatible carriers と independent challenges を残す。

### 定理 TU3（同じ f と全 inner closures の共同 membership）

TU1/TU2 と元 NR の独立入力から、一つの actual f/root r_f の F_U membership、全 actual allocation gκ/root の G_U membership、および同じ V/W/T/Car family を同時に得る。

証明。単に NR の結論を型名の置換で呼び出さず、その postfixedness witness を次のように構成する。H_U は actual f tuples と各 actual entry/Lambda allocation で生じる gκ tuples の value holes のみ。xκ:A の独立 ground evidence は TU1 から得る。world/carrier/observation/guards は holes にしない。B_HU は同じ positive original Φ の relative background、S_U はその全四成分と実 source phase families の和とする。

* **NF_U。** entry carrier の指定 Return は A。actual Return の同じ value/root/current world を fresh xκ に入れる。body Lambda はその xκ と同じ h/f を捕捉して新しい gκ を返す。gκ は S_U.V の positive edge。entry/pending/receipt/future の証明は NR §4 の同じ raw constructors。Int 固有の elimination はここにない。
* **NG_U の entry。** independently admitted I_U carrier が Return した時だけ yλ:U を導入する。TU1 によりその data evidence は新 F/G membership を前提にしない。Union のどちらの branch でも同じ remainder proof function を使う。old captured x は書き換えない。
* **h Call。** captured xκ:A、同じ r_h/H₀ を用い、Name/Delay と全 inlet checking は元の同じ pure A interface である。GC/ReadInvoke により complete h Call を構成する。h の actual Return は Int、pending は recursive Call と Record の原 suffix を保持する。
* **recursive f Call。** actual yλ:U から TU1 の Record introduction が actual `{a=yλ}`:A を与える。その Delay の全 Force は元 Name/Record/Return 規則で導く。callee prefix は S_U.V(F_U)、receiver observations は NF_U の直接関数から得る。未完成 f membership の eliminator は使わない。actual Return した次の gκ′ はその新しい record を capture する。
* **結果と四成分。** 同じ current world の actual h-result:Int と gκ′:G_U から Q_U の Record/Return を作る。全 world は actual registry と独立 guards と installed S_U fields、全 carriers は上の actual Return/Delay、全 observations は両 Call/Bind の phase constructors。background は non-hole unfold と monotonicity、H_U cases は NF_U/NG_U で置換する。独立 arms は元の law を保持する。これで S_U⊆Φ(S_U) の V/W/T/Car を全て尽くす。

ν最大性により同時に S_U⊆νΦ。h₀ の body がどの U branch も調べず 0 を返すことは TU2 の事実であり、g の外部 carrier を source literals の二 case へ制限していない。□

NR で Int 固有だったのは、ground capture の独立証拠、y の Return endpoint、Record field の checking の三箇所である。TU1 と I_U がこれらを実際に供給し、その他の constructor/independent guards は同じである。static formation は PF の finite license induction をこの同じ finite graph に適用する。primitive packet は genuine Int/Bool と原 Union checking のものを保持し、imported h を local default で再初期化しない。

## 5. 二つの actual use judgments

元 source の Bind/Name/Call rules により次の sequential client を構成する。`Bind` は actual RHS Return を次の monomorphic binding に入れる原 constructor を明示した表記である。

```
Bind(Call(Name f,Delay(Record(a:0))), g_I,
 Bind(Call(Name g_I,Delay(0)), q_I,
  Bind(Call(Name f,Delay(Record(a:true))), g_B,
   Bind(Call(Name g_B,Delay(true)), q_B,
        Return(Record(int_case:q_I,bool_case:q_B))))))
```

各 `g_I`/`g_B` は実返却された inner closure の immutable alias。binding 自体はその actual G_U certificate を保持し、Name は合法 restriction するだけで新 root を作らない。ここで alias に polymorphic family を生成する Generalize を仮定しない。これは選択済み sequential local binding judgment の具体的使用である。

### 定理 TU4（二使用の full source typing）

同じ h₀、同じ f、同じ初期 joint world の下で、この client の全 complete/pending observations を型付けできる。両 completed q fields の型は Q_U。各 first field は actual Int、両 input literals はそれぞれ元 Int/Bool のままである。

証明。最初の Record argument は TU1 により A、次の 0 は U。TU3 で初めて完成した f/G membership を用い、各 Name Call へ GC3 の full ReadInvoke introduction を適用する。f の actual Return があった時だけ fresh g_I alias を入れ、その actual closure を次の Name が読む。g_I が Return した時だけ q_I を入れる。同じ current world へ元 f/h の hereditary certificate を restrict して Bool側の二 Call を構成する。true の原証拠は Bool→U、Record(a:true) は A へ TU1 で入る。g_B は f の別 actual allocation であり、g_I の x を書き換えない。

途中が Request の場合は元 Bind law により残りをその actual handle の suspended suffix とする。後半の証拠は admitted response/current-world を引数とする同じ関数であり、前半が Return したことを無条件に置かない。最後は同じ world の q_I,q_B を Record に入れる。latent next closures は Force しない。各 nested g の body は TU3 により h/recursive f/Record の元順序を保持する。したがって全 observations、provider/current world、receipts、future を一つの joint derivation で得る。□

各 actual q.first については original Record elimination がその同じ Int certificate を返す。元 `succ:Int→Int` の genuine complete contract が与えられれば、その same-value projection を Name alias に束縛して succ Call を追加できる。これも元 complete Call law と primitive premise の局所適用であり、first の Int 型から succ の未指定 effects/arms を消さない。

## 6. 公開後 native 比較との接点と残項

この source 証明が示すのは、Int/Bool の両 input が **同じ h/f/world** の下で両立するという事実である。g_I の source 型を `Int→…`、g_B を `Bool→…` に等式固定する必要はない。両方を受け取れる一つの U inlet で元の原契約を満たせる。

native counterpart の二 App chains はそれぞれ argument comparison を生成する。その向きは Int≤Y_I と Bool≤Y_B であり、同じ source の入力をそれらの逆向きの制約と同一視しない。shared T に両 lower を許せるかどうかは、別稿の全 store/client closure と quotient transport で証明する。

本稿の monomorphic Bind aliases と、別稿の native nested-App syntax の間の全 inference/freshening 対応は主張しない。普通の surface `let` が行う Generalize は別の元規則であり、ここで任意に無効化したわけではない。また computed callee へ Name-only ReadInvoke を適用するための無証明の ANF 等価性も使わない。TU4 は明示した原 source constructor client の定理であり、native client 構文をそのまま完成した Yulang certificate とする橋はなお別途必要である。

従って二使用に共通の source witness と native の具体的 coverage 結果を個別に供給できるが、一般化された全 source contexts、actual T/Y occurrence の receiving/SCC qualification、元の全 A/B・principality・combined termination を閉じたとはしない。

## 7. 入力と作業記録

直接契約は [PUBLICATION-TWO-USE](../../tasks/agent-loop/sprints/publication-two-use-20261024.md)、SHA-256 `bbe1f0a66acc592b67bb5050fd5d1e1977a83b99140f26b14c2c4274fbe75aed`。直接引用した source checking の Union/Record/Bind/Function clauses、NR 全四成分、PF finite license proof、GC ReadInvoke を frozen inputs で固定する。数学的 constructor induction と静的読取りのみ。実装変更・test/build/compiler run はない。独立査読は outcome に記録する。

独立査読入力 SHA-256 `873f5f769d9ec89a8c0d8ef8af422151758d5c579820bb8c4b3982babf5e3923`。査読後は status/receipt のみ更新。[outcome](../../tasks/agent-loop/sprints/publication-two-use-20261024-outcome.md) に受理範囲を固定する。
