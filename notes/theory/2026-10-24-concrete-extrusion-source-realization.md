# 実 Record-field extrusion の source checking realization

ACTUAL-COPY-HISTORY-20261024/r1。著者 primary。独立査読前。

本稿は [AR1/AR2](2026-10-24-actual-replay-receiving-diagram.md) の actual event family と、同稿 §4 の実 fresh pair `T/Y` を用い、空欄だった **この一回の extrusion の local whole checking** を構成する。source frame 内の receiving incidence と、別に保持する native occurrence association を同じ sort にしてしまわない。

## 1. 固定入力と exact native event

元 source は変更しない。

```text
let top = lambda h.
  let rec f = lambda x. lambda y.
    {first=h x, next=f {a=y}}
  in f
in top
```

[NR](2026-10-24-name-call-recursive-closure-membership.md) と AR の受理済み monomorphic instance を使う。I=Int、A=Record(a:I)、genuine h:H* の designated argument value view は A。独立 challenge/arm/admission/kernel premises は元通り。全 actual entry/response/future histories は AR の同じ dependent family で量化し、source computation を一つの成功 trace に制限しない。

native 側は、元 empty-start derivation の次の有限部分である。C は先行 h-demand の B の正コピー、D は J の負コピーであり、ここでは新しく作らない。

```text
u : B₂ ≤ C₁                         h-demand の実 positive link
v : Record(a:Y₂) ≤ B₂               f completion の実 argument replay
p : Record(a:Y₂) ≤ C₁               Replay(lower=v,upper=u)
z : ExtrudeFresh(p,field a,Y,+,1)    新 memo M_p の miss
    M_p(Y,+)=T₁
    Y.upper に T を追加
    T.lower = map(extrude,+,1,Y.lower) = empty
    Record(a:T₁) ≤ C₁ を保存
```

これは AR §4 と pinned Typer.scala の同じ event であり、別の source example や再実行によるコピーではない。z の直前の Y.lower は空。T は新しい **型座標**であり、新しい source Value、runtime allocation、provider、receipt、binding、primitive descriptor は作らない。後の client が増やした全 bound の realization をこの空 list case へ縮小しない。

## 2. 同じ実 field の二つの projection

AR の Mκ′ を固定する。その relevant fields は次の actual events を含む。

1. 元 gκ の actual y-entry Return は iλ:I とその decorated provider rλ。
2. 元 `Record(a:Name yλ)` は、同じ iλ を field a に持つ実 a′ を作る。whole Record root r_a′ と field provider rλ を区別する。
3. recursive f の actual entry は a′ を fresh xκ′ に bind し、次の gκ′ がその same binding を capture する。
4. compatible future gκ′ invocation で Name xκ′ の designated computation が実 Return した場合、その actual value/root は同じ a′,r_a′。その field a の projection は同じ iλ,rλ である。

項4を、gκ′ が returned しただけで既に実行済みとはしない。h がその carrier をまだ Force していない場合、この Return と field projection は元の whole-carrier checking が持つ dependent obligation のまま残す。前段が Request の場合も AR の元 pending suffix を保つ。

**RZ1（field square）。** 上の該当 event の current world W で、過去の y-entry field を AR の lawful event/restriction chain に沿って運んだ projection と、Name xκ′ の returned Record の field-a projection は、同じ decorated value (iλ,rλ) を返す。

**証明。** Name yλ は actual binding を読む。Record constructor はその actual field/provider tuple を保持する。ValueBind は a′ を別の fresh key に置き、元 yλ や元 xκ を書き換えない。Lambda capture と後の Name は、その same fresh binding の projection である。この四つの実 constructor equations を順に合成すれば値と field provider の等式を得る。world の違いは AR2 の実 chain に沿う lawful restriction が担当し、過去の world/receipt を新しい world のものへ置き換えない。未実行 event では同じ proof function がその event を引数に取る。従って全 admitted finite prefixes と future events について一つの dependent square が得られる。□

この等式は source endpoint A が偶然同じという理由によらない。whole Record の provider r_a′ と scalar field provider rλ も同一視しない。

## 3. fresh coordinate の checking certificate

[SC](2026-10-24-source-indexed-constraint-derivation.md) の `Obl`/`Real` の区別を保つ。ここで作るのは SC の当該 `Extrusion fresh` obligation に対する、source-indexed annotation と local checking proof である。native の scalar inequality を complete Function membership へ変換する規則は追加しない。

Y の当該 source interpretation は、元 y-entry の I certificate と RZ1 の event action で与えられる。新しい T の解釈には、**同じ既存 I view** を receiver-side field occurrence で使う。この指定は新しい Primitive の宣言や新たな source Desc introduction ではなく、新 native coordinate を、既に構成済みの source field view に結び付ける proof annotation である。過去の Y interpretation と independently fixed targets は変更しない。

次を一つの packet Z_real に保持する。

| field | 実際に入れる証拠 |
| --- | --- |
| native event | 同じ p、Record field-a descent、target1、positive polarity、M_p の fresh miss、actual pair (T,Y) |
| whole source frame | AR2 の同じ Mκ′ と実 h-side boundary、全 provider/world/receipt/pending/future fields |
| parent field | RZ1 の transported actual y-field と元 I certificate |
| copied field | RZ1 の receiver-side actual record field と同じ I view |
| positive link Y≤T | 同じ current-world decorated valueに対する I≤I identity checking |
| selected-list obligations | actual pre-z Y.lower が空なので空 family |
| rewritten root | actual same Record tuple に対する Record(a:I)≤A の structural identity checking |
| source/native map | 元 field occurrenceから native Y、同じ receiver-side field viewから新Tへの、この event に限定した projection |

**RZ2（local whole checking）。** Z_real の各 displayed local checking obligation は、元 source checking constructors から導ける。whole AR2 frame の全原 fields と pending/future obligations は保持される。

**証明。** [SG §3.2](2026-10-08-source-generalize-definition-and-proof.md#32-checking-and-actual-elaboration-rules) の identity は同じ whole operand tuple に適用する。RZ1 により Y/T 側の current-world field tuple を同じものとして使えるため、I≤I の proof はこの rule の実 instance である。これは異なる provider/world の二 membership を marginal に組み合わせたものではない。

Record depth/width checking は同じ actual field tuple を要求する。field a の identity により Record(a:I)≤Record(a:I)=A を得る。selected-list premises は、§1 の実 list が空であるためゼロ個。未証明の unknown bound を真にしていない。

C の native value projection A へのこの checking は、h の whole inlet を単なる A と同一視しない。元 whole-carrier checking、actual receiver/admission、全 independent arms、providerとfutureは AR2/NR/GC の同じ frame に残る。新 coordinate の projectionを追加する action はこれらの tupleを変更しない。両 field checking を、その same frame の型付き field mapsに沿って入れるため、元の whole checking evidence と joint witness はそのまま使える。source graph、raw operation、型の異なる native ports は書き換えない。□

ここで得た realization は、unknown source equality を前提にする式の言い換えではない。新 T の唯一の選択 bound は空と実確認され、唯一の親 link は actual field identity で、rewritten Record も同じ field/provider の structural rule で閉じている。全 arbitrary source fields を一括して identity と呼んではいない。

## 4. native erasure、guarded references、scope action

**RZ3（exact event erasure）。** Z_real から source views/checking/frame を忘れると、§1 の実 z と、その direct link/list/rewritten comparison をそのまま得る。actual parent、fresh copy identity、target、polarity、memo invocation と processing relation は変わらない。

**証明。** packet の native event 欄は SC2 の当該 record 自体への reference である。new T の source annotation は native event を再発行せず、元 pair を他の event へ付け替えない。表示した erasure の各 field は、その同じ record の projection である。selected-bound family の長さ0も actual pre-z list と等しい。よって exact erasure を得る。□

**RZ4（同じ future family と自然性）。** 元 AR family に許される source renaming、whole substitution、actual lawful restriction に対して、Z_real の source field/checking action とその construction は可換である。native row の単射改名を併用する場合も、元 z の parent/copy/memo references を同じ改名で運ぶ。

**証明。** RZ1 は actual Name/Record/ValueBind/capture projections の合成である。元 constructor の lawful actions はこれらの projections と可換する。identity checking と same-record structural checking も同じ whole tuple に作用するので可換。T は同じ transported I view を参照し、独立の新 descriptor interpretation を各 event で選ばない。native data は actual event reference の改名だけを受ける。全 pending case では、元 dependent proof function に同じ action を適用する。□

これは freshening ごとに新しい extrusion occurrence を発生させる定理ではない。未知の captured/State/foreign action について元 AR が与えていない lawful action も追加しない。

## 5. receiving index と actual occurrence の区別

**RZ5（構成した realization 内の receiving index）。** Z_real の whole source frame における当該 boundary の receiving Value は H である。

**証明。** native p は [RD](2026-10-24-residual-demand-source-association.md) の正の residual `u∘v`。source側では AR2 が v の actual returned record→fresh binding→capture→future Name を、u の actual h-side inletへ合成する。合成の codomain は u の同じ h-side boundaryであり、source Name h は元 resolved H/providerを読む。RZ2 はその field の checking annotationだけを追加し、boundaryやcalleeを変えない。したがって source-frame projectionの receiving index はH。Functionのargument反転はvの生成内で既に行われ、外側のpositive Record descentでそれを再反転しない。□

RZ3 と RZ5 を合わせると、**実 z へ消去される genuine local checking certificate** と、その certificate 内の H-boundary を同時に構成できた。従来 SC2 が発行するだけだったこの一回の local checking obligation に、RZ1–RZ2 の actual proofを与える。

ただし、既存の native occurrence record o_z の未同定 association fieldと、この certificateの source-frame projectionは依然として異なる対象である。次の式を RZ5 の単なる言い換えとして採用しない。

```text
o_z.receiving_Value = receiving_index(source_frame(Z_real))
```

この式には、original occurrence constructionがこの source/native realizationを受け取り、その実欄へどの typed projectionを格納・保持するかという constructor correspondenceが要る。native erasureはその source-only association fieldを忘れるため、erasure一致だけから逆算できない。本稿はその未証明fieldの値をHと定義するreceiver conventionを追加しない。

この source certificate のHと定義root Fは異なるbirthなので、**certificateのindexに対する**birth-induced SCC queryは非資格である。actual occurrenceのqualificationを同じ結果として宣言するのは、上の対応式を供給した後である。任意のsource support要素を選ぶ `any` consumerへの正当化も与えない。

## 6. 親への適用と具体的な残項

この稿で供給したものは、AR の実 source event family、SCの当該native fresh record、RZ1のactualfield squareを一つに束ねた、有限の local checking realizationである。元 v/u のsource compositionがsource世界で存在するだけ、あるいはscalarmodelでY/Tに同じIntを置くだけ、という二つの独立な結果から進めて、**同じ native eventを持つ型付き source proof packet**を構成した。

残るowner対応は、どの証拠が必要か不明な状態ではない。上記のpacketをactual occurrence producer/transportの入力から取り出し、同じeventidのreceiving fieldがRZ5のprojectionに一致することを証明する。既存fieldを再定義せず、もとのsource/typeconstructionにおけるconstructorを示す必要がある。一般のselected bounds、負のextrusion、別memoのreuse、全polymorphic instancesにもこの一個のempty-selected-list realizationを自動拡張しない。

本稿の monomorphic source实例は、別稿の全 finite native Let/LetRec モデル輸送とは異なる量化である。両者を混ぜてoriginalA/B、全SCCintrusion、whole-language soundness、principality、terminationを閉じない。

## 7. Freeze / handoff

契約 [ACTUAL-COPY-HISTORY](../../tasks/agent-loop/sprints/actual-copy-history-20261024.md)、SHA-256 `741a7041254bbbb7916d0c7970abb1c8f9d7125b6a749d956c27b0a7f2a5c259`。Primary単著。Native producerのmovingartifactは未読・未依存。実装・tests・build・probesなし。直接入力は契約に固定したAR/SC/RD/NR/GC/PF/SG、occurrence/birth authority、pinnedTyper。独立査読は特にRZ1のworld/provider同一性、RZ2の本当のwholecheckingとscalarprojectionの区別、RZ3のerasure、RZ5と未証明actualassociationとの境界を検査する。
