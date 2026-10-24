# 文字列補間から完全 Call・選択・record の導出を作る

Revision SI1。著者 `/root`、独立査読前。任意の有限な structured string parts について、未構成の「安全な補間器」を仮定せずに展開と型導出を構成する。型付き子式、選択証拠、標準宣言の型という個々の入力は明示する。全 resolver・推論器・parser の正しさとは区別する。

## 1. 固定した根拠

Oracle Git object は `a58eefc31e22141574b6f20c6a5748151c6d79f1`。read-only の `git show` で次を確認した。

| Path in object | SHA-256 |
| --- | --- |
| `crates/infer/src/lowering/string_lit.rs` | `d5d1bb1381687950d3f0e3cf1184d9e45ac3748d5f0f173b1d17266f0decbf66` |
| `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `crates/infer/src/lowering/record_lit.rs` | `88ce8e06f83884fd825402565c52ab1f19e8b9932500036eae495d392a5c990c` |
| `lib/std/core/fmt.yu` | `bb36229d7d75008a5ae4fef6c162bbf4bd7dd7ab186cd331fd689daaa71cf212` |
| `lib/std/text/str.yu` | `3ba0fb8e37c7dbfc6ff118611530632d02a9017c8433c10fbcfa2ad4f0c2513b` |

型導出は [S](../../docs/yulang-source-type-safety-ja.tex)、選択の有限証拠からの構成は [D](../../docs/yulang-dot-selection-safety-ja.tex) §通常・参照・effect member、role member、field fallback を使う。S/D の固定 hash は [sprint 契約](../../tasks/agent-loop/sprints/source-substitution-surface-20261024.md)にある。D の larger manuscript 全体が独立査読済みとは扱わず、以下に使う局所構成を明記する。

## 2. 全 structured part と展開

`App(f,e)` は、callee を評価し e を carrier として完全 Call へ渡す S の App である。二引数 `f a b` は左結合の二つの App。compile time に構文木を作る順序を、runtime の e の先行評価と混同しない。

入力 part は `Text(s)` または `Interp(e,sp)`。sp は kind∈{display,debug,lower_hex,upper_hex}、align、sign、fill、width、precision、alternate、zero_pad の有限 record。`layout(sp)` は kind 以外の option が一つでも Some、または最後の二 bool が true であること。kind だけが debug/hex でも layout は false である。

| kind | member | layout formatter | role |
| --- | --- | --- | --- |
| display | show | format_display | Display |
| debug | debug | format_debug | Debug |
| lower_hex | lower_hex | format_lower_hex | LowerHex |
| upper_hex | upper_hex | format_upper_hex | UpperHex |

`Opt_A(None)=nil[A]`、`Opt_A(Some(v))=App(just[A],v)` とする。variant/constructor は解決済みの同じ nominal identity と instance を使う。

```text
Spec(sp) = App(format_spec,
  { kind = kind_variant(sp.kind),
    align = Opt_Align(sp.align), sign = Opt_Sign(sp.sign),
    fill = Opt_Str(sp.fill), width = Opt_Int(sp.width),
    precision = Opt_Int(sp.precision),
    alternate = sp.alternate, zero_pad = sp.zero_pad })

Part(Text(s)) = literal(s)
Part(Interp(e,sp)) = Select(e,member(sp.kind))              if ¬layout(sp)
Part(Interp(e,sp)) = App(App(formatter(sp.kind),Spec(sp)),e) if layout(sp)
Join(l,r) = App(App(std::text::str::concat,l),r)
```

parts 全体の `String(parts)` は、空なら literal empty string、一要素ならその Part、二要素以上なら Part 列の **left fold** Join である。最初に empty を付ける fold ではない。これにより空・単独補間・複数補間を全て覆う。

## 3. 型導出を組み立てる

**補題 SI1（書式 record）。** standard enum/option/struct の有限宣言から `Spec(sp):FormatSpec` の値型導出を構成できる。

**証明。** kind/align/sign の各列挙子は対応する nominal constructor から型付く。fill は Str、width/precision は Int、二つの flag は Bool の literal 規則。None は同じ A の nil、Some は just:A→Opt A とその payload への App で Opt A を得る。八つの名前は全て異なり required なので、同じ field 列から structural record 導出を作り、生成 struct constructor の型付き input boundary と App を適用する。nominal を透明な record と同一視しない。全て有限個の規則適用である。whole profile/効果は各宣言の元の型付けに残す。□

**補題 SI2（選択の局所構成）。** 子導出 `e:A`、選択済み identity・一つの whole scheme instance・有限の ordinary/role evidence・各直接境界を与えると、`Select(e,m):B` の計画と型導出を有限に作れる。特に B=Str の証拠がある場合に文字列 part となる。

**証明。** ordinary/reference/effect member は、解決済み f:C(A_m,B_m) と直接証拠 a:A⇒A_m、r:B_m⇒B に対し `let f←Get in Call(Wrap(f,a,r),Delay El(e))` を構成する。Delay は UA、Wrap は C(A,B)、Call は B。Get は lookup と同じ instance の型/evidence application である。role member は同じ role occurrence の dictionary から required member field を取り、その member-local 型/evidence を適用して同じ構成へ入る。field fallback は `let x←El(e) in let y←El(b,x) in field_m(y)`、b:A⇒{m:B} から B を得る。直接境界の効果も通常 bind/call の計算である。これらは D の三場合の構成そのものであり、選択を発見する算法の完全性を使わない。□

layout branch の入力は、当該 kind の role evidence `q:Role_k(A)` と、同じ A で instantiate した標準 formatter の全 scheme である。その値型射影は `FormatSpec→A→Str`。部分適用で q を別の A に再選択しない。

この signature は任意の外部「安全な補間器」の公理ではない。固定 `fmt.yu` の四 body からも次の有限な導出を作る。`repeat:Str→Int→Str` を再帰環境へ登録し、比較/減算/concat と同じ再帰参照で body:Str を導く。format_fill は option case の全枝が Str。format_body は precision case と string length/range の全枝が Str。starts_with_minus は length、range、string equality から Bool。format_sign_prefix は sign case と concat から Str。format_with_padding は width/align case、Int の減算・比較・除算、先行 helper と concat から Str。再帰 helper を inline しないので導出は有限である。最後に四 formatter は q の show/debug/hex field が返す Str と固定 head literal を同じ helper へ渡す。ordinary operator/member 選択の identity は固定標準宣言の対応する primitive/helper であり、その証拠を構成に保持する。各 signature への直接境界も同じ endpoint で導出する。計算停止や pure 性はここで要求しない。

**定理 SI3（全 part 列からの値型導出）。** 各補間子式の型導出と、非 layout の Str 結果選択証拠、layout の上記 role evidence があれば、任意の有限 parts に対して `String(parts):Str` の導出を構成できる。

**証明。** Text は literal、非 layout は SI2、layout は SI1 と同じ instance の formatter への二回の App。concat は固定 `str.yu` の StringConcat wrapper で Str→Str→Str、primitive の値型は V3 から得る。空列・一要素・left fold の各 step へ列長の帰納を適用する。完成した文字列全体の型導出を前提にせず、子・選択・宣言の各有限導出から作った。□

## 4. 評価順と全効果の接続

**補題 SI4（完全 Call の位置）。** 上記展開は callee の計算、carrier の受領、argument force、formatter/選択 adapter の計算、結果 adapter の計算を S の App/Select の位置に保つ。生成を理由にユーザー補間式や選択 body の effect を消さない。

**証明。** 非 layout は SI2 の三式をそのまま使い、member の receiver を Call より前に eager な let へ移さない。field fallback のみは定義どおり e と boundary を順に評価する。layout は外側 App の callee が `App(formatter,Spec)` なので、この第一 Call の result を得た後で第二 Call が e の carrier を受領する。Spec の record 子は S の record 順に接続する。Join もまず `App(concat,l)` を評価し、その結果への第二 Call が r を扱う。left fold の l 自体は前部分の構文全体であり、part を compile time の loop で作ったからといって先に評価済みとはしない。全て元の完全 Call の局所規則の適用である。□

固定した concat は Value entry の strict primitive wrapper なので、通常の再開のない実行経路では左部分の string を得てから右部分を要求する。一般の selected member が computation entry なら、その body が carrier を force する回数に従う。補間子式が無条件に一度だけ評価されるという別の性質は SI4 の結論ではない。continuation の繰返し再開による suffix の再実行も許す。

**定理 SI5（核の健全性への適用）。** SI3 の各構成を whole packet とともに G1 に渡すと、補間全体の有限 Gen graph を構成できる。各 mandatory inclusion を満たす証明書と定理 C の他の実際の前提の下で、文字列補間も値・効果・型付き再開の定理 C を満たす。

**証明。** SI3 の有限構成は literal、record、case、rec、App、Select、直接証拠と宣言参照だけを使う。各場合は G1 の既存生成規則である。formatter helper は有限 body label と再帰 backedge で登録する。SI4 が各 body/adapter の実行位置を与え、G2/G3 が request・failure・resume を含む全 edge を被覆する。I が有限 interface、V が値型を与えるので、定理 C の実際の前提を満たせばその prefix 帰納を適用できる。型付き formatting member の効果を無条件に空とする step はない。□

## 5. 凍結 lowering への限定した構造対応

**定理 SI6。** 有限 CST に対して固定 string-literal 前処理が成功し、child lowering と全 standard lookup/selection identity が同じものを返すなら、生成された source Expr の構造は §2 の String(parts) に一致する。fresh binder/内部 identifier の整合した改名を除く。

**証明。** `string_lit_parts` は未走査要素を減らし Text を連結するか Interp を一つ追加する。format parser は有限文字列上で align、sign、alternate、zero_pad、width、precision、kind をこの順で消費する。decimal loop は各 step で index を増やす。overflow/欠落 precision/余分な suffix は既定の診断となる。escape decoder も有限 token を消費する。成功時に同じ structured parts を返す。

`lower_string_lit_parts` の acc は最初 None、最初の part だけはそのまま、二つ目以後だけ concat を二回 App する。空列は empty literal。各 `lower_string_interp_part` の has_layout 分岐は §2 と一致する。`format_spec_value` は同じ八 field を同順に作り、一つの constructor App を作る。Some/None、kind/member/function 名も表の全場合に対応する。plain path は同じ token decoding を literal にする。以上を有限 parts の長さへ帰納する。□

SI6 は型推論の対応を主張しない。特に **単独の非 layout 補間**では固定 lowering は selection をそのまま返す。`lower_synthetic_selection_at_with_origin` は新しい result variable を作り、この箇所自身は結果を Str に固定しない。そのため「文字列の構文だから、成功した全 selection は Str」という証明はできない。SI3 は必要な Str 結果の局所証拠を明示している。実 source の名前解決・選択・全体制約がそれを供給するかは別の compiler/source bridge であり、ここでは実行による反例を報告していない。仕様を変えてこの隙間を消すこともしない。

## 6. 親義務への適用

全表層被覆のうち、文字列補間の全 structured parts、書式 record、四 kind、空/単独/複数の展開と型導出構成を得た。任意の補間 body の完全 Call と効果を保持する。残るものは parser の全入力との意味対応、standard module/name resolution、全 selection/role evidence の発見と conformance、上記単独補間の native 結果制約の対応、および他の表層 family である。

Yumark の commands/inline expressions はこの文字列補間と同じ構文ではない。固定 Yumark lowering はそれらを未対応と明記するため、本稿から全 Yumark の意味を補って採用しない。元の全体目標には残す。

紙上導出と immutable Git object の読取りのみ。tests/build/実装変更/実行例なし。依存と本稿を凍結して独立査読へ渡す。
