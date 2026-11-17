# dots cycle244: 環境消失からの復旧と、実owner定義表の書換え

開始: 2026-11-17T16:30:00Z。最終公開・照合時刻は末尾に追記。
前周期公開: `852df643923f6f77474f0f76ac3e2ad7cb7b19ed`。
監督統合: 開始時`caecfb3bb1b524267527cb3ede318105ba09ee79`、復旧後・17:06確認時`a5951212c147a4c28a401a78e21a47f175abb5fe`。I47 ACTIVE継続、STOPなし。最新統合をmerge済み。I45・凍結・停止条件を保持した。

## 結果

**14新規モジュール・392定数の統合公理監査PASS。** 実PresenceのTyTerm/RowTerm/CompTerm/Atom/Modelを使い、現在のowner表から旧定義を取り出してbaseと他ownerの定義を書換える操作までを、小さな依存範囲で検証した。

大きな未完部分は変わらない。実source/inspection/cacheを持つ後継境界、全操作からのcheck成立、有限公開factとschedulerへの接続、solver停止性、最終selected-node EvidenceNodeは未証明。新しいcheckerのfalseを言語の拒否にしていない。

## 復旧と検証状態の区別

約16:35 UTCに実行環境が置き換わり、作業ディレクトリ・未公開244ソース・Lean toolchain・以前の全object cacheが消えた。単なるtransport切断ではなく、旧cloneだけがある新workspaceであることを確認した。公開済み243の成果はGitHubに全て残っており、そこから作業treeを復旧した。

- `notes/recovery/cycle244/`の**6草稿**は実tool-call本文から再構成したもの。DefinitionSupport/EvidenceSupportの2本は中断前に直接Lean検査exit0、Projection/Packet/JournalSubstの3本も直接PASSとの報告があったが、再構成bytesの同一性と独立公理監査は確認できていない。SourceTraceは直接PASS未確認。
- この6草稿はrootから**importせず、検証済み成果に数えない**。復元を再検証の代わりにはしない。ハッシュを別manifestに保存した。
- 公式Lean4.35.0を再取得した。full journal/evidence/sourceの必要依存だけでも1425本だったため、常設の大規模build禁止を守って再構築しなかった。
- 実PresenceNormalFormの小さい依存閉包36本だけは、2worker・5分上限のfocused処理で復旧成功。その上で14新モジュールを新たに検証した。全体`lake build`・`verify-lean.sh`は実行していない。
- 必要な次手は`notes/questions/2026-11-17-cycle244-build-cache-recovery.md`。監督側の通常の全体検証環境で6草稿を再build/auditするか、版とsourceに一致するcacheを利用する。proof gateの緩和は不要。

## 定理の範囲と量化子

すべて主型・B4完成の主張ではなく、健全性／完全性に向けた表現・支持・進捗の補助である。

### 1. 有限支持とreadback

- `GeneralFiniteWitnessSupport244`: 任意Name/Value、assignment、述語について、有限集合上の一致からの一様iffを表す`Supports`と、既存の一つのmodel/witnessを保存する`SupportedAt`を区別。有限連言・有限list・存在witnessの支持を生成し、有限no-read checkから保存を導く。
- `GeneralFiniteWitnessReadback244`: 各座標のreadback支持が与えられたとき、述語の支持をflatMapで合成。有限候補list全体のexists/forallは一様支持を持つ。候補listの有限性は明示前提であり、実全certificate集合の有限性を証明したものではない。任意write valuesでも、書込先が支持を読まなければ述語を保存する。

### 2. 誤った構文有限性への補助反証

`GeneralNominalRebaseSyntaxGrowth244`: 二つの固定代入`a↦join(b,b)`、`b↦join(a,a)`はそれぞれ自分のtargetを読まず、名前は2個だけ。それでも交互の構文代入n回で高さ2nとなり、任意の有限構文listから外れる項が存在する。

これは「有限ID＋owner局所Externalだけでconsumer構文が有限になる」という**補助推論だけ**の反証。この偽目標は停止した。実Yulang到達列・I47の意味変更・新stable境界の非停止を示してはいない。実EscapedStore242は他ownerの定義そのものも書換えるため、この2-cycleでは次のExternalが破れる可能性がある。診断列を実rebase無限列と呼ばない。

### 3. 実Presence定義blockの書換え

- `GeneralPresenceDefinitionRewrite244`: 任意mapping・entries・Model・assignment。保持ownerのtargetがmappingでそのままのtype変数なら、二つのtyLeからなる実原子blockの置換は、同じtargetと置換済みRHSからなるblockに**構文的に一致**。全modelでreadback iff。target列を保持する。
- `GeneralPresenceSubstitutionSupport244`: 全実TyTerm constructorとRowTermを構造帰納。arrowのincoming/outgoing rowsも含め、置換後支持は元支持からmapping支持へのflatMapに含まれる。明示rank条件からRHSの減少性、owner全targets同rankからblock Externalを導く。
- `GeneralPresenceOwnerRewrite244`: 実有限lookupによるsubstitutionを構成。target非交差から他ownerのblock形と意味を導き、Coherentは物理変換で保持。rank条件から変換後Externalも生成する。
- `GeneralPresenceCrossRead244`: **rankなし**の十分条件。removedの全RHSがretainedの全targetsを避け、retainedが元からExternalなら、変換後もExternal。`retainedCheck`のtrueからtarget非交差・External・cross-readを取り出し、block形、全model意味、変換後Externalを導く。使われないremoved entryまで検査するため必要最小条件ではない。

これらのequations構文は既存Allocation.equationsと同じ二不等式だが、高いimport層のGeneralNominalAllocation/Inline241名とのadapterはまだ再検証していない。

### 4. 反復、条件付き依存順位、診断

- `GeneralFiniteDependencyRewrite244`: 明示したNat rankがsource依存で減少し、置換で増えないなら、書換え後も減少・自己非参照と依存関係のAccを保持する。**依存関係のAccであってsolver StepのAccではない**。実reportからrankが得られることは未証明。
- `GeneralPresenceOwnerCheck244`: rank等の有限診断。trueから保持blockの形・意味・Externalを生成。Coherentやremoved block自身のExternalは別条件なので「完全なrebase準備判定」ではない。
- `GeneralPresenceOwnerSequence244`: 任意の与えられた有限block列について、全変換の意味は正しい順序の`readMany`と一致し、targetとCoherentを保持。共通rank下でExternalも保持。列の長さや実schedulerからの生成は未証明。
- `GeneralPresenceFixedInline244`: **一つの固定External block**の同時inliningは、全実型・行・原子について構文的に冪等。rowは恒等。固定lookupの構文についてなのでCoherentは不要だが、変化する定義や交互owner、全solver停止へ一般化しない。

### 5. 現在のowner表から実際に書換える操作

- `GeneralPresenceOwnerTable244`: `rebase state owner fresh`は、`state.entries owner`から旧定義を読み、base全atomsと全他owner entriesを物理置換し、ownerへfreshを置く。owner列は不変。owner membershipと各他ownerのtarget非交差の下、全結果Modelsは「fresh blockを現在assignmentで満たす」かつ「旧base＋旧他owner consumersをreadback assignmentで満たす」とiff。全owner ExternalとCoherentの保持も、明示したcross-read・fresh条件から生成する。
- `GeneralPresenceOwnerTableCheck244`: 全listed ownerを有限check。trueから上の全表Models分解と、fresh Externalを足した全表Externalを導く。具体例では旧owner2→1を使い、他owner3→2を3→1へ、baseの4≤2を4≤1へ書換える。
- `GeneralPresenceOwnerOwnership244`: 新targetsがそのownerの旧targetsに含まれ、元のlisted ownersが互いにtarget非交差なら、rebase後も全owner非交差。包含条件はchecker自体には含まれず、実stable allocatorから別途導く必要がある。

この表は定義blockを扱う部品で、inspection/cache/全journal metadataを持つSourceBoundaryではない。freshは任意入力であり、モデル非空や旧新同一public解集合のiffを証明していない。次回check成立も自動ではない。

## 検証と実行結果

Lean4.35.0。各新moduleを依存順に:
```
lean --trust=0 -DwarningAsError=true -o <focused-object-path> Yulang/<module>.lean
lean --trust=0 -DwarningAsError=true Audit/Cycle244Support.lean
```
全新module内の全定数について推移的公理を収集。許容は`propext`・`Classical.choice`・`Quot.sound`のみ、空監査は失敗。最終`final-14-audit.txt`: **392 constants in14 modules PASS**。最終追加前の13module full focused buildも全PASS、Ownershipは直接build後に14module監査へ含めた。

runtime（同toolchain、trust0/warningAsError）:
- rank診断の非循環例true、2-cycle false。
- 実型変換 `(3,var2)`→`(3,var1)`、連続変換で`(3,int)`。
- 未読先write check true、読まれる先false。
- 構文診断高さ`[0,2,4,6,8,10]`。

ソース禁止token走査・root import網羅／一意・統合rootの完全prefix保持・凍結`lean/Audit.lean`/`lean/README.md`のbyte一致を確認。既存proof moduleに変更なし。source SHA256と隔離草稿SHA256を別manifestへ保存。生dependencyログの末尾空白はそのまま保存し、source/doc diff検査とは分けた。GitHub CIの成功は主張しない。

## 独立レビュー

実型のrow支持、複数targets同rank、readManyの置換順、表の全base/他owner網羅、lookup固定性を確認。指摘されたcheckerの不足条件とfresh target非交差の別条件を明記し、最後のOwnership補助で包含前提からの非交差保持を追加した。強い十分条件を必要最小条件と呼ばない。

## 次の3点

1. 大きい依存cacheを扱える監督環境で隔離6草稿を再build/auditし、実Allocation/Inlineの名と今回の軽量Presence補助のadapterを検証する。
2. 実install・source promotion・Refresh・I45 ReobserveからCrossRead/External/owner包含を生成する。同ownerの240風promotionを先に確認し、rankやcheckを新たな言語拒否条件として課さない。
3. 全current/historical consumerとmetadataを公開単調factsへ因子化し、全他owner書換えとScheduler242のdirty処理の差を埋める。次にterminal selectedからEvidenceNode。名前・child有限だけでこの穴を飛ばさない。

詳しい残件: `cycle244-boundary-obligations.md`、`cycle244-owner-dependency-review.md`。
199/202/204/206/218/230の旧回帰を変更せず、239/240の旧反証も有効のまま。今回はそれらの大きいruntime/Lean回帰を新たに再実行していない。

## Yulang2照合

`work/dots-audit`のY2-ROLE-003/004/005とX13〜16を再読。安定後finalizeなどは履歴資料で、実center/共有/I45 point記述は現在のspecが権威。新たなYulang2実機実行はない。

## 途中公開と運用

- `29d9be39c74152eae5243cd8beb29a15ba2af73e`: 3module/156定数と隔離復旧草稿。16:45:36に全tree一致。
- `67e4434409b64f37ba9f5a27fcd5641fce8239fa`: 10module/337定数。16:58:40に全tree一致。
- 10分心拍の推定時刻16:41は誤りだったため、観測した16:40:28へ直後に訂正した。以後は観測UTCを使った。
- 使用量枠: 不明。

最終commit・全tree・終了時刻は次の公開照合欄へ追記する。

## 最終公開照合

最終成果commit: `b7cada3fac75123f15ba7136b5785754892f6d21`。
Tree: `092a37b3a94ecd952d2767e0b0a7aec860b5e6ae`。
17:12:38 UTCにGitHubから再取得し、検証済みローカルHEADとの全tree diffが空、worktree cleanを確認。前cycle最終公開から46ファイル。GitHub combined statusesは空で、CI成功とは報告しない。

17:13:29 UTCに全14source hashes不変、6草稿非import、既存proof module不変を再確認。最終Ownership補助も独立レビューPASS。未公開の検証済みLean成果はない。この記録と完了心拍を後続receiptとして公開し、その最終SHAを連絡する。完了記録作成:2026-11-17T17:13:55Z。
