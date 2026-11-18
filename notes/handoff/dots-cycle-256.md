# cycle256 — source 集約の支持と保持済み定義の公開モデル射影

開始: 2026-11-18 12:28:39 UTC。最終公開・照合の時刻は [receipt](../verification/cycle256/publication-receipt.md) に記録する。50分まで研究・検証を続け、55分以内に報告する周。

integration/m1-final `33cf8d490b2e8f09c1f061e3bba7535baa6cdf49` の standing orders/inbox を再読。I-50 が最新、ACTIVE、上限なし。終了前の再取得でも不変。前255の公開と作業停止を確認して開始し、競合 writer は認めなかった。凍結した旧 Lean・spec・plan は変更せず、barrel は追加のみ。公開先は work/dots-main のみ。

## 成果

新規15モジュール、明示101宣言。全宣言の条件・結論は [宣言案内](../verification/cycle256/declaration-guide.md) と [Lean の全型出力](../verification/cycle256/all-types.txt)、設計は [主ノート](../design/2026-11-18-cycle256-aggregate-polarity.md) を参照。

1. 実 Frame から input occurrences の非空性を導き、lo/hi の支持を実 old endpoint ごとの極性別支持と同値にした。初期状態については同一 source basis に対する prepare 成功を、欲しい支持を仮定せず導出した。一般の歴史 snapshot は EndpointSupported/prepare 成功が必要で、失敗は言語の Rejected ではない。
2. 実際に source 到達する I45 の全 n family で、保持された lower 方程式の部分列を replay history として取り出し、固定2原子 pool で集約を一定化した。元 capture の Fits との比較は任意の Models(state n) に対して成立する。history は全 snapshot の同一視ではない。
3. 同 family の全 slot 型は初期5変数のいずれかへ正規化できる。expanded View と compact View の全割当でのモデル同値、および初期0〜4の完全な型成分を固定する raw の存在モデル射影同値を証明した。slot 数は依然 n+5、旧 Step の no-Acc は残る。
4. 任意 raw/ordered entries について、実際に raw.ordinary に含まれる定義 block の除去が公開モデル射影を保存する一般橋を証明した。全 target が hidden に入ることが必要。PublicAgree は非 hidden の完全な型成分と hidden を含む全 row を固定する。逆方向では private 型を solve で変更してよい。同一割当の復元には block 成立が必要。SafeOrder を要しないのは保持済み式の除去だからで、新しい循環 block の可解性や更新の正当性ではない。
5. 実 slot.row の private 名残存と、現 View.Models が読まないその metadata の除去を区別した。active row・nominal row parameter は除去していない。Known、RootPending、PointDescriptor、K2、cache、将来 Step の保存はこのモデル同値からは出ない。

数学15本は commit `f93a952a9c7bb8046d387e905c3c19ef42feb874` ですべて公開し、その後は数学ソース不変。後続 commit は Usage 追加と検証・設計・報告。

## 検証

- `bash notes/verification/cycle256/final-build.sh`: exit 0。15本を新しい focused cache へ `lean --trust=0 -DwarningAsError=true` で再ビルド。
- 明示101宣言と private/generated を含む152宣言を監査。依存公理は propext/Classical.choice/Quot.sound のみ。禁止語なし。
- Usage 22例を検証。実 source family と汎用の循環・反復target block例を含む。後者を source 到達反例とは呼ばない。終了直前の再実行も exit 0。
- 別 cache で実依存閉包内の104モジュールを再ビルド、exit 0。うち現周14本＋以前90本。後から加えた15本目は最終 focused build で検証。全リポジトリ再ビルドではない。
- source hash 閉包1593ファイル、import 構文2719行。255の1549、254の1429旧依存ソース不変。選択した15根から101宣言中88へ到達し、残る13の理由は [reach review](../verification/cycle256/reach-review.md)。全 Main/Audit の接続完成を意味しない。
- 全15本について独立読取レビュー済み、主張範囲の混同なし。独立担当の再ビルドは未実施。レビューは verification/cycle256/review-{first,second,third,last}.md。
- 全体 lake build、verify-lean.sh、Yulang2 runtime は指示に従い未実行。[spec/runtime 照合](../verification/cycle256/spec-runtime-check.md) と [自己点検](../verification/cycle256/self-review.md) に範囲を記録。audit branch は55574b6で不変。

## 未完と次の順序

[次の有限 fact 境界](../design/2026-11-18-cycle256-next-fact-boundary.md) に依存関係と回帰表を記録した。

1. PolaritySourceClosure: 全 source 到達・実 old/current 環境で極性別支持を導く。今回の lower history と5 slot値は全 field/basis 閉包ではない。異なる lower atom の後の upper read は次の検査候補で、到達反例は未確立。
2. UsedConsumerAndInspectionPreservation: active row、binder/capture/target、inspection、証明書、child/output identity を保存する。公開名2と4を意味同値だけで同一化して不変区間を点にする近道は採らない。
3. CanonicalStrictProgress: source 由来の固定有限 fact 集合を証明してから、真に新しい fact または細分化による減少と Acc を示す。rank が減ることを Step の定義に加えただけでは完成としない。

I-50 の無条件出力 producer/循環拒否、全 trace 閉包・private 非流出、後継 Step の停止性、mixed-time packet compiler、Permitted、12性質/回帰、EvidenceNode は未完。新しい完成後継の source 到達失敗や意味変更の必要性は確立しておらず、質問ノート追加なし。利用量の数値は取得できず不明。
