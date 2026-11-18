# Cycle252: I49の有限性不変条件をsource規則に接続する設計

開始08:30:13UTC。integration48627b59eのI49が明示的再開指示。
言語意味は変更しない。source到達反例が得られた時点で実装を止める。

## 1. owner集合

spec6.3のPaterson条件は正規化後の名前なし入力に課され、出力専用変数は入力へ
戻せない。K2が適用された有限の入力木で、同一のsource意味における子のmassが
厳密に小さいことを使う。単に「型集合が有限だからidentity集合も有限」は不可:
Occurrence.identityはNatでdemandと独立、実allocatorは親・宣言・子位置のtuple
から新IDを作る。有限分岐の生成pathを、真の入力mass以下の長さで列挙し、その
有限pathから実identityを写像する方法が必要。再見直し時のsnapshot差をまたぐ
mass保存/減少は未証明であり、旧240反復を有限pathと仮定してはいけない。

## 2. 公開basisと平坦な集約正規形

入力は固定有限poolのTyTerm原子。各原子のtypedReadsはpublicNames内とする。
下界はunionを再帰的にflatten、上界はintersectionを再帰的にflattenし、poolの
順で集合所属を選択したlistを正準代表とする。同じ演算の入れ子と重複は消える。
別の演算やnominal内部は一つの原子であり、一般の混合lattice正規形ではない。

予定定理（任意pool/term/assignmentについて）:
- flattenされた全原子がpool内なら、foldした正規形は元termと意味同値。
- poolが同演算でflatなら、再正規化は文字通り同じ正規形になる。
- 正規形候補はpoolの部分listの有限列挙に含まれる。
- 全pool原子がprivate名を読まなければ正規形も読まない。
- SnapshotGrowth251のduplication反復はこの正規化で同じ代表になる。
これは表現側の本物の不変条件で、sourceがこのpool内で閉じることは別。
既存242は有限Interval poolでcanonicalを行うが、任意snapshot TyTermをflatten
しない。251のroot一段簡約は一般に冪等でないため代用しない。

## 3. 深さ

I49のD=max(source,decl)は注意が必要。specはassociated RHSをhead変数と型構築子
から作ることを許す。templateへの代入ではdepth(template)+depth(capture)まで
増え得る。whereの小ささはoutput RHSには課されない。実source到達例を調査し、
反例が閉じればそこで止める。仮に修正が必要でも、勝手にDを大きくして証明済み
扱いにはしない。旧SourceFactorizationにはより大きいreplacementBoundがあるが、
実source Producerが未構成なので引用するだけで穴を埋めない。

## 4. private escape

public binder/output/childをreadbackする際、定義解決済みpublic原子へ置換する。
現在のframeに対するfreshnessだけで将来のsource名との分離を言わない。
全source生成器によるpublic basis closureと、owner keyがprivate syntax版を含ま
ないことを同時に維持する必要がある。正規形のno-private-readsはその局所部品。

## 5. 測度とstepの厳密さ

owner未install数と各ownerの有限interval fact残数の辞書式を候補とする。
有限性と単調性だけでは厳密降下にならない。同じ意味の再見直しを許せば
stuttering loopが残る。各source Stepが「未install owner追加」または「未成立の
有限factを成立」に当たることを実規則から証明する。I45 point固定だけで
nonpointの同値な見直しを除外したとは言わない。239/240の回帰移植はこの箇所。

## ゲート

現時点で全1〜5の見通し完成ではない。今回のLean対象は2の表現不変条件と、
実sourceの反例候補を確認するための最小診断に限る。source到達反例が得られれば
閉じた証明・報告を保全して止める。packet/Permitted/EvidenceNode部品は増やさない。
