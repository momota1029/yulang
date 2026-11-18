from pathlib import Path
import re
v=Path('notes/verification/cycle259');mods=v.joinpath('modules.txt').read_text().splitlines()
scopes=[
'固定I45 sourceのreport構文を有限factsへ復号する。capture名0と端点2/4だけを受理する局所decoderで、任意reportの言語的健全性は主張しない。',
'任意段階nの実packet reportを投影して得たproposalは固定factsと一致する。これを使う有限Stepは初回だけ進み、全状態Acc。ただしobserveAtは外部段階を受け取る。',
'任意初期rawモデルから同一complete assignmentを構成し、現journal・実plan Holds・次journal・有限終点モデルを同時に満たす。初期0〜4全成分と全rowを保持し内部binder型は補完する。',
'実reportのdecoderとtryWriteを接続したrunと有限Stepのiff。初回成功・以後noopとcertificateを証明するが、証明書はPropであって実行時モデル判定ではない。',
'任意二assignmentの全type成分が等しければOrigin観測が同値。rowを任意に変えられる局所補題であり全モデルの同値ではない。',
'I45 runをstage0だけで実行し、任意段階のrunと関数値等号で一致する。実行定義には増大する段階番号が不要。',
'具体239 familyの既存typeモデルへ任意row関数を付けたassignmentを構成する。rawのordinary成立はここでは明示仮定。',
'同じ239 assignmentでhead projection/merge/schemaを満たす。実ordinary条件と固定source構造を使い、任意headの一般定理ではない。',
'239の実packet Holdsをordinary条件下で構成する。raw/head/観測の証明をまとめ、未証明producerを仮定しない。',
'実239履歴について帰納的にordinary条件を解消し、任意rowを持つ同一assignmentが全段階journalと実packetを満たす。',
'任意239初期モデルの初期0〜3全成分・全rowをliteralに保存して内部typeを補完する。初期typeのEquivalentから全段階モデルを得る。',
'固定239 familyで、公開境界を保つ各段階または同一assignmentの全段階モデル存在 iff 初期rawモデル。任意sourceには一般化しない。',
'有限contextとownerとslot→atom写像を引数とするreport構文decoder。capture名0等の制約を持ち、任意Reportの正当性を認証するものではない。',
'任意239段階の実reportを初期4slotへ投影すると初回reportに一致し、実decoderのproposalが固定5factsと一致する。',
'239実reportから有限Stepを実行する。初回一度だけ進み、以後noop、全状態Acc。旧slot数や旧Stepの停止性とは別。',
'任意remaining subsetにsnapshot Models＋present factsの意味を定義する。初期/終点の正確な意味と、内部binder型補完を許す公開モデル存在同値。全subset到達は主張しない。',
'239の同一complete assignmentで現journal・実plan・次journal・有限終点を接続。旧completed roundの射影stutterを示すが、旧microstep simulationではない。',
'任意basis/state/proposalの低level writeについてpresent所属とModelsを厳密に記述。意味に加わるのはproposal∩basisだけで、basis外はwriteが無視する。',
'I45にも全subsetの明示的present-fact意味を与え、snapshotのPair制約から2≤4を導いてcompleteを構成。初期0〜4全成分と全row固定の公開存在同値。',
'proposalのbasis外を先に検査するchecked commit。成功なら全proposalがbasis内で、書込み後Models iff旧Models＋全proposal成立。errorは状態を返さず当該commitの部分書込みをしない。',
'I45/239の実decoderをchecked commitへ接続する。初回成功・以後noop。手作り不正proposalのerrorは内部診断で、到達source拒否反例ではない。',
'有限proposal列を順に検査しnoopを飛ばして最初のerror/進捗を返す。進捗後の後続proposalはそのpassでは未検査。成功は有限Step、全noopならquiescent。',
'任意observerをremaining長で整礎反復するsettle。成功時に有限Runs、長さ上界、終端・quiescence。途中成功後errorもあり得るので全履歴rollbackは主張しない。',
'全state・全proposalがbasis内という明示Closed仮定からerrorなしと有限完了を証明。一般source compilerがこの仮定を満たすことは未証明。',
'I45/239の実report observerはClosedで、settle初期=終点・終点=自身。noopを飛ばす実例も検証する。両固定family限定。',
'任意proposalのwrite可換・append・空・固定点・batch flattenをfilter代数で証明。basis外を無視する低level操作の結果である。',
'固定proposal列observerかつ全proposal⊆basisの場合に、settle結果はbatchとliteral State等号。可変observerの合流性や言語正規形の一意性ではない。',
'外側リストでproposal自体のmembershipが一致する固定batchは同結果。閉包仮定下でsettleも等しく、順序交換・重複を許す。不正proposal errorの順序独立や動的observer合流性は主張しない。'
]
s='# cycle259 宣言の日本語案内\n\n各節はmoduleの量化範囲・前提・主張。各宣言の全引数を含む正確な型は `alltypes-final.txt`、公理監査は `complete-final.txt`。定義・補助補題も列挙する。\n'
count=0
for i,(m,scope) in enumerate(zip(mods,scopes),1):
 names=re.findall(r'^\s*(?:noncomputable\s+)?(?:theorem|def|abbrev)\s+(\w+)',Path('lean/Yulang/'+m+'.lean').read_text(),re.M);count+=len(names)
 s+=f'\n## {i}. {m}\n\n{scope}\n\n'+', '.join('`'+n+'`' for n in names)+'\n'
assert len(mods)==len(scopes)==28 and count==185
v.joinpath('declaration-guide.md').write_text(s+v.joinpath('probe-guide.md').read_text())
